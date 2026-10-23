#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
"""Verify the model, then require well-typed mutants to fail verification."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PINS = json.loads((HERE / "pins.json").read_text())


def replace_once(source, before, after):
    if source.count(before) != 1:
        raise RuntimeError("Mutation anchor missing or ambiguous: " + before)
    return source.replace(before, after, 1)


MUTATIONS = {
    "omit_rollback": (
        "rollback(heap, u); // mutation: rollback",
        "let _ = u; // intentionally omit rollback",
    ),
    "fifo_unwind": (
        "let task = stack.pop().unwrap();",
        "let task = stack.remove(0); // intentionally unwind oldest first",
    ),
    "reverse_children": (
        "stack.push(Task::Unify(x2, y2)); // mutation: right push\n"
        "    stack.push(Task::Unify(x1, y1)); // mutation: left push",
        "stack.push(Task::Unify(x1, y1)); // intentionally reversed\n"
        "    stack.push(Task::Unify(x2, y2));",
    ),
    "premature_finish": (
        "stack.push(Task::FinishUnion(u)); // mutation: finish push\n"
        "    stack.push(Task::Bind(u.new_root, new_bound)); // mutation: bind push",
        "stack.push(Task::Bind(u.new_root, new_bound));\n"
        "    stack.push(Task::FinishUnion(u)); // intentionally completes before binding",
    ),
    "wrong_saved_child": (
        "Some(Pending { child, old_root, new_root })",
        "Some(Pending { child: y, old_root, new_root }) // intentionally ignores rank swap",
    ),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verus", default=os.environ.get("VERUS", shutil.which("verus")))
    parser.add_argument("--out", type=Path, help="New directory for logs and mutant copies")
    args = parser.parse_args()
    if not args.verus:
        parser.error("Pass --verus /path/to/the/pinned/verus (see README.md)")
    verus = str(Path(args.verus).resolve())
    out = args.out.resolve() if args.out else Path(tempfile.mkdtemp(prefix="simplicity-verus-"))
    if args.out:
        out.mkdir(parents=True, exist_ok=False)
    print("Evidence: " + str(out), flush=True)

    # This is a source-drift tripwire, not a proof of source/model equivalence.
    for filename, expected in PINS["source_sha256"].items():
        actual = hashlib.sha256((ROOT / filename).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(filename + " changed: review the model correspondence before updating pins")

    version_run = subprocess.run([verus, "--version", "--output-json"],
                                 capture_output=True, text=True, check=True, timeout=30)
    version = json.loads(version_run.stdout)["verus"]
    if (version["version"] != PINS["verus_version"]
            or version["commit"] != PINS["verus_commit"]):
        raise RuntimeError("Verifier version differs from pins.json")
    (out / "version.json").write_text(version_run.stdout)

    source = (HERE / "model.rs").read_text()
    results = {
        "verus": version,
        "model_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "source_sha256": PINS["source_sha256"],
        "checks": [],
    }

    def invoke(name, file, *, verify):
        args = [verus, str(file), "--no-cheating", "--output-json", "--compile",
                "-o", str(out / (name + ".bin"))]
        if not verify:
            args.append("--no-verify")
        proc = subprocess.run(args, cwd=out, capture_output=True, text=True, timeout=120)
        (out / (name + ".stdout.json")).write_text(proc.stdout)
        (out / (name + ".stderr.log")).write_text(proc.stderr)
        if not verify:
            if proc.returncode != 0:
                raise RuntimeError(name + " failed Rust/frontend validation:\n" + proc.stderr)
            return {"name": name, "compiled": True}
        try:
            verification = json.loads(proc.stdout)["verification-results"]
        except (ValueError, KeyError):
            raise RuntimeError(name + " did not produce verification results:\n" + proc.stderr)
        if verification["encountered-vir-error"] or not verification["is-verifying-entire-crate"]:
            raise RuntimeError(name + " did not verify the whole model")
        if re.search(r"resource limit|timed? out|internal compiler error", proc.stderr, re.I):
            raise RuntimeError(name + " encountered an inconclusive verifier failure:\n" + proc.stderr)
        return {"name": name, "exit": proc.returncode, **verification}

    baseline = out / "baseline.rs"
    baseline.write_text(source)
    result = invoke("baseline", baseline, verify=True)
    if result["exit"] != 0 or not result["success"] or result["errors"] != 0 or result["verified"] == 0:
        raise RuntimeError("Baseline proof failed; see " + str(out / "baseline.stderr.log"))
    subprocess.run([str(out / "baseline.bin")], check=True, timeout=10)
    results["checks"].append(result)
    print("PASS baseline: " + str(result["verified"]) + " verified, 0 errors; executable ran", flush=True)

    for name, (before, after) in MUTATIONS.items():
        mutant = out / (name + ".rs")
        mutant.write_text(replace_once(source, before, after))
        results["checks"].append(invoke(name + "_compile", mutant, verify=False))
        result = invoke(name, mutant, verify=True)
        if result["exit"] == 0 or result["success"] or result["errors"] <= 0:
            raise RuntimeError("Mutation survived verification: " + name)
        diagnostics = (out / (name + ".stderr.log")).read_text()
        if not re.search(r"assertion failed|postcondition not satisfied|invariant not satisfied", diagnostics):
            raise RuntimeError(name + " failed without the expected proof diagnostic")
        results["checks"].append(result)
        print("PASS negative control " + name + ": compiled, proof rejected ("
              + str(result["errors"]) + " failing checks)", flush=True)

    results["success"] = True
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print("All proof and mutation checks passed.", flush=True)


if __name__ == "__main__":
    main()

# Verus experiment: inference continuations and rollback

This standalone experiment models the continuation and undo mechanics introduced
by commit `ea065b8` (`types: make binding and unification iterative`). It starts
from `b93345f`, whose subsequent optimization leaves those mechanics unchanged.
It neither changes nor links into the production library.

**Result:** the model verifies with Verus `0.2026.10.18.7d82994` and
`--no-cheating`. Five deliberately broken variants compile as Rust and fail
verification. This establishes properties of the model below, not a formal
verification of the complete production inference implementation.

## Run it

Install the pinned verifier from the
[official release](https://github.com/verus-lang/verus/releases/tag/release/0.2026.10.18.7d82994),
following Verus's [installation instructions](https://github.com/verus-lang/verus/blob/release/0.2026.10.18.7d82994/INSTALL.md).
Version, commit, and the tested macOS ARM archive checksum are in `pins.json`.
The experiment used Rust `1.99.1-aarch64-apple-darwin` and the release's bundled
Z3. No verifier binaries or toolchain dependencies are added to this repository.

From the repository root:

```sh
python3 verification/inference/check.py --verus /absolute/path/to/verus
```

Python 3.9+ and the pinned Verus executable are required. The runner creates a
temporary evidence directory and prints its path. An explicit `--out PATH`
selects a **new** directory. `VERUS=/absolute/path/to/verus` is also supported.
The runner needs no network access once Verus and its required Rust toolchain
are installed.

The runner:

1. Checks the production-source hashes and verifier version against `pins.json`.
2. Verifies the entire model with `--no-cheating`, compiles it, and executes its
   three concrete scenarios.
3. Copies the model into separate temporary files and applies one mutation to
   each, leaving the original file and its specifications unchanged.
4. Compiles each mutant with verification disabled to exclude syntax, typing,
   and unsupported-feature failures. These binaries are **not executed**.
5. Runs full verification on each mutant with `--no-cheating`, requiring an
   actual proof failure. Timeouts, resource exhaustion, verifier/frontend errors,
   and partial-crate verification are rejected as inconclusive.

Raw verifier JSON, diagnostics, binaries, mutant source, and `results.json` stay
in that evidence directory. The checked-in `results.json` records the completed
run, including the exact model hash. Executing the baseline is a compilation
smoke check; its proof assertions are erased, not runtime assertions.

## Model and proof obligations

`Heap.data` represents union-bound elements, either `Root(bound_id)` or
`EqualTo(parent_id)`. Its separate `ranks` and `bounds` vectors let the proof
distinguish restoring a root handle from restoring the entire context. Bound
payloads are opaque integers; type constructors and TMRs are not interpreted.
Repeated element/handle IDs retain sharing. No tree-shaped-heap or disjoint-undo
assumption is imposed on the unwind theorem.

`Task` mirrors `Bind`, `Unify`, `Finalize`, and `FinishUnion`. The specification
`execution_order` reads the work stack in next-to-execute order. `active_calls`
projects only the unfinished union frames, oldest first. `recursive_error`
specifies the previous algorithm's error returns: restore the innermost
unfinished union, then propagate the error to its caller.

The verified executable operations have these contracts:

| Operation | Verified property |
| --- | --- |
| `merge_roots` | Selects the parent by rank, increments equal ranks, handles identical representatives, and saves the selected child's old root even when argument order is swapped. |
| `rollback` | Restores exactly the saved child's root handle; all other data slots, ranks, and bound payloads are unchanged. |
| `merge_then_reject` | An immediately rejected merge restores the original data vector, while retaining its rank increment. |
| `schedule_compound` | Executes left unification, then right unification, then parent finalization, before the older continuation. |
| `schedule_complete` | Executes left binding before right binding, before the older continuation. |
| `schedule_union` | Binding precedes completion; the undo record remains in the active-call projection until completion. |
| `finish_union` | Removes exactly the completed top union's marker without modifying the heap. |
| `unwind` | For every finite valid pending stack, the actual pop/filter/restore loop yields exactly `recursive_error`, then leaves the stack empty. |
| `unwind_outer` | Restores the outermost union only after all nested pending unions have been unwound. |

The loop's central invariant is:

```text
recursive_error(current_heap, active_calls(remaining_stack))
    == recursive_error(initial_heap, active_calls(initial_stack))
```

Each pop either removes ordinary unexecuted work or performs one restoration
and removes that active frame. The invariant establishes equality of the whole
modeled result, rather than just an error flag. `stack.len()` strictly decreases
during unwinding, including when an ordinary queued task is discarded.

Separate inductive lemmas prove that unwinding preserves ranks, bound payloads,
and any data slot not targeted by a pending undo record. Completed calls no
longer contribute an undo record; their work is retained except where a still
pending record restores the same slot. This matches the original restoration
operation. It does not assert that an error restores the entire pre-operation
state or that every completed merge survives all possible aliasing patterns.

Three executable, verified examples check that the contracts compose and their
preconditions can actually be met:

- `nested_partial_failure`: merges an outer pair, completes the left sibling
  and changes a bound payload, then fails the right sibling. The left union and
  payload survive; the right and outer roots are restored; rank increments stay.
- `rank_swapped_failure`: the second argument wins on rank, and rollback still
  restores the correct child.
- `aliased_undo_targets`: two saved records target the same slot. The inner one
  is restored first, making the outer saved root the final value. This synthetic
  control is stronger than requiring distinct pending targets; it is not a claim
  that every such stack is reachable from production inference.

## Negative controls

All five controls compiled and then failed verification in the recorded run:

| Mutation | Failure that must be detected |
| --- | --- |
| Omit the rollback call during unwind | Recursive-error loop invariant is not preserved. |
| Unwind from the front of the work vector (FIFO) | Recursive-error loop invariant is not preserved. |
| Reverse the left/right child pushes | Left-before-right execution-order contract fails. |
| Put `FinishUnion` ahead of its binding | Binding-before-completion execution-order contract fails. |
| Save the second argument as the child despite a rank swap | Saved-child contract fails. |

These are mutations of executable model code, not changes to the reference
specification, preconditions, or proof expectations. Their rejection checks that
the verified contracts are sensitive to these particular regressions. It does
not establish that the specification catches every possible bug.

## Correspondence to commit two

| Production code | Model counterpart | Remaining manual connection |
| --- | --- | --- |
| `union_bound.rs`: `UbData` / `PendingUnion` | `Data` / `Pending` | Node IDs and bound IDs stand in for `Arc<GhostCell<...>>` and `BoundRef`; memory ownership is abstracted. |
| `UbElement::unify`, after `root_element` | `merge_roots` | Root finding is a precondition; its path-halving implementation is not verified here. |
| `PendingUnion::rollback` | `rollback` | A checked vector write stands in for mutation through the ghost token. |
| `context.rs`: compound and complete/incomplete `bind_step` arms | `schedule_compound` / `schedule_complete` | Which arm is selected and the correctness of binding itself are outside the model. |
| Nested `BindTask::Unify` arm | `merge_roots` + `schedule_union` | The model uses opaque bound IDs instead of cloning actual bounds. |
| `BindTask::FinishUnion` arm | `finish_union` | Production pops the task before matching; the helper includes that pop. Both consume the undo record without restoring it. |
| `bind` error loop | `unwind` | Pop, filter, restore, and discard ordering are modeled directly. |
| Top-level `unify` error handling | `unwind_outer` | The top-level saved union is outside the work vector, as in production. |

The hashes in `pins.json` detect production-source drift and force this mapping
to be reviewed before rerunning on changed sources. **A matching hash does not
prove the mapping.** There is no automatic extraction or refinement proof from
the production Rust functions to this model. In particular, the scheduling
contracts compose for arbitrary older continuations, but this experiment does
not verify every transition of the complete inference loop or prove that every
reachable production state satisfies the model's preconditions.

Path compression is relevant to the boundary: rollback preserves every modeled
slot except its saved child, so earlier path-compression writes to other slots
remain. This does not prove that path compression plus rollback preserves all
union-find invariants; the theorem is equivalence to the original restoration
operation, whose behavior also retains those writes.

## Trusted boundary and excluded claims

The model contains no `assume`, `admit`, `external_body`, or user-defined
`assume_specification`. `--no-cheating` enforces that restriction. Assertions in
unreachable match arms must themselves verify; they are not assumptions.
Verus, its solver, Rust compilation, and the specifications supplied by `vstd`
remain trusted. The manual source/model correspondence remains unproved.

This experiment does **not** verify custom `Drop`, `Arc` reference counting,
`GhostCell` memory safety, concurrency/locking, root finding, complete type
inference, exact errors/TMRs, or compiled stack-byte limits. It does not establish
absence of allocation failure or panics outside the modeled preconditions.
The loop termination measure applies to error unwinding, not all inference.
The prior Rust regressions, differential comparisons, and Fedimint checks remain
the evidence for integration behavior. No claim about Liquid network impact is
made.

The useful next extension would be a refinement proof for the complete binding
state machine, or adapting the actual executable core to Verus so that fewer
steps depend on the manual correspondence above.

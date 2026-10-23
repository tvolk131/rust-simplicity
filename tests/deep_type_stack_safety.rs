// SPDX-License-Identifier: CC0-1.0

//! Exercise deep types on a small stack. Each test runs in its own subprocess
//! because a stack overflow aborts the process rather than unwinding the thread.

use std::process::Command;
use std::sync::Arc;
use std::thread;

use simplicity::node::CoreConstructible;
use simplicity::types::{Context, Final, Type};
use simplicity::{BitIter, ConstructNode};

const DEPTH: usize = 10_000;

fn on_small_stack(name: &str, test: impl FnOnce() + Send + 'static) {
    const CHILD_TEST: &str = "SIMPLICITY_STACK_SAFETY_TEST";
    if std::env::var(CHILD_TEST).as_deref() == Ok(name) {
        thread::Builder::new()
            .name(name.to_owned())
            .stack_size(1024 * 1024)
            .spawn(test)
            .unwrap()
            .join()
            .unwrap();
    } else {
        let output = Command::new(std::env::current_exe().unwrap())
            .env(CHILD_TEST, name)
            .args(["--exact", name, "--nocapture"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name}: {}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }
}

fn drop_nested_type(is_sum: bool, nest_left: bool) {
    let mut ty = Final::unit();
    let leaf = Arc::downgrade(&ty);
    for _ in 0..DEPTH {
        let (left, right) = if nest_left {
            (ty, Final::unit())
        } else {
            (Final::unit(), ty)
        };
        ty = if is_sum {
            Final::sum(left, right)
        } else {
            Final::product(left, right)
        };
    }
    assert_eq!(ty.bit_width(), if is_sum { DEPTH } else { 0 });
    drop(ty);
    assert!(leaf.upgrade().is_none());
}

#[test]
fn drop_left_product() {
    on_small_stack("drop_left_product", || drop_nested_type(false, true));
}

#[test]
fn drop_right_product() {
    on_small_stack("drop_right_product", || drop_nested_type(false, false));
}

#[test]
fn drop_left_sum() {
    on_small_stack("drop_left_sum", || drop_nested_type(true, true));
}

#[test]
fn drop_right_sum() {
    on_small_stack("drop_right_sum", || drop_nested_type(true, false));
}

#[test]
fn drop_shared_type() {
    on_small_stack("drop_shared_type", || {
        let mut ty = Final::unit();
        let leaf = Arc::downgrade(&ty);
        for _ in 0..DEPTH {
            ty = Final::product(Arc::clone(&ty), ty);
        }
        // A clone by value also owns the shared children. They must remain
        // accessible until this last owner is dropped, then be freed exactly once.
        let retained = ty.as_ref().clone();
        drop(ty);
        assert_eq!(retained.bit_width(), 0);
        assert!(leaf.upgrade().is_some());
        drop(retained);
        assert!(leaf.upgrade().is_none());
    });
}

#[test]
fn bind_deep_complete_types() {
    on_small_stack("bind_deep_complete_types", || {
        for is_sum in [false, true] {
            for nest_left in [false, true] {
                for complete_first in [false, true] {
                    Context::with_context(|ctx| {
                        let mut complete = Final::unit();
                        let mut incomplete = Type::free(&ctx, "leaf".into());
                        for _ in 0..DEPTH {
                            let (cl, cr, il, ir) = if nest_left {
                                (
                                    complete,
                                    Final::unit(),
                                    incomplete,
                                    Type::free(&ctx, "r".into()),
                                )
                            } else {
                                (
                                    Final::unit(),
                                    complete,
                                    Type::free(&ctx, "l".into()),
                                    incomplete,
                                )
                            };
                            if is_sum {
                                complete = Final::sum(cl, cr);
                                incomplete = Type::sum(&ctx, il, ir);
                            } else {
                                complete = Final::product(cl, cr);
                                incomplete = Type::product(&ctx, il, ir);
                            }
                        }
                        let expected = complete.tmr();
                        let complete = Type::complete(&ctx, complete);
                        let (left, right) = if complete_first {
                            (&complete, &incomplete)
                        } else {
                            (&incomplete, &complete)
                        };
                        ctx.unify(left, right, "deep complete binding").unwrap();
                        assert_eq!(incomplete.finalize().unwrap().tmr(), expected);
                    });
                }
            }
        }
    });
}

#[test]
fn unify_deep_incomplete_types() {
    on_small_stack("unify_deep_incomplete_types", || {
        for is_sum in [false, true] {
            Context::with_context(|ctx| {
                let mut left = Type::unit(&ctx);
                let mut right = Type::free(&ctx, "leaf".into());
                let mut expected = Final::unit();
                for _ in 0..DEPTH {
                    let free = Type::free(&ctx, "right".into());
                    if is_sum {
                        left = Type::sum(&ctx, left, free);
                        right = Type::sum(&ctx, right, Type::unit(&ctx));
                        expected = Final::sum(expected, Final::unit());
                    } else {
                        left = Type::product(&ctx, left, free);
                        right = Type::product(&ctx, right, Type::unit(&ctx));
                        expected = Final::product(expected, Final::unit());
                    }
                }
                ctx.unify(&left, &right, "deep incomplete unification")
                    .unwrap();
                // Eager finalization must reach every ancestor, without an
                // explicit finalize() call hiding a missing continuation.
                assert_eq!(left.tmr(), Some(expected.tmr()));
                assert_eq!(right.tmr(), Some(expected.tmr()));
            });
        }
    });
}

#[test]
fn reject_deep_incomplete_types() {
    on_small_stack("reject_deep_incomplete_types", || {
        Context::with_context(|ctx| {
            let mut left = Type::unit(&ctx);
            let mut right = Type::two_two_n(&ctx, 0);
            for _ in 0..DEPTH {
                left = Type::product(&ctx, left, Type::free(&ctx, "left".into()));
                right = Type::product(&ctx, right, Type::free(&ctx, "right".into()));
            }
            for _ in 0..2 {
                let err = ctx.unify(&left, &right, "deep mismatch").unwrap_err();
                assert_eq!(
                    err.to_string(),
                    "failed to apply bound `2` to existing bound `1`: deep mismatch",
                );
            }
        });
    });
}

#[test]
fn decode_deep_program() {
    on_small_stack("decode_deep_program", || {
        // Build on a separate, large stack so a regression is detected in
        // decoding, rather than while constructing the test's input.
        let (bytes, cmr) = thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                Context::with_context(|ctx| {
                    let mut finished: Arc<ConstructNode> = Arc::unit(&ctx);
                    let mut unfinished: Arc<ConstructNode> = Arc::iden(&ctx);
                    for _ in 0..2253 {
                        finished = Arc::pair(&finished, &Arc::unit(&ctx)).unwrap();
                        unfinished = Arc::take(&unfinished);
                    }
                    let program = Arc::comp(&finished, &unfinished).unwrap();
                    let program = program.finalize_types().unwrap();
                    (program.to_vec_without_witness(), program.cmr())
                })
            })
            .unwrap()
            .join()
            .unwrap();
        assert!(bytes.len() <= 8192);
        Context::with_context(|ctx| {
            let decoded = ConstructNode::decode::<_, simplicity::jet::Core>(
                &ctx,
                BitIter::from(bytes.as_slice()),
            )
            .unwrap();
            let program = decoded.finalize_types().unwrap();
            assert_eq!(program.cmr(), cmr);
            assert_eq!(program.to_vec_without_witness(), bytes);
        });
    });
}

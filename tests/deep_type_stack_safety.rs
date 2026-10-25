// SPDX-License-Identifier: CC0-1.0

//! Exercise deep types on a small stack. Each test runs in its own subprocess
//! because a stack overflow aborts the process rather than unwinding the thread.

use std::process::Command;
use std::sync::Arc;
use std::thread;

use simplicity::types::Final;

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

fn drop_branching_type(nest_left: bool) {
    let mut ty = Final::unit();
    let leaf = Arc::downgrade(&ty);
    let mut siblings = Vec::with_capacity(DEPTH);
    for _ in 0..DEPTH {
        // Both children have children of their own, exercising the destructor's
        // work stack rather than only its path for leaves and shared children.
        let sibling = Final::sum(Final::unit(), Final::unit());
        siblings.push(Arc::downgrade(&sibling));
        ty = if nest_left {
            Final::product(ty, sibling)
        } else {
            Final::product(sibling, ty)
        };
    }
    assert_eq!(ty.bit_width(), DEPTH);
    drop(ty);
    assert!(leaf.upgrade().is_none());
    assert!(siblings
        .into_iter()
        .all(|sibling| sibling.upgrade().is_none()));
}

#[test]
fn drop_left_branching_type() {
    on_small_stack("drop_left_branching_type", || drop_branching_type(true));
}

#[test]
fn drop_right_branching_type() {
    on_small_stack("drop_right_branching_type", || drop_branching_type(false));
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

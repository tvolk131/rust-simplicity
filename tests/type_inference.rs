// SPDX-License-Identifier: CC0-1.0

use simplicity::types::{Context, Final, Type};

#[test]
fn nested_failure_preserves_successful_sibling() {
    Context::with_context(|ctx| {
        let good_left = Type::product(&ctx, Type::free(&ctx, "a".into()), Type::unit(&ctx));
        let good_right = Type::product(&ctx, Type::unit(&ctx), Type::free(&ctx, "b".into()));
        let x = Type::free(&ctx, "x".into());
        let y = Type::free(&ctx, "y".into());
        let bad_left = Type::sum(&ctx, Type::unit(&ctx), x.clone());
        let bad_right = Type::sum(&ctx, Type::two_two_n(&ctx, 0), y.clone());
        let left = Type::product(&ctx, good_left.clone(), bad_left.clone());
        let right = Type::product(&ctx, good_right.clone(), bad_right.clone());

        for _ in 0..2 {
            let err = ctx.unify(&left, &right, "nested failure").unwrap_err();
            assert_eq!(
                err.to_string(),
                "failed to apply bound `2` to existing bound `1`: nested failure",
            );
        }
        // The left subtree finished before the right subtree failed. Its
        // union and eager finalization must survive the error unwind.
        let expected = Final::product(Final::unit(), Final::unit()).tmr();
        assert_eq!(good_left.tmr(), Some(expected));
        assert_eq!(good_right.tmr(), Some(expected));
        assert!(!left.is_final());
        assert!(!right.is_final());

        // The failed subtree's union was undone, and its right child was not
        // visited. These variables remain independent and unconstrained.
        ctx.unify(&x, &Type::unit(&ctx), "x is unit").unwrap();
        ctx.unify(&y, &Type::two_two_n(&ctx, 0), "y is bit")
            .unwrap();
        assert_ne!(bad_left.finalize().unwrap(), bad_right.finalize().unwrap());
        assert_ne!(left.finalize().unwrap(), right.finalize().unwrap());
    });
}

#[test]
fn failure_after_swapping_union_roots() {
    Context::with_context(|ctx| {
        let unit = Type::unit(&ctx);
        let bit = Type::two_two_n(&ctx, 0);
        // Raise bit's union rank so it wins even as the second argument.
        ctx.unify(&bit, &Type::free(&ctx, "rank".into()), "raise rank")
            .unwrap();
        for _ in 0..2 {
            let err = ctx.unify(&unit, &bit, "ranked failure").unwrap_err();
            assert_eq!(
                err.to_string(),
                "failed to apply bound `1` to existing bound `2`: ranked failure",
            );
            assert_eq!(unit.tmr(), Some(Final::unit().tmr()));
            assert_eq!(bit.tmr(), Some(Final::two_two_n(0).unwrap().tmr()));
        }
    });
}

#[test]
fn eagerly_finalize_shared_children() {
    for is_sum in [false, true] {
        Context::with_context(|ctx| {
            let a = Type::free(&ctx, "a".into());
            let b = Type::free(&ctx, "b".into());
            let left_child = Type::product(&ctx, a, Type::unit(&ctx));
            let right_child = Type::product(&ctx, Type::unit(&ctx), b);
            let (left, right) = if is_sum {
                (
                    Type::sum(&ctx, left_child.clone(), left_child.clone()),
                    Type::sum(&ctx, right_child.clone(), right_child.clone()),
                )
            } else {
                (
                    Type::product(&ctx, left_child.clone(), left_child.clone()),
                    Type::product(&ctx, right_child.clone(), right_child.clone()),
                )
            };
            ctx.unify(&left, &right, "shared children").unwrap();
            let child = Final::product(Final::unit(), Final::unit());
            let expected = if is_sum {
                Final::sum(child.clone(), child)
            } else {
                Final::product(child.clone(), child)
            };
            assert_eq!(left.tmr(), Some(expected.tmr()));
            assert_eq!(right.tmr(), Some(expected.tmr()));
            assert!(left_child.is_final());
            assert!(right_child.is_final());
        });
    }
}

#[test]
fn bind_product_preserves_error_order_and_hint() {
    Context::with_context(|ctx| {
        let untouched = Type::free(&ctx, "untouched".into());
        let existing = Type::product(&ctx, Type::unit(&ctx), untouched.clone());
        for _ in 0..2 {
            let err = ctx
                .bind_product(
                    &existing,
                    &Type::two_two_n(&ctx, 0),
                    &Type::unit(&ctx),
                    "product mismatch",
                )
                .unwrap_err();
            assert_eq!(
                err.to_string(),
                "failed to apply bound `2` to existing bound `1`: product mismatch",
            );
            assert!(!untouched.is_final());
        }
        ctx.bind_product(
            &existing,
            &Type::unit(&ctx),
            &Type::unit(&ctx),
            "compatible",
        )
        .unwrap();
        assert!(existing.is_final());
    });
}

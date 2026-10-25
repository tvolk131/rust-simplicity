// SPDX-License-Identifier: CC0-1.0

//! The Union-Bound Algorithm
//!
//! Type inference proceeds using the union-bound algorithm, which maintains a
//! set of equivalence classes of types. Initially every type is free and lives
//! in its own equivalence class. As inference proceeds, types are constrained
//! to be equal to each other, and their equivalence classes are merged.
//!
//! The union-bound algorithm provides a very efficient way of tracking these
//! equivalence classes. Each type is stored in an [`UbElement`], an opaque data
//! structure which only provides access to the underlying data via the
//! [`UbElement::root`] method, which returns the representative of the element's
//! class.
//!
//! Merging classes is done using the [`UbElement::unify`] method. Since when two
//! classes are merged, there is no longer any way to distinguish elements of
//! either, it is essential that they actually be equal. The returned
//! [`PendingUnion`] contains the representatives of the original classes so
//! that the caller can check or constrain them to be equal.
//!
//! If those constraints fail, the caller must roll back the pending union.
//! Keeping this state explicitly lets type inference use a work stack instead
//! of recursive callbacks.
//!
//! This is a classic CS algorithm. We use the "path-halving" variant of it, which
//! was inspired by the same algorithm in the C implementation of the code, which
//! cites ``Worst-Case Analysis of Set Union Algorithms'' by Robert E. Tarjan and
//! Jan van Leeuwen (1984) as giving amortized time complexity of O(InvAck(n)).
//!

use std::sync::Arc;
use std::{cmp, mem, ops};

use ghost_cell::{GhostCell, GhostToken};

/// Trait describing objects that can be stored and manipulated by the union-bound
/// algorithm.
///
/// Because the algorithm depends on identity equality (i.e. two objects being
/// exactly the same in memory) such objects need to have such a notion of
/// equality. In general this differs from the `Eq` trait which implements
/// "semantic equality".
pub trait PointerLike {
    /// Whether two objects are the same.
    fn ptr_eq(&self, other: &Self) -> bool;

    /// A "shallow copy" of the object.
    fn shallow_clone(&self) -> Self;
}

impl<T> PointerLike for Arc<T> {
    fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(self, other)
    }
    fn shallow_clone(&self) -> Self {
        Arc::clone(self)
    }
}

/// Container which associates a ghost token with some arbitrary other data.
///
/// This allows the union-bound algorithm to work with a token (which is used
/// by the algorithm) while passing data (which is -not- used by the algorithm)
/// everywhere that needs it, without offending the borrow checker or forcing
/// callers to manually destructure their types to separate out tokens.
///
/// If Rust had view types, this structure wouldn't be necessary.
pub struct WithGhostToken<'brand, T> {
    pub token: GhostToken<'brand>,
    pub inner: T,
}

impl<'brand, T> ops::Deref for WithGhostToken<'brand, T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.inner
    }
}

impl<'brand, T> ops::DerefMut for WithGhostToken<'brand, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

pub struct UbElement<'brand, T> {
    inner: Arc<GhostCell<'brand, UbInner<'brand, T>>>,
}

impl<T> Clone for UbElement<'_, T> {
    fn clone(&self) -> Self {
        UbElement {
            inner: Arc::clone(&self.inner),
        }
    }
}

struct UbInner<'brand, T> {
    data: UbData<'brand, T>,
    rank: usize,
}

enum UbData<'brand, T> {
    Root(T),
    EqualTo(UbElement<'brand, T>),
}

/// A union whose representatives still need to be bound to each other.
///
/// Drop this after a successful bind. On failure, roll back pending unions in
/// reverse order. Unions whose binds already succeeded should not be undone.
#[must_use]
pub struct PendingUnion<'brand, T> {
    pub new_root: T,
    pub old_root: T,
    child: UbElement<'brand, T>,
}

impl<'brand, T> PendingUnion<'brand, T> {
    pub fn rollback(self, token: &mut GhostToken<'brand>) {
        // As in the recursive implementation, retain ranks and path compression.
        self.child.inner.borrow_mut(token).data = UbData::Root(self.old_root);
    }
}

impl<T> UbData<'_, T> {
    fn unwrap_root(&self) -> &T {
        match self {
            UbData::Root(ref x) => x,
            UbData::EqualTo(..) => unreachable!(),
        }
    }
}

impl<T> UbElement<'_, T> {
    /// Turns an existing piece of data into a singleton union-bound set.
    pub fn new(data: T) -> Self {
        UbElement {
            inner: Arc::new(GhostCell::new(UbInner {
                data: UbData::Root(data),
                rank: 0,
            })),
        }
    }

    /// Clones the `UbElement`.
    ///
    /// This is the same as just calling `.clone()` but has a different name to
    /// emphasize that what's being cloned is internally just an Arc.
    pub fn shallow_clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<'brand, T: PointerLike> UbElement<'brand, T> {
    /// Find the representative of this object in its disjoint set.
    pub fn root(&self, token: &mut GhostToken<'brand>) -> T {
        let root = self.root_element(token);
        let inner_lock = root.inner.borrow(token);
        inner_lock.data.unwrap_root().shallow_clone()
    }

    /// Find the representative of this object in its disjoint set.
    fn root_element(&self, token: &mut GhostToken<'brand>) -> Self {
        let mut x: Self = self.shallow_clone();
        loop {
            // Find the parent of the current target, if there is one. If not, we
            // are done, so return.
            let parent: &Self = match x.inner.borrow(token).data {
                UbData::Root(..) => return x.shallow_clone(),
                UbData::EqualTo(ref parent) => parent,
            };

            // Find the grandparent of the current target, if there is one. If not, we
            // are done, so return.
            let grandparent: &Self = match parent.inner.borrow(token).data {
                UbData::Root(..) => return parent.shallow_clone(),
                UbData::EqualTo(ref grandparent) => grandparent,
            };

            // If the parent has a parent, remove the intermediate link. (This is
            // the "halving" variant of union-bound.)
            let grandparent = grandparent.shallow_clone();
            x.inner.borrow_mut(token).data = UbData::EqualTo(grandparent.shallow_clone());
            x = grandparent;
        }
    }

    /// Combine two sets.
    ///
    /// When the two sets are combined, the representative of one will be replaced
    /// by the representative of the other. The caller must bind the returned
    /// `new_root` to `old_root`, rolling back the union if that fails. Returns
    /// `None` if the elements already belong to the same set.
    pub fn unify(
        &self,
        token: &mut GhostToken<'brand>,
        other: &Self,
    ) -> Option<PendingUnion<'brand, T>> {
        let mut x_root = self.root_element(token);
        let mut y_root = other.root_element(token);

        let x_elem = x_root.inner.borrow(token);
        let y_elem = y_root.inner.borrow(token);

        // In the case that we are unifying a variable with itself, there is
        // nothing to do. So exit early.
        if x_elem.data.unwrap_root().ptr_eq(y_elem.data.unwrap_root()) {
            return None;
        }

        // Swap so that x always has rank >= y. Then x will become the parent of
        // y, meaning that y's root will be replaced by x's root.
        let rank_ord = x_elem.rank.cmp(&y_elem.rank);
        match rank_ord {
            cmp::Ordering::Less => {
                // Swap x_root and y_root. This invalidates x_elem and y_elem, but
                // the Rust borrowck ensures that we can't reuse them :-).
                mem::swap(&mut x_root, &mut y_root);
            }
            cmp::Ordering::Equal => {
                let x_elem = x_root.inner.borrow_mut(token);
                assert_ne!(
                    x_elem.rank,
                    usize::MAX,
                    "Attempted to unify two frozen variables",
                );
                x_elem.rank += 1;
            }
            _ => {}
        }

        let x_elem = x_root.inner.borrow(token);
        let x_data = match x_elem.data {
            UbData::Root(ref data) => data.shallow_clone(),
            UbData::EqualTo(..) => unreachable!(),
        };

        let y_elem = y_root.inner.borrow_mut(token);
        let old_y_data = mem::replace(&mut y_elem.data, UbData::EqualTo(x_root.shallow_clone()));

        match old_y_data {
            UbData::Root(y_data) => Some(PendingUnion {
                new_root: x_data,
                old_root: y_data,
                child: y_root,
            }),
            UbData::EqualTo(..) => unreachable!(),
        }
    }
}

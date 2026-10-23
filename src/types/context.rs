// SPDX-License-Identifier: CC0-1.0

//! Type Inference Context
//!
//! When constructing a Simplicity program, you must first create a type inference
//! context, in which type inference occurs incrementally during construction. Each
//! leaf node (e.g. `unit` and `iden`) must explicitly refer to the type inference
//! context, while combinator nodes (e.g. `comp`) infer the context from their
//! children, raising an error if there are multiple children whose contexts don't
//! match.
//!
//! This helps to prevent situations in which users attempt to construct multiple
//! independent programs, but types in one program accidentally refer to types in
//! the other.
//!

use std::any::TypeId;
use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex, MutexGuard};

use ghost_cell::GhostToken;

use crate::dag::{Dag, DagLike, SharingTracker};
use crate::jet::Jet;

use super::union_bound::PendingUnion;
use super::{
    Bound, CompleteBound, Error, Final, Incomplete, Type, TypeInner, UbElement, WithGhostToken,
};

// Copied from ghost_cell source. See
//     https://arhan.sh/blog/the-generativity-pattern-in-rust/
// in particular the box labeled "Throughout the years lifetime invariance has
// been achieved in several other ways." for some detail about this.
type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

/// Type inference context, or handle to a context.
///
/// Can be cheaply cloned with [`Context::shallow_clone`]. These clones will
/// refer to the same underlying type inference context, and can be used as
/// handles to each other. The derived [`Context::clone`] has the same effect.
///
/// There is currently no way to create an independent context with the same
/// type inference variables (i.e. a deep clone). If you need this functionality,
/// please file an issue.
#[derive(Clone)]
pub struct Context<'brand> {
    inner: Arc<Mutex<WithGhostToken<'brand, ContextInner<'brand>>>>,
}

struct ContextInner<'brand> {
    slab: Vec<Bound<'brand>>,
    /// Concrete jet type registered in this context, if any.
    jet_type: Option<TypeId>,
}

impl fmt::Debug for Context<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let id = Arc::as_ptr(&self.inner) as usize;
        write!(f, "inference_ctx_{:08x}", id)
    }
}

impl PartialEq for Context<'_> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}
impl Eq for Context<'_> {}

impl<'brand> Context<'brand> {
    /// Creates a scope with a new empty type inference context.
    pub fn with_context<R, F>(fun: F) -> R
    where
        F: for<'new_brand> FnOnce(Context<'new_brand>) -> R,
    {
        GhostToken::new(|token| {
            let ctx = Context::new(token);
            fun(ctx)
        })
    }

    /// Creates a new empty type inference context.
    pub fn new(token: GhostToken<'brand>) -> Self {
        Context {
            inner: Arc::new(Mutex::new(WithGhostToken {
                token,
                inner: ContextInner {
                    slab: vec![],
                    jet_type: None,
                },
            })),
        }
    }

    /// Helper function to allocate a bound and return a reference to it.
    fn alloc_bound(&self, bound: Bound<'brand>) -> BoundRef<'brand> {
        let mut lock = self.lock();
        lock.alloc_bound(bound)
    }

    /// Allocate a new free type bound, and return a reference to it.
    pub fn alloc_free(&self, name: String) -> BoundRef<'brand> {
        self.alloc_bound(Bound::Free(name))
    }

    /// Allocate a new unit type bound, and return a reference to it.
    pub fn alloc_unit(&self) -> BoundRef<'brand> {
        self.alloc_bound(Bound::Complete(Final::unit()))
    }

    /// Allocate a new unit type bound, and return a reference to it.
    pub fn alloc_complete(&self, data: Arc<Final>) -> BoundRef<'brand> {
        self.alloc_bound(Bound::Complete(data))
    }

    /// Allocate a new sum-type bound, and return a reference to it.
    pub fn alloc_sum(&self, left: Type<'brand>, right: Type<'brand>) -> BoundRef<'brand> {
        let mut lock = self.lock();
        if let Some((data1, data2)) = lock.complete_pair_data(&left.inner, &right.inner) {
            lock.alloc_bound(Bound::Complete(Final::sum(data1, data2)))
        } else {
            lock.alloc_bound(Bound::Sum(left.inner, right.inner))
        }
    }

    /// Allocate a new product-type bound, and return a reference to it.
    pub fn alloc_product(&self, left: Type<'brand>, right: Type<'brand>) -> BoundRef<'brand> {
        let mut lock = self.lock();
        if let Some((data1, data2)) = lock.complete_pair_data(&left.inner, &right.inner) {
            lock.alloc_bound(Bound::Complete(Final::product(data1, data2)))
        } else {
            lock.alloc_bound(Bound::Product(left.inner, right.inner))
        }
    }

    /// Creates a new handle to the context.
    ///
    /// This handle holds a reference to the underlying context and will keep
    /// it alive. The context will only be dropped once all handles, including
    /// the original context object, are dropped.
    pub fn shallow_clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }

    /// Checks whether two inference contexts are equal, and returns an error if not.
    pub fn check_eq(&self, other: &Self) -> Result<(), super::Error> {
        if self == other {
            Ok(())
        } else {
            Err(super::Error::InferenceContextMismatch)
        }
    }

    /// Asserts that all jets in this context have the same concrete type.
    ///
    /// Records the jet's type on first call, panics on subsequent calls with
    /// a different concrete type.
    pub fn check_jet(&self, jet: &dyn Jet) {
        let new_id = jet.as_any().type_id();
        let mut lock = self.lock();

        if let Some(existing_id) = lock.inner.jet_type {
            assert!(existing_id == new_id, "mixed jet types in context");

            return;
        }

        lock.inner.jet_type = Some(new_id);
    }

    /// Accesses a bound.
    pub(super) fn get(&self, bound: &BoundRef<'brand>) -> Bound<'brand> {
        let lock = self.lock();
        lock.inner.slab[bound.index].shallow_clone()
    }

    /// Accesses a bound through a union-bound element.
    pub(super) fn get_root_ref(
        &self,
        bound: &UbElement<'brand, BoundRef<'brand>>,
    ) -> BoundRef<'brand> {
        let mut lock = self.lock();
        bound.root(&mut lock.token)
    }

    /// Reassigns a bound to a different bound.
    ///
    /// # Panics
    ///
    /// Panics if called on a complete type. This is a sanity-check to avoid
    /// replacing already-completed types, which can cause inefficiencies in
    /// the union-bound algorithm (and if our replacement changes the type,
    /// this is probably a bug.
    ///
    /// Also panics if passed a `BoundRef` that was not allocated by this context.
    pub(super) fn reassign_non_complete(&self, bound: BoundRef<'brand>, new: Bound<'brand>) {
        let mut lock = self.lock();
        lock.reassign_non_complete(bound, new);
    }

    /// Binds the type to a product bound formed by the two inner types. If this
    /// fails, attach the provided hint to the error.
    ///
    /// Fails if the type has an existing incompatible bound.
    pub fn bind_product(
        &self,
        existing: &Type<'brand>,
        prod_l: &Type<'brand>,
        prod_r: &Type<'brand>,
        hint: &'static str,
    ) -> Result<(), Error> {
        let mut lock = self.lock();
        let existing_root = existing.inner.bound.root(&mut lock.token);
        let new_bound = Bound::Product(prod_l.inner.shallow_clone(), prod_r.inner.shallow_clone());

        lock.bind(existing_root, new_bound).map_err(|e| {
            let new_bound = lock.alloc_bound(e.new);
            drop(lock);
            Error::Bind {
                existing_bound: Incomplete::from_bound_ref(self, e.existing),
                new_bound: Incomplete::from_bound_ref(self, new_bound),
                hint,
            }
        })
    }

    /// Unify the type with another one.
    ///
    /// Fails if the bounds on the two types are incompatible
    pub fn unify(
        &self,
        ty1: &Type<'brand>,
        ty2: &Type<'brand>,
        hint: &'static str,
    ) -> Result<(), Error> {
        let mut lock = self.lock();
        lock.unify(&ty1.inner, &ty2.inner).map_err(|e| {
            let new_bound = lock.alloc_bound(e.new);
            drop(lock);
            Error::Bind {
                existing_bound: Incomplete::from_bound_ref(self, e.existing),
                new_bound: Incomplete::from_bound_ref(self, new_bound),
                hint,
            }
        })
    }

    /// Locks the underlying slab mutex.
    fn lock(&self) -> MutexGuard<'_, WithGhostToken<'brand, ContextInner<'brand>>> {
        self.inner.lock().unwrap()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoundRef<'brand> {
    phantom: InvariantLifetime<'brand>,
    index: usize,
}

impl<'brand> BoundRef<'brand> {
    /// Creates an "occurs-check ID" which is just a copy of the [`BoundRef`]
    /// with `PartialEq` and `Eq` implemented in terms of underlying pointer
    /// equality.
    pub fn occurs_check_id(&self) -> OccursCheckId<'brand> {
        OccursCheckId {
            phantom: InvariantLifetime::default(),
            index: self.index,
        }
    }
}

impl super::PointerLike for BoundRef<'_> {
    fn ptr_eq(&self, other: &Self) -> bool {
        self.index == other.index
    }

    fn shallow_clone(&self) -> Self {
        BoundRef {
            phantom: InvariantLifetime::default(),
            index: self.index,
        }
    }
}

pub type CtxAndBoundRef<'ctx, 'brand> = (&'ctx Context<'brand>, BoundRef<'brand>);

impl<'brand> DagLike for CtxAndBoundRef<'_, 'brand> {
    type Node = BoundRef<'brand>;
    fn data(&self) -> &BoundRef<'brand> {
        &self.1
    }

    fn as_dag_node(&self) -> Dag<Self> {
        match self.0.get(&self.1) {
            Bound::Free(..) | Bound::Complete(..) => Dag::Nullary,
            Bound::Sum(ref ty1, ref ty2) | Bound::Product(ref ty1, ref ty2) => {
                let root1 = self.0.get_root_ref(&ty1.bound);
                let root2 = self.0.get_root_ref(&ty2.bound);
                Dag::Binary((self.0, root1), (self.0, root2))
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct BoundRefSharing<'brand> {
    map: HashMap<BoundRef<'brand>, usize>,
}

impl<'brand> SharingTracker<CtxAndBoundRef<'_, 'brand>> for BoundRefSharing<'brand> {
    fn record(&mut self, d: &CtxAndBoundRef<'_, 'brand>, index: usize) -> Option<usize> {
        use std::collections::hash_map::Entry;
        match self.map.entry(d.1.clone()) {
            Entry::Occupied(occ) => Some(*occ.get()),
            Entry::Vacant(vac) => {
                vac.insert(index);
                None
            }
        }
    }
    fn seen_before(&self, d: &CtxAndBoundRef<'_, 'brand>) -> Option<usize> {
        self.map.get(&d.1).copied()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct OccursCheckId<'brand> {
    phantom: InvariantLifetime<'brand>,
    index: usize,
}

struct BindError<'brand> {
    existing: BoundRef<'brand>,
    new: Bound<'brand>,
}

/// Continuations for the depth-first binding traversal.
enum BindTask<'brand> {
    Bind(BoundRef<'brand>, Bound<'brand>),
    Unify(TypeInner<'brand>, TypeInner<'brand>),
    Finalize {
        existing: BoundRef<'brand>,
        is_sum: bool,
        left: TypeInner<'brand>,
        right: TypeInner<'brand>,
    },
    /// Keep the undo information until all bindings below this union succeed.
    FinishUnion(PendingUnion<'brand, BoundRef<'brand>>),
}

impl<'brand> ContextInner<'brand> {
    fn alloc_bound(&mut self, bound: Bound<'brand>) -> BoundRef<'brand> {
        self.slab.push(bound);
        let index = self.slab.len() - 1;

        BoundRef {
            phantom: InvariantLifetime::default(),
            index,
        }
    }

    fn reassign_non_complete(&mut self, bound: BoundRef<'brand>, new: Bound<'brand>) {
        assert!(
            !matches!(self.slab[bound.index], Bound::Complete(..)),
            "tried to modify finalized type",
        );
        self.slab[bound.index] = new;
    }
}

impl<'brand> WithGhostToken<'brand, ContextInner<'brand>> {
    /// It is a common situation that we are pairing two types, and in the
    /// case that they are both complete, we want to pair the complete types.
    ///
    /// This method deals with all the annoying/complicated member variable
    /// paths to get the actual complete data out.
    fn complete_pair_data(
        &mut self,
        inn1: &TypeInner<'brand>,
        inn2: &TypeInner<'brand>,
    ) -> Option<(Arc<Final>, Arc<Final>)> {
        let idx1 = inn1.bound.root(&mut self.token).index;
        let idx2 = inn2.bound.root(&mut self.token).index;
        let bound1 = &self.slab[idx1];
        let bound2 = &self.slab[idx2];
        if let (Bound::Complete(ref data1), Bound::Complete(ref data2)) = (bound1, bound2) {
            Some((Arc::clone(data1), Arc::clone(data2)))
        } else {
            None
        }
    }
    /// Unify the type with another one.
    ///
    /// Fails if the bounds on the two types are incompatible
    fn unify(
        &mut self,
        existing: &TypeInner<'brand>,
        other: &TypeInner<'brand>,
    ) -> Result<(), BindError<'brand>> {
        if let Some(union) = existing.bound.unify(&mut self.token, &other.bound) {
            let new = self.slab[union.old_root.index].shallow_clone();
            let result = self.bind(union.new_root.clone(), new);
            if result.is_err() {
                union.rollback(&mut self.token);
            }
            result
        } else {
            Ok(())
        }
    }

    fn bind(
        &mut self,
        existing: BoundRef<'brand>,
        new: Bound<'brand>,
    ) -> Result<(), BindError<'brand>> {
        // Start with a task outside the Vec so that leaf bindings, including
        // free and complete types, do not need to allocate a work stack.
        let mut task = BindTask::Bind(existing, new);
        let mut stack = Vec::new();
        loop {
            match task {
                BindTask::Bind(existing, new) => {
                    if let Err(err) = self.bind_step(existing, new, &mut stack) {
                        // This is the recursive error unwind: only unions whose
                        // child bindings have not finished are rolled back.
                        while let Some(task) = stack.pop() {
                            if let BindTask::FinishUnion(union) = task {
                                union.rollback(&mut self.token);
                            }
                        }
                        return Err(err);
                    }
                }
                BindTask::Unify(existing, other) => {
                    if let Some(union) = existing.bound.unify(&mut self.token, &other.bound) {
                        let existing = union.new_root.clone();
                        let new = self.slab[union.old_root.index].shallow_clone();
                        stack.push(BindTask::FinishUnion(union));
                        stack.push(BindTask::Bind(existing, new));
                    }
                }
                BindTask::Finalize {
                    existing,
                    is_sum,
                    left,
                    right,
                } => {
                    // Finalize only after both children's bindings have run,
                    // preserving the information available during inference.
                    if let Some((data1, data2)) = self.complete_pair_data(&left, &right) {
                        self.reassign_non_complete(
                            existing,
                            Bound::Complete(if is_sum {
                                Final::sum(data1, data2)
                            } else {
                                Final::product(data1, data2)
                            }),
                        );
                    }
                }
                BindTask::FinishUnion(_) => {}
            }
            match stack.pop() {
                Some(next) => task = next,
                None => return Ok(()),
            }
        }
    }

    fn bind_step(
        &mut self,
        existing: BoundRef<'brand>,
        new: Bound<'brand>,
        stack: &mut Vec<BindTask<'brand>>,
    ) -> Result<(), BindError<'brand>> {
        // Unlike the recursive traversal, this step only queues child bindings,
        // so it can borrow the existing bound instead of cloning it. Borrow the
        // slab explicitly to allow independent access to the ghost token below.
        let existing_bound = &self.inner.slab[existing.index];
        let bind_error = || BindError {
            existing: existing.clone(),
            new: new.shallow_clone(),
        };

        match (existing_bound, &new) {
            (_, Bound::Free(_)) => Ok(()),
            (Bound::Free(_), _) => {
                self.reassign_non_complete(existing, new);
                Ok(())
            }
            (Bound::Complete(existing_final), Bound::Complete(new_final)) => {
                if existing_final == new_final {
                    Ok(())
                } else {
                    Err(bind_error())
                }
            }
            // Bind the children of an incomplete type to the complete children.
            (Bound::Complete(complete), incomplete) | (incomplete, Bound::Complete(complete)) => {
                match (complete.bound(), incomplete) {
                    // A unit might match a Bound::Free(..) or a Bound::Complete(..),
                    // and both cases were handled above. So this is an error.
                    (CompleteBound::Unit, _) => Err(bind_error()),
                    (
                        CompleteBound::Product(ref comp1, ref comp2),
                        Bound::Product(ref ty1, ref ty2),
                    )
                    | (CompleteBound::Sum(ref comp1, ref comp2), Bound::Sum(ref ty1, ref ty2)) => {
                        let bound1 = ty1.bound.root(&mut self.token);
                        let bound2 = ty2.bound.root(&mut self.token);
                        stack.push(BindTask::Bind(bound2, Bound::Complete(Arc::clone(comp2))));
                        stack.push(BindTask::Bind(bound1, Bound::Complete(Arc::clone(comp1))));
                        Ok(())
                    }
                    _ => Err(bind_error()),
                }
            }
            (Bound::Sum(ref x1, ref x2), Bound::Sum(ref y1, ref y2))
            | (Bound::Product(ref x1, ref x2), Bound::Product(ref y1, ref y2)) => {
                // LIFO order: finish the left subtree, then the right subtree,
                // then eagerly finalize the parent if both children are complete.
                stack.push(BindTask::Finalize {
                    existing,
                    is_sum: matches!(existing_bound, Bound::Sum(..)),
                    left: y1.shallow_clone(),
                    right: y2.shallow_clone(),
                });
                stack.push(BindTask::Unify(x2.shallow_clone(), y2.shallow_clone()));
                stack.push(BindTask::Unify(x1.shallow_clone(), y1.shallow_clone()));
                Ok(())
            }
            (_, _) => Err(bind_error()),
        }
    }
}

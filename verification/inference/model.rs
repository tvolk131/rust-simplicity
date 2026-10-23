// SPDX-License-Identifier: CC0-1.0
// Standalone Verus model of commit ea065b8's continuation/undo mechanics.
// This is not linked into simplicity-lang. See README.md for the proof boundary.
use vstd::prelude::*;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

#[derive(Clone, Copy)]
pub enum Data {
    Root(usize),
    EqualTo(usize),
}

#[derive(Clone, Copy)]
struct Pending {
    child: usize,
    old_root: usize,
    new_root: usize,
}

// Identifiers stand for existing handles, so repeated identifiers retain sharing.
// Binding decisions and the contents of types are outside this control model.
#[derive(Clone, Copy)]
enum Task {
    Bind(usize, usize),
    Unify(usize, usize),
    Finalize(usize, bool, usize, usize),
    FinishUnion(Pending),
}

pub struct Heap {
    pub data: Vec<Data>,
    pub ranks: Vec<usize>,
    pub bounds: Vec<usize>,
}

pub struct Snapshot {
    pub data: Seq<Data>,
    pub ranks: Seq<usize>,
    pub bounds: Seq<usize>,
}

impl View for Heap {
    type V = Snapshot;
    open spec fn view(&self) -> Snapshot {
        Snapshot { data: self.data@, ranks: self.ranks@, bounds: self.bounds@ }
    }
}

// Logical order of execution, with the next operation first.
spec fn execution_order(stack: Seq<Task>) -> Seq<Task>
    decreases stack.len(),
{
    if stack.len() == 0 { Seq::empty() }
    else { seq![stack.last()] + execution_order(stack.drop_last()) }
}

proof fn push_pop<A>(s: Seq<A>, a: A)
    ensures s.push(a).drop_last() == s, s.push(a).last() == a,
{
    assert(s.push(a).drop_last() =~= s);
}

proof fn order_push(s: Seq<Task>, task: Task)
    ensures execution_order(s.push(task)) == seq![task] + execution_order(s),
{
    push_pop(s, task);
}

// Active recursive call frames, oldest first. Ordinary queued work is not an
// active call and must never be executed during error unwinding.
spec fn active_calls(stack: Seq<Task>) -> Seq<Pending>
    decreases stack.len(),
{
    if stack.len() == 0 { Seq::empty() }
    else {
        let outer = active_calls(stack.drop_last());
        match stack.last() {
            Task::FinishUnion(u) => outer.push(u),
            _ => outer,
        }
    }
}

spec fn valid_stack(stack: Seq<Task>, n: nat) -> bool {
    forall|i: int| 0 <= i < stack.len() ==> match #[trigger] stack[i] {
        Task::FinishUnion(u) => u.child < n,
        _ => true,
    }
}

spec fn restore(s: Snapshot, u: Pending) -> Snapshot {
    Snapshot {
        data: s.data.update(u.child as int, Data::Root(u.old_root)),
        ranks: s.ranks,
        bounds: s.bounds,
    }
}

// Reference semantics for recursive error returns: restore the innermost
// unfinished call, then propagate the error to its caller. This intentionally
// preserves the current bounds/ranks and any work whose call already returned.
spec fn recursive_error(s: Snapshot, calls: Seq<Pending>) -> Snapshot
    decreases calls.len(),
{
    if calls.len() == 0 { s }
    else { recursive_error(restore(s, calls.last()), calls.drop_last()) }
}

fn rollback(heap: &mut Heap, u: Pending)
    requires u.child < old(heap).data.len(),
    ensures final(heap)@ == restore(old(heap)@, u),
{
    heap.data.set(u.child, Data::Root(u.old_root));
}

spec fn root_value(data: Data) -> usize {
    match data { Data::Root(v) => v, _ => 0 }
}

spec fn can_merge(s: Snapshot, x: usize, y: usize) -> bool {
    &&& s.data.len() == s.ranks.len()
    &&& x < s.data.len()
    &&& y < s.data.len()
    &&& s.data[x as int] is Root
    &&& s.data[y as int] is Root
    &&& (s.ranks[x as int] == s.ranks[y as int]
        && root_value(s.data[x as int]) != root_value(s.data[y as int]))
        ==> s.ranks[x as int] < usize::MAX
}

spec fn selected_parent(s: Snapshot, x: usize, y: usize) -> usize {
    if s.ranks[x as int] < s.ranks[y as int] { y } else { x }
}

spec fn selected_child(s: Snapshot, x: usize, y: usize) -> usize {
    if s.ranks[x as int] < s.ranks[y as int] { x } else { y }
}

spec fn merged(s: Snapshot, x: usize, y: usize) -> Snapshot {
    if root_value(s.data[x as int]) == root_value(s.data[y as int]) { s }
    else {
        Snapshot {
            data: s.data.update(selected_child(s, x, y) as int,
                Data::EqualTo(selected_parent(s, x, y))),
            ranks: if s.ranks[x as int] == s.ranks[y as int] {
                s.ranks.update(x as int, (s.ranks[x as int] + 1) as usize)
            } else { s.ranks },
            bounds: s.bounds,
        }
    }
}

// Starts after root_element has found the two representatives. Resolving roots
// and proving path-halving correct are deliberately outside this experiment.
fn merge_roots(heap: &mut Heap, x: usize, y: usize) -> (result: Option<Pending>)
    requires can_merge(old(heap)@, x, y),
    ensures
        final(heap)@ == merged(old(heap)@, x, y),
        match result {
            None => root_value(old(heap).data@[x as int]) == root_value(old(heap).data@[y as int]),
            Some(u) => {
                &&& u.child == selected_child(old(heap)@, x, y)
                &&& u.old_root == root_value(old(heap).data@[u.child as int])
                &&& u.new_root == root_value(old(heap).data@[selected_parent(old(heap)@, x, y) as int])
                &&& u.old_root != u.new_root
            }
        },
{
    let x_data = match heap.data[x] { Data::Root(v) => v, _ => { assert(false); 0 } };
    let y_data = match heap.data[y] { Data::Root(v) => v, _ => { assert(false); 0 } };
    if x_data == y_data { return None; }
    let mut parent = x;
    let mut child = y;
    if heap.ranks[x] < heap.ranks[y] {
        parent = y;
        child = x;
    } else if heap.ranks[x] == heap.ranks[y] {
        let rank = heap.ranks[x];
        heap.ranks.set(x, rank + 1);
    }
    let new_root = match heap.data[parent] { Data::Root(v) => v, _ => { assert(false); 0 } };
    let old_root = match heap.data[child] { Data::Root(v) => v, _ => { assert(false); 0 } };
    heap.data.set(child, Data::EqualTo(parent));
    Some(Pending { child, old_root, new_root })
}

// Failed immediate binding restores the selected child's data even if union
// rank swapped the argument order. Rank increments intentionally survive.
fn merge_then_reject(heap: &mut Heap, x: usize, y: usize)
    requires can_merge(old(heap)@, x, y),
    ensures
        final(heap).data@ == old(heap).data@,
        final(heap).ranks@ == merged(old(heap)@, x, y).ranks,
        final(heap).bounds@ == old(heap).bounds@,
{
    let ghost before = heap@;
    if let Some(u) = merge_roots(heap, x, y) {
        rollback(heap, u);
        proof { assert(heap.data@ =~= before.data); }
    }
}

// Same push order as context.rs's Sum/Sum and Product/Product arm. The
// postcondition is written in recursive execution order, independent of LIFO.
fn schedule_compound(
    stack: &mut Vec<Task>, parent: usize, is_sum: bool,
    x1: usize, x2: usize, y1: usize, y2: usize,
)
    ensures
        execution_order(final(stack)@) == seq![
            Task::Unify(x1, y1), Task::Unify(x2, y2),
            Task::Finalize(parent, is_sum, y1, y2),
        ] + execution_order(old(stack)@),
        final(stack)@ == old(stack)@.push(Task::Finalize(parent, is_sum, y1, y2))
            .push(Task::Unify(x2, y2)).push(Task::Unify(x1, y1)),
{
    let ghost base = stack@;
    stack.push(Task::Finalize(parent, is_sum, y1, y2));
    stack.push(Task::Unify(x2, y2)); // mutation: right push
    stack.push(Task::Unify(x1, y1)); // mutation: left push
    proof {
        let f = Task::Finalize(parent, is_sum, y1, y2);
        let r = Task::Unify(x2, y2);
        let l = Task::Unify(x1, y1);
        order_push(base, f);
        order_push(base.push(f), r);
        order_push(base.push(f).push(r), l);
        assert(execution_order(stack@) =~= seq![l, r, f] + execution_order(base));
    }
}

fn schedule_complete(
    stack: &mut Vec<Task>, bound1: usize, bound2: usize, comp1: usize, comp2: usize,
)
    ensures execution_order(final(stack)@) == seq![
        Task::Bind(bound1, comp1), Task::Bind(bound2, comp2),
    ] + execution_order(old(stack)@),
{
    let ghost base = stack@;
    stack.push(Task::Bind(bound2, comp2));
    stack.push(Task::Bind(bound1, comp1));
    proof {
        let r = Task::Bind(bound2, comp2);
        let l = Task::Bind(bound1, comp1);
        order_push(base, r);
        order_push(base.push(r), l);
        assert(execution_order(stack@) =~= seq![l, r] + execution_order(base));
    }
}

fn schedule_union(stack: &mut Vec<Task>, u: Pending, new_bound: usize)
    ensures
        execution_order(final(stack)@) == seq![
            Task::Bind(u.new_root, new_bound), Task::FinishUnion(u),
        ] + execution_order(old(stack)@),
        active_calls(final(stack)@) == active_calls(old(stack)@).push(u),
        final(stack)@ == old(stack)@.push(Task::FinishUnion(u)).push(Task::Bind(u.new_root, new_bound)),
{
    let ghost base = stack@;
    stack.push(Task::FinishUnion(u)); // mutation: finish push
    stack.push(Task::Bind(u.new_root, new_bound)); // mutation: bind push
    proof {
        let finish = Task::FinishUnion(u);
        let bind = Task::Bind(u.new_root, new_bound);
        order_push(base, finish);
        order_push(base.push(finish), bind);
        push_pop(base, finish);
        push_pop(base.push(finish), bind);
        reveal_with_fuel(active_calls, 3);
        assert(execution_order(stack@) =~= seq![bind, finish] + execution_order(base));
    }
}

fn finish_union(heap: &mut Heap, stack: &mut Vec<Task>)
    requires
        old(stack).len() > 0,
        old(stack)@.last() is FinishUnion,
    ensures
        final(heap)@ == old(heap)@,
        final(stack)@ == old(stack)@.drop_last(),
        active_calls(final(stack)@) == active_calls(old(stack)@).drop_last(),
{
    let _ = stack.pop().unwrap();
}

proof fn error_step(s: Snapshot, stack: Seq<Task>)
    requires stack.len() > 0,
    ensures recursive_error(s, active_calls(stack)) == match stack.last() {
        Task::FinishUnion(u) => recursive_error(restore(s, u), active_calls(stack.drop_last())),
        _ => recursive_error(s, active_calls(stack.drop_last())),
    },
{
    if let Task::FinishUnion(u) = stack.last() {
        push_pop(active_calls(stack.drop_last()), u);
    }
}

// This is the actual pop/filter/restore loop, checked for arbitrary stack
// lengths and arbitrary slot aliasing, including repeated undo targets.
fn unwind(heap: &mut Heap, stack: &mut Vec<Task>)
    requires valid_stack(old(stack)@, old(heap).data@.len()),
    ensures
        final(stack).len() == 0,
        final(heap)@ == recursive_error(old(heap)@, active_calls(old(stack)@)),
        final(heap).data.len() == old(heap).data.len(),
{
    let ghost initial = recursive_error(heap@, active_calls(stack@));
    let ghost n = heap.data@.len();
    while stack.len() > 0
        invariant
            heap.data@.len() == n,
            valid_stack(stack@, n),
            recursive_error(heap@, active_calls(stack@)) == initial,
        decreases stack.len(),
    {
        let ghost before_stack = stack@;
        let ghost before_heap = heap@;
        proof { error_step(before_heap, before_stack); }
        let task = stack.pop().unwrap();
        if let Task::FinishUnion(u) = task {
            rollback(heap, u); // mutation: rollback
        }
    }
}

// The top-level union is held outside the work Vec in production. Its restore
// must happen after all nested frames have been unwound.
fn unwind_outer(heap: &mut Heap, stack: &mut Vec<Task>, outer: Pending)
    requires
        valid_stack(old(stack)@, old(heap).data@.len()),
        outer.child < old(heap).data.len(),
    ensures
        final(stack).len() == 0,
        final(heap)@ == restore(recursive_error(old(heap)@, active_calls(old(stack)@)), outer),
{
    unwind(heap, stack);
    rollback(heap, outer);
}

proof fn preserves_other_state(s: Snapshot, calls: Seq<Pending>)
    ensures
        recursive_error(s, calls).ranks == s.ranks,
        recursive_error(s, calls).bounds == s.bounds,
    decreases calls.len(),
{
    if calls.len() > 0 {
        preserves_other_state(restore(s, calls.last()), calls.drop_last());
    }
}

proof fn preserves_unrelated_slot(s: Snapshot, calls: Seq<Pending>, index: int)
    requires
        0 <= index < s.data.len(),
        forall|i: int| 0 <= i < calls.len() ==> (#[trigger] calls[i]).child != index,
    ensures recursive_error(s, calls).data[index] == s.data[index],
    decreases calls.len(),
{
    if calls.len() > 0 {
        preserves_unrelated_slot(restore(s, calls.last()), calls.drop_last(), index);
    }
}

// A non-vacuous composition of the verified operations. The heap contains
// aliases, ranks increase, a successful sibling changes a bound, and a later
// failure restores the right and outer unions while preserving that progress.
fn nested_partial_failure() {
    proof {
        reveal_with_fuel(active_calls, 4);
        reveal_with_fuel(recursive_error, 4);
    }
    let mut heap = Heap {
        data: vec![Data::Root(0), Data::Root(1), Data::Root(2),
            Data::Root(3), Data::Root(4), Data::Root(5)],
        ranks: vec![0, 0, 0, 0, 0, 0],
        bounds: vec![0, 1, 2, 3, 4, 5],
    };
    let outer = merge_roots(&mut heap, 0, 1).unwrap();
    let mut stack = Vec::new();
    schedule_compound(&mut stack, 0, false, 2, 4, 3, 5);
    let _ = stack.pop().unwrap(); // execute left Unify(2, 3)
    let left = merge_roots(&mut heap, 2, 3).unwrap();
    schedule_union(&mut stack, left, 3);
    let _ = stack.pop().unwrap(); // execute left Bind
    heap.bounds.set(2, 99);       // successful eager binding/finalization effect
    finish_union(&mut heap, &mut stack);
    let _ = stack.pop().unwrap(); // execute right Unify(4, 5)
    let right = merge_roots(&mut heap, 4, 5).unwrap();
    schedule_union(&mut stack, right, 5);
    let _ = stack.pop().unwrap(); // right Bind returns an error
    unwind_outer(&mut heap, &mut stack, outer);
    assert(heap.data@[1] == Data::Root(1));
    assert(heap.data@[5] == Data::Root(5));
    assert(heap.data@[3] == Data::EqualTo(2));
    assert(heap.bounds@[2] == 99);
    assert(heap.ranks@ == seq![1usize, 0, 1, 0, 1, 0]);
    assert(stack.len() == 0);
}

fn rank_swapped_failure() {
    let mut heap = Heap {
        data: vec![Data::Root(10), Data::Root(20)],
        ranks: vec![0, 5],
        bounds: Vec::new(),
    };
    let u = merge_roots(&mut heap, 0, 1).unwrap();
    assert(u.child == 0 && u.new_root == 20 && u.old_root == 10);
    rollback(&mut heap, u);
    assert(heap.data@ == seq![Data::Root(10), Data::Root(20)]);
    assert(heap.ranks@ == seq![0usize, 5]);
}

// Reverse order is observable even when undo records target the same slot.
// The general unwind theorem allows this aliasing; it does not require disjoint
// undo targets to make a FIFO implementation accidentally equivalent.
fn aliased_undo_targets() {
    proof {
        reveal_with_fuel(active_calls, 5);
        reveal_with_fuel(recursive_error, 3);
    }
    let mut heap = Heap {
        data: vec![Data::EqualTo(1), Data::Root(30)],
        ranks: vec![7, 8],
        bounds: vec![99],
    };
    let outer = Pending { child: 0, old_root: 10, new_root: 20 };
    let inner = Pending { child: 0, old_root: 20, new_root: 30 };
    let mut stack = vec![Task::FinishUnion(outer), Task::Finalize(0, false, 0, 0),
        Task::FinishUnion(inner), Task::Unify(0, 1)];
    unwind(&mut heap, &mut stack);
    assert(heap.data@[0] == Data::Root(10));
    assert(heap.ranks@ == seq![7usize, 8]);
    assert(heap.bounds@ == seq![99usize]);
}

fn main() {
    nested_partial_failure();
    rank_swapped_failure();
    aliased_undo_targets();
}

} // verus!

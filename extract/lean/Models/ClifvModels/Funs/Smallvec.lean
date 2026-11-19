/-
Handwritten executable models of the `smallvec` 1.15.1 functions used by the extracted code,
transcribed from `smallvec-1.15.1/src/lib.rs` (features: none; `union`, `specialization`,
`may_dangle`, `drain_filter` off).

A `SmallVec` is modeled by its element sequence (`ClifvModels.Types.Smallvec`). Every operation
below returns the element sequence the native one leaves, calls the trait methods of its
arguments (`Clone::clone`, `PartialEq::eq`, the closure, `Iterator::next`, `RangeBounds`) in the
native order and number, and panics (`fail .panic`) under the native panic conditions:

- index/range errors (`drain`'s `assert!`s and `checked_add`s, `Index`/`IndexMut` through the
  slice `SliceIndex` instance);
- "capacity overflow": the length exceeding `usize::MAX` (the model's `alloc.vec.Vec` bound).

Allocation failure (natively an abort through `handle_alloc_error`, or a "capacity overflow"
panic when the byte size of the buffer exceeds `isize::MAX`) is not modeled.

`Extend::extend` natively first calls `size_hint` and `reserve(lower)`: the model calls
`size_hint` too and panics ("capacity overflow") when `len + lower` overflows `usize`; the rest of
the reservation is unobservable apart from the allocation failures above.
-/
module
public import Aeneas
public import ClifvGen.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
universe u v
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.Smallvec

/-- A `Vec` with the elements `l`; panics ("capacity overflow") beyond `usize::MAX` elements. -/
def vecOfList {T : Type u} (l : List T) : Result (alloc.vec.Vec T) :=
  if h : l.length ≤ Usize.max then ok (alloc.vec.Vec.from l h) else fail .panic

/-- The `SmallVec` with the elements `l`. -/
def ofList {A : Type u} {T : Type v} (l : List T) : Result (smallvec.SmallVec A T) := do
  let v ← vecOfList l
  ok ⟨v⟩

/-- Drive an iterator to exhaustion; the yielded items in order. -/
def collect {It : Type u} {Item : Type v} (inst : core.iter.traits.iterator.Iterator It Item)
    (it : It) (acc : List Item) : Result (List Item) := do
  let (o, it) ← inst.next it
  match o with
  | none => ok acc.reverse
  | some x => collect inst it (x :: acc)
partial_fixpoint

/-- `n.checked_add(1).expect(..)` on a `usize`. -/
def succChecked (n : Std.Usize) : Result Nat :=
  if n.val + 1 ≤ Usize.max then ok (n.val + 1) else fail .panic

/-- The `start..end` of a `RangeBounds<usize>` against a length `len`, as in `SmallVec::drain`
(and `Vec::drain`'s slice-range check): `Excluded` start / `Included` end are incremented with
`checked_add(1)` (panic on overflow); then `assert!(start <= end)` and `assert!(end <= len)`. -/
def drainRange {R : Type u} (inst : core.ops.range.RangeBounds R Std.Usize) (r : R) (len : Nat) :
    Result (Nat × Nat) := do
  let sb ← inst.start_bound r
  let start ← match sb with
    | .Included n => ok n.val
    | .Excluded n => succChecked n
    | .Unbounded => ok 0
  let eb ← inst.end_bound r
  let stop ← match eb with
    | .Included n => succChecked n
    | .Excluded n => ok n.val
    | .Unbounded => ok len
  if start ≤ stop ∧ stop ≤ len then ok (start, stop) else fail .panic

/-- `clone` each element, in order. -/
def cloneList {T : Type u} (inst : core.clone.Clone T) : List T → Result (List T)
  | [] => ok []
  | x :: xs => do
    let y ← inst.clone x
    let ys ← cloneList inst xs
    ok (y :: ys)

/-- `n` calls of `clone` on `x`, in order. -/
def cloneN {T : Type u} (inst : core.clone.Clone T) (x : T) : Nat → Result (List T)
  | 0 => ok []
  | n + 1 => do
    let y ← inst.clone x
    let ys ← cloneN inst x n
    ok (y :: ys)

/-- `Formatter::debug_list().entries(xs).finish()`: each entry's `Debug::fmt`, in order,
stopping at the first error. (The formatter carries no output in the model.) -/
def debugEntries {T : Type u} (inst : core.fmt.Debug T) :
    List T → core.fmt.Formatter →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  | [], f => ok (.Ok (), f)
  | x :: xs, f => do
    let (r, f) ← inst.fmt x f
    match r with
    | .Ok _ => debugEntries inst xs f
    | .Err e => ok (.Err e, f)

/-- `dedup_by(|a, b| a == b)`: `kept` is the deduplicated prefix, reversed (its head is the
element at `w - 1`); each next element `x` is kept iff `!(x == last kept)`. -/
def dedupLoop {T : Type u} (inst : core.cmp.PartialEq T T) :
    List T → T → List T → Result (List T)
  | [], _, kept => ok kept.reverse
  | x :: xs, last, kept => do
    let same ← inst.eq x last
    if same then dedupLoop inst xs last kept
    else dedupLoop inst xs x (x :: kept)

/-- `retain`: call the closure on each element in order (threading its state); keep the
elements for which it returns `true`. -/
def retainLoop {F : Type u} {T : Type v} (inst : core.ops.function.FnMut F T Bool) :
    F → List T → Result (List T)
  | _, [] => ok []
  | f, x :: xs => do
    let (b, f) ← inst.call_mut f x
    let rest ← retainLoop inst f xs
    ok (if b then x :: rest else rest)

end ClifvModels.Smallvec

open ClifvModels.Smallvec

/-- [smallvec::{smallvec::Array<[@T; N], @T>}::size]: `N`. -/
def ArrayT1.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 1#usize
def ArrayT2.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 2#usize
def ArrayT4.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 4#usize
def ArrayT8.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 8#usize
def ArrayT16.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 16#usize
def ArrayT32.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 32#usize
def ArrayT64.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 64#usize
def ArrayT128.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 128#usize
def ArrayT1024.Insts.SmallvecArray.size (T : Type _) : Result Std.Usize := ok 1024#usize

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::new]: empty. -/
def smallvec.SmallVec.new
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  Result (smallvec.SmallVec A Clause0_Item) :=
  ok ⟨alloc.vec.Vec.new Clause0_Item⟩

/-- [smallvec::{core::default::Default<smallvec::SmallVec<@A, @Clause0_Item>>}::default]:
`SmallVec::new()`. -/
def smallvec.SmallVec.Insts.CoreDefaultDefault.default
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  Result (smallvec.SmallVec A Clause0_Item) :=
  smallvec.SmallVec.new ArrayInst

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::inline_size]: `A::size()`. -/
def smallvec.SmallVec.inline_size
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result Std.Usize :=
  fun _ => ArrayInst.size

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::len] -/
def smallvec.SmallVec.len
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result Std.Usize :=
  fun v => ok (alloc.vec.Vec.len v.vec)

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::is_empty]: `len() == 0`. -/
def smallvec.SmallVec.is_empty
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result Bool :=
  fun v => ok v.vec.val.isEmpty

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::push]: append (panics with "capacity
overflow" past `usize::MAX` elements). -/
def smallvec.SmallVec.push
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Clause0_Item → Result
    (smallvec.SmallVec A Clause0_Item) :=
  fun v x => ofList (v.vec.val ++ [x])

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::pop]: remove the last element. -/
def smallvec.SmallVec.pop
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result ((Option Clause0_Item) ×
    (smallvec.SmallVec A Clause0_Item)) :=
  fun v => do
    let l := v.vec.val
    match l.getLast? with
    | none => ok (none, v)
    | some x => do
      let v' ← ofList l.dropLast
      ok (some x, v')

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::truncate]: keep the first `len`
elements (no effect if `len >= self.len()`). -/
def smallvec.SmallVec.truncate
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Std.Usize → Result (smallvec.SmallVec
    A Clause0_Item) :=
  fun v n => ofList (v.vec.val.take n.val)

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::clear]: `truncate(0)`. -/
def smallvec.SmallVec.clear
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result (smallvec.SmallVec A
    Clause0_Item) :=
  fun _ => smallvec.SmallVec.new ArrayInst

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::resize]: if `len > old_len`,
`extend(repeat(value).take(len - old_len))` (`len - old_len` clones of `value`); else
`truncate(len)`. -/
def smallvec.SmallVec.resize
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) (corecloneCloneInst : core.clone.Clone Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Std.Usize → Clause0_Item → Result
    (smallvec.SmallVec A Clause0_Item) :=
  fun v n x => do
    let l := v.vec.val
    if n.val > l.length then
      let ys ← cloneN corecloneCloneInst x (n.val - l.length)
      ofList (l ++ ys)
    else ofList (l.take n.val)

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::extend_from_slice]: append a copy of
the slice (`insert_from_slice(len, slice)`). -/
def smallvec.SmallVec.extend_from_slice
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) (coremarkerCopyInst : core.marker.Copy Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Slice Clause0_Item → Result
    (smallvec.SmallVec A Clause0_Item) :=
  fun v s => ofList (v.vec.val ++ s.val)

/-- [smallvec::{core::convert::From<smallvec::SmallVec<@A, @Clause0_Item>, &'a [@Clause0_Item]>}::from]:
`slice.iter().cloned().collect()`: a clone of each element, in order. -/
def smallvec.SmallVec.Insts.CoreConvertFromSharedASlice.from
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) (corecloneCloneInst : core.clone.Clone Clause0_Item) :
  Slice Clause0_Item → Result (smallvec.SmallVec A Clause0_Item) :=
  fun s => do
    let l ← cloneList corecloneCloneInst s.val
    ofList l

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::from_vec]: the vector's elements. -/
def smallvec.SmallVec.from_vec
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  alloc.vec.Vec Clause0_Item → Result (smallvec.SmallVec A Clause0_Item) :=
  fun v => ok ⟨v⟩

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::from_elem]: if `n > A::size()`,
`vec![elem; n].into()` (`n - 1` clones followed by `elem` itself); else `n` clones of `elem`. -/
def smallvec.SmallVec.from_elem
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) (corecloneCloneInst : core.clone.Clone Clause0_Item) :
  Clause0_Item → Std.Usize → Result (smallvec.SmallVec A Clause0_Item) :=
  fun x n => do
    let cap ← ArrayInst.size
    if n.val > cap.val then
      let ys ← cloneN corecloneCloneInst x (n.val - 1)
      ofList (ys ++ [x])
    else
      let l ← cloneN corecloneCloneInst x n.val
      ofList l

/-- [smallvec::{core::ops::deref::Deref<smallvec::SmallVec<@A, @Clause0_Item>, [@Clause0_Item]>}::deref] -/
def smallvec.SmallVec.Insts.CoreOpsDerefDerefSlice.deref
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result (Slice Clause0_Item) :=
  fun v => ok v.vec.slice

/-- [smallvec::{core::ops::deref::DerefMut<smallvec::SmallVec<@A, @Clause0_Item>, [@Clause0_Item]>}::deref_mut] -/
def smallvec.SmallVec.Insts.CoreOpsDerefDerefMutSlice.deref_mut
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result ((Slice Clause0_Item) × (Slice
    Clause0_Item → smallvec.SmallVec A Clause0_Item)) :=
  fun v => ok (v.vec.slice, fun s => ⟨{ slice := s }⟩)

/-- [smallvec::{core::ops::index::Index<smallvec::SmallVec<@A, @Clause0_Item>, @I, @Clause1_Output>}::index]:
`&(**self)[index]`. -/
def smallvec.SmallVec.Insts.CoreOpsIndexIndex.index
  {A : Type _} {I : Type _} {Clause0_Item : Type _} {Clause1_Output : Type _}
  (ArrayInst : smallvec.Array A Clause0_Item)
  (coresliceindexSliceIndexISliceClause1_OutputInst :
  core.slice.index.SliceIndex I (Slice Clause0_Item) Clause1_Output) :
  smallvec.SmallVec A Clause0_Item → I → Result Clause1_Output :=
  fun v i => coresliceindexSliceIndexISliceClause1_OutputInst.index i v.vec.slice

/-- [smallvec::{core::ops::index::IndexMut<smallvec::SmallVec<@A, @Clause0_Item>, @I, @Clause1_Output>}::index_mut]:
`&mut (&mut **self)[index]`. -/
def smallvec.SmallVec.Insts.CoreOpsIndexIndexMut.index_mut
  {A : Type _} {I : Type _} {Clause0_Item : Type _} {Clause1_Output : Type _}
  (ArrayInst : smallvec.Array A Clause0_Item)
  (coresliceindexSliceIndexISliceClause1_OutputInst :
  core.slice.index.SliceIndex I (Slice Clause0_Item) Clause1_Output) :
  smallvec.SmallVec A Clause0_Item → I → Result (Clause1_Output ×
    (Clause1_Output → smallvec.SmallVec A Clause0_Item)) :=
  fun v i => do
    let (o, back) ← coresliceindexSliceIndexISliceClause1_OutputInst.index_mut i v.vec.slice
    ok (o, fun o' => ⟨{ slice := back o' }⟩)

/-- [smallvec::{core::clone::Clone<smallvec::SmallVec<@A, @Clause0_Item>>}::clone]:
`SmallVec::from(self.as_slice())`. -/
def smallvec.SmallVec.Insts.CoreCloneClone.clone
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) (corecloneCloneInst : core.clone.Clone Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result (smallvec.SmallVec A
    Clause0_Item) :=
  fun v => smallvec.SmallVec.Insts.CoreConvertFromSharedASlice.from ArrayInst
    corecloneCloneInst v.vec.slice

/-- [smallvec::{core::iter::traits::collect::Extend<smallvec::SmallVec<@A, @Clause0_Item>, @Clause0_Item>}::extend]:
`into_iter()`, then append every item yielded by `next()` until `None`. -/
def smallvec.SmallVec.Insts.CoreIterTraitsCollectExtend.extend
  {A : Type _} {I : Type _} {Clause0_Item : Type _} {Clause1_IntoIter : Type _}
  (ArrayInst : smallvec.Array A Clause0_Item)
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause1_IntoIter) :
  smallvec.SmallVec A Clause0_Item → I → Result (smallvec.SmallVec A
    Clause0_Item) :=
  fun v i => do
    let it ← coreitertraitscollectIntoIteratorInst.into_iter i
    let (lower, _) ← coreitertraitscollectIntoIteratorInst.iteratorInst.size_hint it
    if v.vec.val.length + lower.val > Usize.max then fail .panic
    else
      let xs ← collect coreitertraitscollectIntoIteratorInst.iteratorInst it []
      ofList (v.vec.val ++ xs)

/-- [smallvec::{core::iter::traits::collect::FromIterator<smallvec::SmallVec<@A, @Clause0_Item>, @Clause0_Item>}::from_iter]:
`let mut v = SmallVec::new(); v.extend(iterable); v`. -/
def smallvec.SmallVec.Insts.CoreIterTraitsCollectFromIterator.from_iter
  {A : Type _} {I : Type _} {Clause0_Item : Type _} {Clause1_IntoIter : Type _}
  (ArrayInst : smallvec.Array A Clause0_Item)
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause1_IntoIter) :
  I → Result (smallvec.SmallVec A Clause0_Item) :=
  fun i => do
    let v ← smallvec.SmallVec.new ArrayInst
    smallvec.SmallVec.Insts.CoreIterTraitsCollectExtend.extend ArrayInst
      coreitertraitscollectIntoIteratorInst v i

/-- [smallvec::{core::fmt::Debug<smallvec::SmallVec<@A, @Clause0_Item>>}::fmt]:
`f.debug_list().entries(self.iter()).finish()`. -/
def smallvec.SmallVec.Insts.CoreFmtDebug.fmt
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) (corefmtDebugInst : core.fmt.Debug Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun v f => debugEntries corefmtDebugInst v.vec.val f

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::dedup]: `dedup_by(|a, b| a == b)`, where
`a` is the current element and `b` the last kept one. -/
def smallvec.SmallVec.dedup
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) (corecmpPartialEqInst : core.cmp.PartialEq Clause0_Item
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result (smallvec.SmallVec A
    Clause0_Item) :=
  fun v => do
    match v.vec.val with
    | [] => ok v
    | x :: xs => do
      let l ← dedupLoop corecmpPartialEqInst xs x [x]
      ofList l

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::retain]: call `f` on each element in
order; keep those for which it returns `true` (order preserved). The closure takes
`&mut A::Item`; its write-back is not part of the extracted closure signature. -/
def smallvec.SmallVec.retain
  {A : Type _} {F : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array
  A Clause0_Item) (coreopsfunctionFnMutFTupleMut0Clause0_ItemBoolInst :
  core.ops.function.FnMut F Clause0_Item Bool) :
  smallvec.SmallVec A Clause0_Item → F → Result (smallvec.SmallVec A
    Clause0_Item) :=
  fun v f => do
    let l ← retainLoop coreopsfunctionFnMutFTupleMut0Clause0_ItemBoolInst f v.vec.val
    ofList l

/-- [smallvec::{smallvec::SmallVec<@A, @Clause0_Item>}::drain]: the `Drain` over
`self[start..end]` and the vector with that range removed (see `drainRange` for the panics). -/
def smallvec.SmallVec.drain
  {A : Type _} {R : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array
  A Clause0_Item) (coreopsrangeRangeBoundsRUsizeInst :
  core.ops.range.RangeBounds R Std.Usize) :
  smallvec.SmallVec A Clause0_Item → R → Result ((smallvec.Drain A
    Clause0_Item) × (smallvec.SmallVec A Clause0_Item)) :=
  fun v r => do
    let l := v.vec.val
    let (start, stop) ← drainRange coreopsrangeRangeBoundsRUsizeInst r l.length
    let rest ← ofList (l.take start ++ l.drop stop)
    ok (⟨(l.drop start).take (stop - start)⟩, rest)

/-- [smallvec::{core::iter::traits::iterator::Iterator<smallvec::Drain<'a, @T, @Clause0_Item>, @Clause0_Item>}::next] -/
def smallvec.Drain.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array T
  Clause0_Item) :
  smallvec.Drain T Clause0_Item → Result ((Option Clause0_Item) ×
    (smallvec.Drain T Clause0_Item)) :=
  fun d => match d.items with
    | [] => ok (none, d)
    | x :: xs => ok (some x, ⟨xs⟩)

/-- [smallvec::{core::iter::traits::collect::IntoIterator<smallvec::SmallVec<@A, @Clause0_Item>, @Clause0_Item, smallvec::IntoIter<@A, @Clause0_Item>>}::into_iter] -/
def smallvec.SmallVec.Insts.CoreIterTraitsCollectIntoIteratorClause0_ItemIntoIter.into_iter
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result (smallvec.IntoIter A
    Clause0_Item) :=
  fun v => ok ⟨v.vec.val⟩

/-- [smallvec::{core::iter::traits::iterator::Iterator<smallvec::IntoIter<@A, @Clause0_Item>, @Clause0_Item>}::next] -/
def smallvec.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.IntoIter A Clause0_Item → Result ((Option Clause0_Item) ×
    (smallvec.IntoIter A Clause0_Item)) :=
  fun it => match it.items with
    | [] => ok (none, it)
    | x :: xs => ok (some x, ⟨xs⟩)

/-- [smallvec::{core::iter::traits::double_ended::DoubleEndedIterator<smallvec::IntoIter<@A, @Clause0_Item>, @Clause0_Item>}::next_back] -/
def smallvec.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.IntoIter A Clause0_Item → Result ((Option Clause0_Item) ×
    (smallvec.IntoIter A Clause0_Item)) :=
  fun it => match it.items.getLast? with
    | none => ok (none, it)
    | some x => ok (some x, ⟨it.items.dropLast⟩)

/-- [smallvec::{core::iter::traits::iterator::Iterator<smallvec::IntoIter<@A, @Clause0_Item>, @Clause0_Item>}::size_hint]:
`(end - current, Some(end - current))`. -/
def smallvec.IntoIter.Insts.CoreIterTraitsIteratorIterator.size_hint
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.IntoIter A Clause0_Item → Result (Std.Usize × (Option Std.Usize)) :=
  fun it =>
    if h : it.items.length < 2 ^ UScalarTy.Usize.numBits then
      let n := Usize.ofNatCore it.items.length h
      ok (n, some n)
    else fail .panic

/-- [smallvec::{core::iter::traits::collect::IntoIterator<&'a smallvec::SmallVec<@A, @Clause0_Item>, &'a @Clause0_Item, core::slice::iter::Iter<'a, @Clause0_Item>>}::into_iter]:
`self.iter()`. -/
def SharedASmallVec.Insts.CoreIterTraitsCollectIntoIteratorSharedAClause0_ItemIter.into_iter
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result (core.slice.iter.Iter
    Clause0_Item) :=
  fun v => core.slice.Slice.iter v.vec.slice

/-- [smallvec::{core::iter::traits::collect::IntoIterator<&'a mut smallvec::SmallVec<@A, @Clause0_Item>, &'a mut @Clause0_Item, core::slice::iter::IterMut<'a, @Clause0_Item>>}::into_iter]:
`self.iter_mut()`. -/
def MutASmallVec.Insts.CoreIterTraitsCollectIntoIteratorMutAClause0_ItemIterMut.into_iter
  {A : Type _} {Clause0_Item : Type _} (ArrayInst : smallvec.Array A
  Clause0_Item) :
  smallvec.SmallVec A Clause0_Item → Result ((core.slice.iter.IterMut
    Clause0_Item) × (core.slice.iter.IterMut Clause0_Item →
    smallvec.SmallVec A Clause0_Item)) :=
  fun v => do
    let (it, back) ← core.slice.Slice.iter_mut v.vec.slice
    ok (it, fun it' => ⟨{ slice := back it' }⟩)

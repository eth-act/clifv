/-
Handwritten executable models of the `allocator-api2` 0.2.20 functions used by the extracted code,
transcribed from `allocator-api2-0.2.20/src/stable/vec/{mod,drain,into_iter}.rs`.

A `Vec<T, A>` is modeled by its element sequence and its allocator
(`ClifvModels.Types.AllocatorApi2`). As in the Aeneas `alloc.vec.Vec` model, a vector's buffer is
not modeled: the allocator's methods are never called by the `Vec` operations (natively they only
obtain/release memory, whose failure is an abort through `handle_alloc_error`, or a "capacity
overflow" panic when the byte size exceeds `isize::MAX`; neither is modeled). Every operation
returns the native element sequence, calls the trait methods of its arguments (`Clone::clone`,
the closure, `Iterator::next`, `RangeBounds`) in the native order and number, and panics under
the native panic conditions (index/range checks; more than `usize::MAX` elements).

The `Allocator` provided methods (`allocate_zeroed`, `grow`, `grow_zeroed`, `shrink`) are
transcribed over the Aeneas library's value-based pointer model (`NonNull<T>` carries the
pointee): a memory block `NonNull<[u8]>` carries its bytes, while a `NonNull<u8>` block start
carries only its first byte, so `copy_nonoverlapping` from it can copy only that byte.
-/
module
public import Aeneas
public import ClifvGen.Types
public import ClifvModels.Funs.Smallvec
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
universe u v
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.AllocatorApi2

/-- The vector with elements `l` and allocator `a` (panics past `usize::MAX` elements). -/
def ofList {T : Type u} {A : Type v} (l : List T) (a : A) :
    Result (allocator_api2.stable.vec.Vec T A) := do
  let v ← ClifvModels.Smallvec.vecOfList l
  ok ⟨v, a⟩

/-- `Vec::retain`: `f(&elem)` on each element in order (threading the closure state); keep the
elements for which it returns `true`. -/
def retainLoop {F : Type u} {T : Type v} (inst : core.ops.function.FnMut F T Bool) :
    F → List T → Result (List T)
  | _, [] => ok []
  | f, x :: xs => do
    let (b, f) ← inst.call_mut f x
    let rest ← retainLoop inst f xs
    ok (if b then x :: rest else rest)

def usizeOfLen (n : Nat) : Result Std.Usize :=
  if h : n < 2 ^ UScalarTy.Usize.numBits then ok (Usize.ofNatCore n h) else fail .panic

/-- A block of `n` zero bytes. -/
def zeroBlock (n : Nat) : Result (core.ptr.non_null.NonNull (Slice Std.U8)) := do
  let v ← ClifvModels.Smallvec.vecOfList (List.replicate n (0#u8))
  ok ⟨⟨v.slice⟩⟩

/-- `ptr::copy_nonoverlapping(src, dst, n)` in the value pointer model: the source `NonNull<u8>`
carries only its first byte, which is copied when `n > 0`. -/
def copyFirst (src : core.ptr.non_null.NonNull Std.U8) (n : Nat)
    (dst : core.ptr.non_null.NonNull (Slice Std.U8)) :
    Result (core.ptr.non_null.NonNull (Slice Std.U8)) := do
  let bytes := Slice.val dst.pointer.v
  if n > 0 ∧ bytes.length > 0 then
    let v ← ClifvModels.Smallvec.vecOfList (bytes.set 0 src.pointer.v)
    ok ⟨⟨v.slice⟩⟩
  else ok dst

end ClifvModels.AllocatorApi2

open ClifvModels.AllocatorApi2

/-- [allocator_api2::stable::alloc::Allocator::allocate_zeroed]: `self.allocate(layout)?`, then
zero the `ptr.len()` bytes of the block. -/
@[trait_default]
def allocator_api2.stable.alloc.Allocator.allocate_zeroed.default
  {Self : Type _} (AllocatorInst : allocator_api2.stable.alloc.Allocator Self)
  :
  Self → core.alloc.layout.Layout → Result (core.result.Result
    (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun self layout => do
    let r ← AllocatorInst.allocate self layout
    match r with
    | .Err e => ok (.Err e)
    | .Ok p => do
      let z ← zeroBlock (Slice.val p.pointer.v).length
      ok (.Ok z)

/-- [allocator_api2::stable::alloc::Allocator::grow]: `self.allocate(new_layout)?`, copy
`old_layout.size()` bytes from `ptr`, `self.deallocate(ptr, old_layout)`. -/
@[trait_default]
def allocator_api2.stable.alloc.Allocator.grow.default
  {Self : Type _} (AllocatorInst : allocator_api2.stable.alloc.Allocator Self)
  :
  Self → core.ptr.non_null.NonNull Std.U8 → core.alloc.layout.Layout →
    core.alloc.layout.Layout → Result (core.result.Result
    (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun self ptr old new => do
    let r ← AllocatorInst.allocate self new
    match r with
    | .Err e => ok (.Err e)
    | .Ok p =>
      let p ← copyFirst ptr old.size.val p
      AllocatorInst.deallocate self ptr old
      ok (.Ok p)

/-- [allocator_api2::stable::alloc::Allocator::grow_zeroed]: as `grow`, with
`self.allocate_zeroed(new_layout)?`. -/
@[trait_default]
def allocator_api2.stable.alloc.Allocator.grow_zeroed.default
  {Self : Type _} (AllocatorInst : allocator_api2.stable.alloc.Allocator Self)
  :
  Self → core.ptr.non_null.NonNull Std.U8 → core.alloc.layout.Layout →
    core.alloc.layout.Layout → Result (core.result.Result
    (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun self ptr old new => do
    let r ← AllocatorInst.allocate_zeroed self new
    match r with
    | .Err e => ok (.Err e)
    | .Ok p =>
      let p ← copyFirst ptr old.size.val p
      AllocatorInst.deallocate self ptr old
      ok (.Ok p)

/-- [allocator_api2::stable::alloc::Allocator::shrink]: `self.allocate(new_layout)?`, copy
`new_layout.size()` bytes from `ptr`, `self.deallocate(ptr, old_layout)`. -/
@[trait_default]
def allocator_api2.stable.alloc.Allocator.shrink.default
  {Self : Type _} (AllocatorInst : allocator_api2.stable.alloc.Allocator Self)
  :
  Self → core.ptr.non_null.NonNull Std.U8 → core.alloc.layout.Layout →
    core.alloc.layout.Layout → Result (core.result.Result
    (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun self ptr old new => do
    let r ← AllocatorInst.allocate self new
    match r with
    | .Err e => ok (.Err e)
    | .Ok p =>
      let p ← copyFirst ptr new.size.val p
      AllocatorInst.deallocate self ptr old
      ok (.Ok p)

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::new_in]: empty. -/
def allocator_api2.stable.vec.Vec.new_in
  (T : Type _) {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  A → Result (allocator_api2.stable.vec.Vec T A) :=
  fun a => ok ⟨alloc.vec.Vec.new T, a⟩

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::shrink_to_fit]:
only the capacity changes. -/
def allocator_api2.stable.vec.Vec.shrink_to_fit
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result (allocator_api2.stable.vec.Vec T
    A) :=
  fun v => ok v

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::truncate]: keep the
first `len` elements (no effect if `len > self.len`). -/
def allocator_api2.stable.vec.Vec.truncate
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Std.Usize → Result
    (allocator_api2.stable.vec.Vec T A) :=
  fun v n => ofList (v.vec.val.take n.val) v.alloc

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::insert]: panics
("insertion index (is {index}) should be <= len (is {len})") if `index > len`. -/
def allocator_api2.stable.vec.Vec.insert
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Std.Usize → T → Result
    (allocator_api2.stable.vec.Vec T A) :=
  fun v i x =>
    let l := v.vec.val
    if i.val ≤ l.length then ofList (l.take i.val ++ x :: l.drop i.val) v.alloc
    else fail .panic

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::retain]:
`retain_mut(|elem| f(elem))`: `f` is called once per element, in order. -/
def allocator_api2.stable.vec.Vec.retain
  {T : Type _} {A : Type _} {F : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A)
  (coreopsfunctionFnMutFTupleShared0TBoolInst : core.ops.function.FnMut F T
  Bool) :
  allocator_api2.stable.vec.Vec T A → F → Result
    (allocator_api2.stable.vec.Vec T A) :=
  fun v f => do
    let l ← retainLoop coreopsfunctionFnMutFTupleShared0TBoolInst f v.vec.val
    ofList l v.alloc

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::push] -/
def allocator_api2.stable.vec.Vec.push
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → T → Result
    (allocator_api2.stable.vec.Vec T A) :=
  fun v x => ofList (v.vec.val ++ [x]) v.alloc

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::pop] -/
def allocator_api2.stable.vec.Vec.pop
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result ((Option T) ×
    (allocator_api2.stable.vec.Vec T A)) :=
  fun v => do
    let l := v.vec.val
    match l.getLast? with
    | none => ok (none, v)
    | some x => do
      let v' ← ofList l.dropLast v.alloc
      ok (some x, v')

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::drain]: the range
check of `&self.as_slice()[(start_bound, end_bound)]` (panics as `SmallVec::drain`), then the
`Drain` over `self[start..end]` and the vector with that range removed. -/
def allocator_api2.stable.vec.Vec.drain
  {T : Type _} {A : Type _} {R : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) (coreopsrangeRangeBoundsRUsizeInst :
  core.ops.range.RangeBounds R Std.Usize) :
  allocator_api2.stable.vec.Vec T A → R → Result
    ((allocator_api2.stable.vec.drain.Drain T A) ×
    (allocator_api2.stable.vec.Vec T A)) :=
  fun v r => do
    let l := v.vec.val
    let (start, stop) ← ClifvModels.Smallvec.drainRange coreopsrangeRangeBoundsRUsizeInst r
      l.length
    let rest ← ofList (l.take start ++ l.drop stop) v.alloc
    ok (⟨(l.drop start).take (stop - start)⟩, rest)

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::len] -/
def allocator_api2.stable.vec.Vec.len
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result Std.Usize :=
  fun v => ok (alloc.vec.Vec.len v.vec)

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::is_empty] -/
def allocator_api2.stable.vec.Vec.is_empty
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result Bool :=
  fun v => ok v.vec.val.isEmpty

/-- [allocator_api2::stable::vec::{allocator_api2::stable::vec::Vec<@T, @A>}::extend_from_slice]:
`self.extend(other.iter().cloned())`: a clone of each element, in order. -/
def allocator_api2.stable.vec.Vec.extend_from_slice
  {T : Type _} {A : Type _} (corecloneCloneInst : core.clone.Clone T)
  (allocAllocatorInst : allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Slice T → Result
    (allocator_api2.stable.vec.Vec T A) :=
  fun v s => do
    let ys ← ClifvModels.Smallvec.cloneList corecloneCloneInst s.val
    ofList (v.vec.val ++ ys) v.alloc

/-- [allocator_api2::stable::vec::{core::ops::deref::Deref<allocator_api2::stable::vec::Vec<@T, @A>, [@T]>}::deref] -/
def allocator_api2.stable.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result (Slice T) :=
  fun v => ok v.vec.slice

/-- [allocator_api2::stable::vec::{core::ops::deref::DerefMut<allocator_api2::stable::vec::Vec<@T, @A>, [@T]>}::deref_mut] -/
def allocator_api2.stable.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result ((Slice T) × (Slice T →
    allocator_api2.stable.vec.Vec T A)) :=
  fun v => ok (v.vec.slice, fun s => ⟨{ slice := s }, v.alloc⟩)

/-- [allocator_api2::stable::vec::{core::clone::Clone<allocator_api2::stable::vec::Vec<@T, @A>>}::clone]:
`let alloc = self.allocator().clone(); Vec::with_capacity_in(len, alloc)` then
`extend_from_slice(self)`: the allocator is cloned first, then each element in order. -/
def allocator_api2.stable.vec.Vec.Insts.CoreCloneClone.clone
  {T : Type _} {A : Type _} (corecloneCloneInst : core.clone.Clone T)
  (allocAllocatorInst : allocator_api2.stable.alloc.Allocator A)
  (corecloneCloneInst1 : core.clone.Clone A) :
  allocator_api2.stable.vec.Vec T A → Result (allocator_api2.stable.vec.Vec T
    A) :=
  fun v => do
    let a ← corecloneCloneInst1.clone v.alloc
    let ys ← ClifvModels.Smallvec.cloneList corecloneCloneInst v.vec.val
    ofList ys a

/-- [allocator_api2::stable::vec::{core::ops::index::Index<allocator_api2::stable::vec::Vec<@T, @A>, @I, @Clause0_Output>}::index]:
`Index::index(&**self, index)`. -/
def allocator_api2.stable.vec.Vec.Insts.CoreOpsIndexIndex.index
  {T : Type _} {I : Type _} {A : Type _} {Clause0_Output : Type _}
  (coresliceindexSliceIndexISliceClause0_OutputInst :
  core.slice.index.SliceIndex I (Slice T) Clause0_Output) (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → I → Result Clause0_Output :=
  fun v i => coresliceindexSliceIndexISliceClause0_OutputInst.index i v.vec.slice

/-- [allocator_api2::stable::vec::{core::ops::index::IndexMut<allocator_api2::stable::vec::Vec<@T, @A>, @I, @Clause0_Output>}::index_mut]:
`IndexMut::index_mut(&mut **self, index)`. -/
def allocator_api2.stable.vec.Vec.Insts.CoreOpsIndexIndexMut.index_mut
  {T : Type _} {I : Type _} {A : Type _} {Clause0_Output : Type _}
  (coresliceindexSliceIndexISliceClause0_OutputInst :
  core.slice.index.SliceIndex I (Slice T) Clause0_Output) (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → I → Result (Clause0_Output ×
    (Clause0_Output → allocator_api2.stable.vec.Vec T A)) :=
  fun v i => do
    let (o, back) ← coresliceindexSliceIndexISliceClause0_OutputInst.index_mut i v.vec.slice
    ok (o, fun o' => ⟨{ slice := back o' }, v.alloc⟩)

/-- [allocator_api2::stable::vec::{core::iter::traits::collect::IntoIterator<allocator_api2::stable::vec::Vec<@T, @A>, @T, allocator_api2::stable::vec::into_iter::IntoIter<@T, @A>>}::into_iter] -/
def allocator_api2.stable.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result
    (allocator_api2.stable.vec.into_iter.IntoIter T A) :=
  fun v => ok ⟨v.vec.val⟩

/-- [allocator_api2::stable::vec::{core::iter::traits::collect::IntoIterator<&'a allocator_api2::stable::vec::Vec<@T, @A>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter]:
`self.iter()`. -/
def allocator_api2.stable.vec.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result (core.slice.iter.Iter T) :=
  fun v => core.slice.Slice.iter v.vec.slice

/-- [allocator_api2::stable::vec::{core::iter::traits::collect::IntoIterator<&'a mut allocator_api2::stable::vec::Vec<@T, @A>, &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter]:
`self.iter_mut()`. -/
def allocator_api2.stable.vec.MutAVec.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → Result ((core.slice.iter.IterMut T) ×
    (core.slice.iter.IterMut T → allocator_api2.stable.vec.Vec T A)) :=
  fun v => do
    let (it, back) ← core.slice.Slice.iter_mut v.vec.slice
    ok (it, fun it' => ⟨{ slice := back it' }, v.alloc⟩)

/-- [allocator_api2::stable::vec::{core::iter::traits::collect::Extend<allocator_api2::stable::vec::Vec<@T, @A>, @T>}::extend]:
`into_iter()`, then push every item yielded by `next()` until `None`. -/
def allocator_api2.stable.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend
  {T : Type _} {A : Type _} {I : Type _} {Clause1_IntoIter : Type _}
  (allocAllocatorInst : allocator_api2.stable.alloc.Allocator A)
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I T Clause1_IntoIter) :
  allocator_api2.stable.vec.Vec T A → I → Result
    (allocator_api2.stable.vec.Vec T A) :=
  fun v i => do
    let it ← coreitertraitscollectIntoIteratorInst.into_iter i
    let xs ← ClifvModels.Smallvec.collect coreitertraitscollectIntoIteratorInst.iteratorInst it []
    ofList (v.vec.val ++ xs) v.alloc

/-- [allocator_api2::stable::vec::{core::fmt::Debug<allocator_api2::stable::vec::Vec<@T, @A>>}::fmt]:
`fmt::Debug::fmt(&**self, f)` (a debug list of the elements). -/
def allocator_api2.stable.vec.Vec.Insts.CoreFmtDebug.fmt
  {T : Type _} {A : Type _} (corefmtDebugInst : core.fmt.Debug T)
  (allocAllocatorInst : allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.Vec T A → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun v f => ClifvModels.Smallvec.debugEntries corefmtDebugInst v.vec.val f

/-- [allocator_api2::stable::vec::into_iter::{core::iter::traits::iterator::Iterator<allocator_api2::stable::vec::into_iter::IntoIter<@T, @A>, @T>}::next] -/
def allocator_api2.stable.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.into_iter.IntoIter T A → Result ((Option T) ×
    (allocator_api2.stable.vec.into_iter.IntoIter T A)) :=
  fun it => match it.items with
    | [] => ok (none, it)
    | x :: xs => ok (some x, ⟨xs⟩)

/-- [allocator_api2::stable::vec::drain::{core::iter::traits::iterator::Iterator<allocator_api2::stable::vec::drain::Drain<'0, @T, @A>, @T>}::next] -/
def allocator_api2.stable.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.drain.Drain T A → Result ((Option T) ×
    (allocator_api2.stable.vec.drain.Drain T A)) :=
  fun d => match d.items with
    | [] => ok (none, d)
    | x :: xs => ok (some x, ⟨xs⟩)

/-- [allocator_api2::stable::vec::drain::{core::iter::traits::iterator::Iterator<allocator_api2::stable::vec::drain::Drain<'0, @T, @A>, @T>}::size_hint]:
`self.iter.size_hint()` (exact). -/
def allocator_api2.stable.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.size_hint
  {T : Type _} {A : Type _} (allocAllocatorInst :
  allocator_api2.stable.alloc.Allocator A) :
  allocator_api2.stable.vec.drain.Drain T A → Result (Std.Usize × (Option
    Std.Usize)) :=
  fun d => do
    let n ← usizeOfLen d.items.length
    ok (n, some n)

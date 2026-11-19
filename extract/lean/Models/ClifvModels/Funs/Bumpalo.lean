/-
Handwritten executable models of the `bumpalo` 3.20.2 functions used by the extracted code,
transcribed from `bumpalo-3.20.2/src/lib.rs`.

Arena memory is not modeled (`ClifvModels.Types.Bumpalo`): an arena allocation returns its
contents as a value, and the returned borrow's write-back is dropped (the arena never reads its
allocations). Allocation failure (natively an abort through `oom()`/`handle_alloc_error`, an
`Err(AllocError)` from the `Allocator` methods, or a panic when the byte size overflows) is not
modeled.

The `allocator_api2::Allocator` impl of `&Bump` is over the Aeneas library's value-based pointer
model (`NonNull<T>` carries the pointee): a returned block `NonNull<[u8]>` carries
`layout.size()` bytes (zero: fresh arena memory is unobservable before it is written), and a
block start `NonNull<u8>` carries only its first byte (copied by `grow`/`shrink`).
-/
module
public import Aeneas
public import ClifvGen.Types
public import ClifvModels.Funs.Smallvec
public import ClifvModels.Funs.AllocatorApi2
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
universe u v
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.Bumpalo

/-- `n` calls of `iter.next().expect("Iterator supplied too few elements")`. -/
def pullN {It : Type u} {Item : Type v} (inst : core.iter.traits.iterator.Iterator It Item)
    (it : It) : Nat → Result (List Item)
  | 0 => ok []
  | n + 1 => do
    let (o, it) ← inst.next it
    match o with
    | none => fail .panic
    | some x => do
      let xs ← pullN inst it n
      ok (x :: xs)

/-- `Bump::grow`/`Bump::shrink` (in place or by copy): a block of `new_size` bytes starting with
the first `min(old, new)` bytes of `ptr`. -/
def realloc (ptr : core.ptr.non_null.NonNull Std.U8) (copied : Nat) (newSize : Nat) :
    Result (core.result.Result (core.ptr.non_null.NonNull (Slice Std.U8))
      allocator_api2.stable.alloc.AllocError) := do
  let b ← ClifvModels.AllocatorApi2.zeroBlock newSize
  let c ← ClifvModels.AllocatorApi2.copyFirst ptr copied b
  ok (.Ok c)

end ClifvModels.Bumpalo

/-- [bumpalo::{core::default::Default<bumpalo::Bump<@MIN_ALIGN>>}::default]: `Bump::with_min_align()`
(its `MIN_ALIGN` assertions hold for the only instantiation, `MIN_ALIGN = 1`). -/
def bumpalo.Bump.Insts.CoreDefaultDefault.default
  (MIN_ALIGN : Std.Usize) : Result (bumpalo.Bump MIN_ALIGN) :=
  if MIN_ALIGN.val ∈ [1, 2, 4, 8, 16] then ok ⟨⟩ else fail .panic

/-- [bumpalo::{bumpalo::Bump<1>}::with_capacity]: a new arena (the initial chunk is not
observable). -/
def bumpalo.Bump1.with_capacity : Std.Usize → Result (bumpalo.Bump 1#usize) :=
  fun _ => ok ⟨⟩

/-- [bumpalo::{bumpalo::Bump<@MIN_ALIGN>}::reset]: frees all allocations (unobservable). -/
def bumpalo.Bump.reset
  {MIN_ALIGN : Std.Usize} :
  bumpalo.Bump MIN_ALIGN → Result (bumpalo.Bump MIN_ALIGN) :=
  fun b => ok b

/-- [bumpalo::{bumpalo::Bump<@MIN_ALIGN>}::alloc_slice_copy]: a copy of `src`. -/
def bumpalo.Bump.alloc_slice_copy
  {T : Type _} {MIN_ALIGN : Std.Usize} (coremarkerCopyInst : core.marker.Copy
  T) :
  bumpalo.Bump MIN_ALIGN → Slice T → Result ((Slice T) × (Slice T →
    Unit)) :=
  fun _ s => ok (s, fun _ => ())

/-- [bumpalo::{bumpalo::Bump<@MIN_ALIGN>}::alloc_slice_fill_iter]: `let mut iter =
iter.into_iter(); self.alloc_slice_fill_with(iter.len(), |_| iter.next().expect(..))`, where
`ExactSizeIterator::len` is the provided `let (lower, upper) = self.size_hint();
assert_eq!(upper, Some(lower)); lower`. -/
def bumpalo.Bump.alloc_slice_fill_iter
  {T : Type _} {I : Type _} {Clause0_IntoIter : Type _} {Clause1_Clause0_Item :
  Type _} {MIN_ALIGN : Std.Usize} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I T Clause0_IntoIter)
  (coreitertraitsexact_sizeExactSizeIteratorInst :
  core.iter.traits.exact_size.ExactSizeIterator Clause0_IntoIter
  Clause1_Clause0_Item) :
  bumpalo.Bump MIN_ALIGN → I → Result ((Slice T) × (Slice T → Unit)) :=
  fun _ i => do
    let it ← coreitertraitscollectIntoIteratorInst.into_iter i
    let (lower, upper) ←
      coreitertraitsexact_sizeExactSizeIteratorInst.iteratorInst.size_hint it
    let exact := match upper with
      | some u => u.val == lower.val
      | none => false
    if !exact then fail .panic
    else
      let xs ← ClifvModels.Bumpalo.pullN coreitertraitscollectIntoIteratorInst.iteratorInst it
        lower.val
      let v ← ClifvModels.Smallvec.vecOfList xs
      ok (v.slice, fun _ => ())

/-- [bumpalo::{allocator_api2::stable::alloc::Allocator<&'a bumpalo::Bump<@MIN_ALIGN>>}::allocate]:
a fresh block of `layout.size()` bytes. -/
def SharedABump.Insts.Allocator_api2StableAllocAllocator.allocate
  {MIN_ALIGN : Std.Usize} :
  bumpalo.Bump MIN_ALIGN → core.alloc.layout.Layout → Result
    (core.result.Result (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun _ layout => do
    let z ← ClifvModels.AllocatorApi2.zeroBlock layout.size.val
    ok (.Ok z)

/-- [bumpalo::{allocator_api2::stable::alloc::Allocator<&'a bumpalo::Bump<@MIN_ALIGN>>}::deallocate]:
`Bump::dealloc` (reclaims the block only if it is the last allocation; unobservable). -/
def SharedABump.Insts.Allocator_api2StableAllocAllocator.deallocate
  {MIN_ALIGN : Std.Usize} :
  bumpalo.Bump MIN_ALIGN → core.ptr.non_null.NonNull Std.U8 →
    core.alloc.layout.Layout → Result Unit :=
  fun _ _ _ => ok ()

/-- [bumpalo::{allocator_api2::stable::alloc::Allocator<&'a bumpalo::Bump<@MIN_ALIGN>>}::shrink]:
`Bump::shrink`: the block, `new_layout.size()` bytes long. -/
def SharedABump.Insts.Allocator_api2StableAllocAllocator.shrink
  {MIN_ALIGN : Std.Usize} :
  bumpalo.Bump MIN_ALIGN → core.ptr.non_null.NonNull Std.U8 →
    core.alloc.layout.Layout → core.alloc.layout.Layout → Result
    (core.result.Result (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun _ ptr _ new => ClifvModels.Bumpalo.realloc ptr new.size.val new.size.val

/-- [bumpalo::{allocator_api2::stable::alloc::Allocator<&'a bumpalo::Bump<@MIN_ALIGN>>}::grow]:
`Bump::grow`: a block of `new_layout.size()` bytes starting with the old contents. -/
def SharedABump.Insts.Allocator_api2StableAllocAllocator.grow
  {MIN_ALIGN : Std.Usize} :
  bumpalo.Bump MIN_ALIGN → core.ptr.non_null.NonNull Std.U8 →
    core.alloc.layout.Layout → core.alloc.layout.Layout → Result
    (core.result.Result (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun _ ptr old new => ClifvModels.Bumpalo.realloc ptr old.size.val new.size.val

/-- [bumpalo::{allocator_api2::stable::alloc::Allocator<&'a bumpalo::Bump<@MIN_ALIGN>>}::grow_zeroed]:
`self.grow(..)?`, then zero the bytes from `old_layout.size()` on (already zero in the model). -/
def SharedABump.Insts.Allocator_api2StableAllocAllocator.grow_zeroed
  {MIN_ALIGN : Std.Usize} :
  bumpalo.Bump MIN_ALIGN → core.ptr.non_null.NonNull Std.U8 →
    core.alloc.layout.Layout → core.alloc.layout.Layout → Result
    (core.result.Result (core.ptr.non_null.NonNull (Slice Std.U8))
    allocator_api2.stable.alloc.AllocError) :=
  fun _ ptr old new => ClifvModels.Bumpalo.realloc ptr old.size.val new.size.val

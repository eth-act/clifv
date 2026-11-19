/-
Handwritten executable models of the `hashbrown` 0.17.0 functions (`hashbrown#2`) used by the
extracted code.

`ClifvModels.Hashbrown.RawTable` is a line-by-line port of `hashbrown-0.17.0/src/raw.rs` for the
native x86_64 build (SSE2 `Group::WIDTH = 16`, `BitMask` stride 1, `usize` = 64 bits, default
features `inline-more`, `allocator-api2`, `equivalent`, `raw-entry`, `default-hasher`):
`h1(hash) = hash`, `Tag::full(hash) = hash >> 57`, triangular `ProbeSeq`, `find_insert_index`
(incl. `fix_insert_index` for small tables), `erase`'s EMPTY/DELETED rule, `capacity_to_buckets`
/ `bucket_mask_to_capacity`, `reserve_rehash` (in-place rehash vs. resize, with the native
element moves), `clear` / `clear_no_drop`, and `RawIter`'s ascending-bucket iteration order.

Element-size dependence: `capacity_to_buckets` picks the minimum capacity for small requests
from `size_of::<T>()` (`T = (K, V)`); every instantiation in the extracted code has
`size_of::<T>() >= 4`, for which the native minimum is 3 (4 buckets). The model fixes that case.
`Layout` overflow (`calculate_layout_for`) and allocation failure are not modeled.

Hashing goes through the generated `BuildHasher`/`Hash`/`Hasher` instances it receives
(`make_hash` = `BuildHasher::hash_one` default: `build_hasher`, `hash`, `finish`).
-/
module
public import Aeneas
public import ClifvGen.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.Hashbrown

/-- `Group::WIDTH` (SSE2). -/
def WIDTH : Nat := 16
/-- `Tag::EMPTY`. -/
def EMPTY : UInt8 := 0xFF
/-- `Tag::DELETED`. -/
def DELETED : UInt8 := 0x80
/-- `usize::MAX + 1` on x86_64. -/
def USIZE_BOUND : Nat := 2 ^ 64

def toUsize (n : Nat) : Std.Usize := ⟨BitVec.ofNat _ n⟩

/-- `Tag::is_full`. -/
@[inline] def isFull (b : UInt8) : Bool := b &&& 0x80 == 0
/-- `Tag::is_special`. -/
@[inline] def isSpecial (b : UInt8) : Bool := b &&& 0x80 != 0
/-- `Tag::full(hash)`: the top 7 bits of the 64-bit hash. -/
@[inline] def tagOf (hash : UInt64) : UInt8 := ((hash >>> 57) &&& 0x7f).toUInt8

/-- `bucket_mask_to_capacity`. -/
def bucketMaskToCapacity (m : Nat) : Nat := if m < 8 then m else ((m + 1) / 8) * 7

/-- `capacity_to_buckets` for `size_of::<T>() >= 4` (`min_cap = 3`). `none`: overflow. -/
def capacityToBuckets (cap : Nat) : Option Nat :=
  if cap < 15 then
    let cap := max 3 cap
    some (if cap < 4 then 4 else if cap < 8 then 8 else 16)
  else if cap * 8 ≥ USIZE_BOUND then none
  else some (cap * 8 / 7).nextPowerOfTwo

/-- Set bits of a 16-bit `BitMask`, lowest first (`BitMaskIter`). -/
def bits (m : Nat) : List Nat := (List.range WIDTH).filter m.testBit
/-- `BitMask::lowest_set_bit`. -/
def lowestSetBit (m : Nat) : Option Nat := (List.range WIDTH).find? m.testBit
/-- `BitMask::trailing_zeros` (16 for the empty mask). -/
def trailingZeros (m : Nat) : Nat := (lowestSetBit m).getD WIDTH
/-- `BitMask::leading_zeros` (`u16::leading_zeros`). -/
def leadingZeros (m : Nat) : Nat :=
  match (List.range WIDTH).reverse.find? m.testBit with
  | some i => WIDTH - 1 - i
  | none => WIDTH

namespace RawTable
variable {T : Type}

/-- `RawTableInner::NEW`: the unallocated empty singleton. -/
def new : RawTable T := ⟨0, Array.replicate (1 + WIDTH) EMPTY, #[none], 0, 0⟩

def numBuckets (t : RawTable T) : Nat := t.bucket_mask + 1

/-- `RawTableInner::new_uninitialized` + `fill_empty`. -/
def withBuckets (buckets : Nat) : RawTable T :=
  ⟨buckets - 1, Array.replicate (buckets + WIDTH) EMPTY, Array.replicate buckets none, 0,
    bucketMaskToCapacity (buckets - 1)⟩

/-- `RawTableInner::with_capacity` (`Fallibility::Infallible`: overflow panics). -/
def withCapacity (cap : Nat) : Result (RawTable T) :=
  if cap = 0 then ok new
  else match capacityToBuckets cap with
    | none => fail .panic
    | some b => ok (withBuckets b)

@[inline] def ctrlAt (t : RawTable T) (i : Nat) : UInt8 := t.ctrl[i]!

/-- The bitmask of the bytes of `Group::load(ctrl(pos))` satisfying `p`. -/
def groupMatch (t : RawTable T) (pos : Nat) (p : UInt8 → Bool) : Nat :=
  (List.range WIDTH).foldl (fun m i => if p (t.ctrlAt (pos + i)) then m ||| (1 <<< i) else m) 0

def matchTag (t : RawTable T) (pos : Nat) (tag : UInt8) : Nat := t.groupMatch pos (· == tag)
def matchEmpty (t : RawTable T) (pos : Nat) : Nat := t.groupMatch pos (· == EMPTY)
def matchEmptyOrDeleted (t : RawTable T) (pos : Nat) : Nat := t.groupMatch pos isSpecial

/-- `(i - WIDTH) & bucket_mask` with wrapping `usize` subtraction. -/
def subWidthMasked (t : RawTable T) (i : Nat) : Nat :=
  (i + t.numBuckets * WIDTH - WIDTH) % t.numBuckets

/-- `RawTableInner::set_ctrl`: write the byte and its replica. -/
def setCtrl (t : RawTable T) (i : Nat) (b : UInt8) : RawTable T :=
  let i2 := t.subWidthMasked i + WIDTH
  { t with ctrl := (t.ctrl.set! i b).set! i2 b }

def setSlot (t : RawTable T) (i : Nat) (v : Option T) : RawTable T :=
  { t with slots := t.slots.set! i v }

def getSlot (t : RawTable T) (i : Nat) : Result T :=
  match t.slots[i]? with
  | some (some v) => ok v
  | _ => fail .panic -- unreachable: FULL control byte without element

/-- `fix_insert_index`. -/
def fixInsertIndex (t : RawTable T) (i : Nat) : Nat :=
  if isFull (t.ctrlAt i) then (lowestSetBit (t.matchEmptyOrDeleted 0)).getD 0 else i

/-- `find_insert_index_in_group`. -/
def findInsertIndexInGroup (t : RawTable T) (pos : Nat) : Option Nat :=
  (lowestSetBit (t.matchEmptyOrDeleted pos)).map fun bit => (pos + bit) &&& t.bucket_mask

/-- `ProbeSeq::move_next`: `(pos, stride)` ↦ next. -/
@[inline] def moveNext (t : RawTable T) (pos stride : Nat) : Nat × Nat :=
  let stride := stride + WIDTH
  ((pos + stride) &&& t.bucket_mask, stride)

/-- `find_insert_index`. -/
def findInsertIndex (t : RawTable T) (hash : UInt64) : Result Nat :=
  loop (fun (ps : Nat × Nat) =>
    match t.findInsertIndexInGroup ps.1 with
    | some i => ok (done (t.fixInsertIndex i))
    | none => ok (cont (t.moveNext ps.1 ps.2)))
    (hash.toNat &&& t.bucket_mask, 0)

/-- The first `bit` (ascending) of the group at `pos` matching the tag whose bucket satisfies
`eq` (the `for bit in group.match_tag(tag_hash)` loop). -/
def firstEq (t : RawTable T) (pos : Nat) (tag : UInt8) (eq : T → Result Bool) :
    Result (Option Nat) :=
  (bits (t.matchTag pos tag)).foldlM (init := none) fun acc bit =>
    match acc with
    | some i => ok (some i)
    | none => do
      let i := (pos + bit) &&& t.bucket_mask
      let v ← t.getSlot i
      let b ← eq v
      if b then ok (some i) else ok none

/-- `find_inner`. -/
def find (t : RawTable T) (hash : UInt64) (eq : T → Result Bool) : Result (Option Nat) :=
  let tag := tagOf hash
  loop (fun (ps : Nat × Nat) => do
    let r ← t.firstEq ps.1 tag eq
    match r with
    | some i => ok (done (some i))
    | none =>
      if t.matchEmpty ps.1 != 0 then ok (done none)
      else ok (cont (t.moveNext ps.1 ps.2)))
    (hash.toNat &&& t.bucket_mask, 0)

/-- `find_or_find_insert_index_inner`: `.inl` found bucket, `.inr` insertion index. -/
def findOrFindInsertIndexInner (t : RawTable T) (hash : UInt64) (eq : T → Result Bool) :
    Result (Nat ⊕ Nat) :=
  let tag := tagOf hash
  loop (fun (st : Nat × Nat × Option Nat) => do
    let (pos, stride, insertIndex) := st
    let r ← t.firstEq pos tag eq
    match r with
    | some i => ok (done (.inl i))
    | none =>
      let insertIndex :=
        if insertIndex.isNone then t.findInsertIndexInGroup pos else insertIndex
      match insertIndex with
      | some ii =>
        if t.matchEmpty pos != 0 then ok (done (.inr (t.fixInsertIndex ii)))
        else let (p, s) := t.moveNext pos stride; ok (cont (p, s, insertIndex))
      | none => let (p, s) := t.moveNext pos stride; ok (cont (p, s, insertIndex)))
    (hash.toNat &&& t.bucket_mask, 0, none)

/-- `record_item_insert_at` + writing the element (`insert_tagged_at_index`). -/
def insertAtIndex (t : RawTable T) (hash : UInt64) (i : Nat) (v : T) : RawTable T :=
  let old := t.ctrlAt i
  let t := { t with growth_left := t.growth_left - (if old &&& 1 != 0 then 1 else 0) }
  let t := t.setCtrl i (tagOf hash)
  let t := { t with items := t.items + 1 }
  t.setSlot i (some v)

/-- `RawTableInner::erase` (the element is moved out by the caller). -/
def erase (t : RawTable T) (i : Nat) : RawTable T :=
  let emptyBefore := t.matchEmpty (t.subWidthMasked i)
  let emptyAfter := t.matchEmpty i
  let (b, t) :=
    if leadingZeros emptyBefore + trailingZeros emptyAfter ≥ WIDTH then (DELETED, t)
    else (EMPTY, { t with growth_left := t.growth_left + 1 })
  let t := t.setCtrl i b
  let t := { t with items := t.items - 1 }
  t.setSlot i none

/-- The full buckets in `RawIter` / `FullBucketsIndices` order (ascending index). -/
def fullIndices (t : RawTable T) : List Nat :=
  (List.range t.numBuckets).filter fun i => isFull (t.ctrlAt i)

/-- The elements in `RawIter` order. -/
def elems (t : RawTable T) : List T :=
  t.fullIndices.filterMap fun i => (t.slots[i]?).join

/-- `clear_no_drop`. -/
def clearNoDrop (t : RawTable T) : RawTable T :=
  let t := if t.bucket_mask != 0 then
      { t with ctrl := Array.replicate t.ctrl.size EMPTY,
               slots := Array.replicate t.slots.size none }
    else t
  { t with items := 0, growth_left := bucketMaskToCapacity t.bucket_mask }

/-- `RawTable::clear`. -/
def clear (t : RawTable T) : RawTable T := if t.items = 0 then t else t.clearNoDrop

/-- `resize_inner`: reinsert the elements, in ascending old-bucket order, into a new table with
the given capacity. -/
def resize (t : RawTable T) (capacity : Nat) (hasher : T → Result UInt64) :
    Result (RawTable T) := do
  let nt ← withCapacity capacity
  let nt ← t.fullIndices.foldlM (init := nt) fun (nt : RawTable T) (i : Nat) => do
    let v ← t.getSlot i
    let h ← hasher v
    let ni ← nt.findInsertIndex h
    ok ((nt.setCtrl ni (tagOf h)).setSlot ni (some v))
  ok { nt with growth_left := nt.growth_left - t.items, items := t.items }

/-- `prepare_rehash_in_place`. -/
def prepareRehashInPlace (t : RawTable T) : RawTable T :=
  let n := t.numBuckets
  let ctrl := (List.range ((n + WIDTH - 1) / WIDTH)).foldl (init := t.ctrl) fun ctrl g =>
    (List.range WIDTH).foldl (init := ctrl) fun ctrl j =>
      let i := g * WIDTH + j
      ctrl.set! i (if isSpecial ctrl[i]! then EMPTY else DELETED)
  let ctrl :=
    if n < WIDTH then
      (List.range n).foldl (init := ctrl) fun c j => c.set! (WIDTH + j) c[j]!
    else
      (List.range WIDTH).foldl (init := ctrl) fun c j => c.set! (n + j) c[j]!
  { t with ctrl := ctrl }

/-- `is_in_same_group`. -/
def isInSameGroup (t : RawTable T) (i newI : Nat) (hash : UInt64) : Bool :=
  let p := hash.toNat &&& t.bucket_mask
  let n := t.numBuckets
  let probeIndex := fun (pos : Nat) => ((pos + n - p) % n) / WIDTH
  probeIndex i == probeIndex newI

/-- The `loop` of `rehash_in_place` for a DELETED (= to be rehashed) bucket `i`: move its
element to its insertion position, swapping with a DELETED one there and repeating. -/
def rehashBucket (hasher : T → Result UInt64) (i : Nat) (t0 : RawTable T) :
    Result (RawTable T) :=
  loop (fun (t : RawTable T) => do
    let v ← t.getSlot i
    let hash ← hasher v
    let newI ← t.findInsertIndex hash
    if t.isInSameGroup i newI hash then
      ok (done (t.setCtrl i (tagOf hash)))
    else
      let prev := t.ctrlAt newI
      let t1 := t.setCtrl newI (tagOf hash)
      if prev == EMPTY then
        let t2 := (t1.setCtrl i EMPTY).setSlot newI (some v)
        ok (done (t2.setSlot i none))
      else
        ok (cont { t1 with slots := t1.slots.swapIfInBounds i newI })) t0

/-- `rehash_in_place`. -/
def rehashInPlace (t : RawTable T) (hasher : T → Result UInt64) : Result (RawTable T) := do
  let t0 := t.prepareRehashInPlace
  let t1 ← (List.range t0.numBuckets).foldlM (init := t0) fun (acc : RawTable T) (i : Nat) =>
    if acc.ctrlAt i != DELETED then ok acc else rehashBucket hasher i acc
  ok { t1 with growth_left := bucketMaskToCapacity t1.bucket_mask - t1.items }

/-- `reserve_rehash_inner` (`Fallibility::Infallible`). -/
def reserveRehash (t : RawTable T) (additional : Nat) (hasher : T → Result UInt64) :
    Result (RawTable T) :=
  let newItems := t.items + additional
  if newItems ≥ USIZE_BOUND then fail .panic -- "Hash table capacity overflow"
  else
    let fullCapacity := bucketMaskToCapacity t.bucket_mask
    if newItems ≤ fullCapacity / 2 then t.rehashInPlace hasher
    else t.resize (max newItems (fullCapacity + 1)) hasher

/-- `RawTable::reserve`. -/
def reserve (t : RawTable T) (additional : Nat) (hasher : T → Result UInt64) :
    Result (RawTable T) :=
  if additional > t.growth_left then t.reserveRehash additional hasher else ok t

/-- `RawTable::insert`: returns the table and the bucket index. -/
def insert (t : RawTable T) (hash : UInt64) (v : T) (hasher : T → Result UInt64) :
    Result (RawTable T × Nat) := do
  let i0 ← t.findInsertIndex hash
  if t.growth_left == 0 && (t.ctrlAt i0 &&& 1) != 0 then
    let t1 ← t.reserve 1 hasher
    let i1 ← t1.findInsertIndex hash
    ok (t1.insertAtIndex hash i1 v, i1)
  else ok (t.insertAtIndex hash i0 v, i0)

/-- `RawTable::clone` (element-wise `clone_from_impl`, ascending bucket order); the allocator
is cloned first. -/
def clone (t : RawTable T) (cloneT : T → Result T) : Result (RawTable T) :=
  if t.bucket_mask = 0 then ok new
  else do
    let slots ← t.fullIndices.foldlM (init := Array.replicate t.numBuckets none)
      fun (slots : Array (Option T)) (i : Nat) => do
        let v ← t.getSlot i
        let v ← cloneT v
        ok (slots.set! i (some v))
    ok { t with slots := slots }

end RawTable

/-- `make_hash` (`BuildHasher::hash_one`): `build_hasher`, `Hash::hash`, `finish`. -/
def makeHash {Q S H : Type} (bh : core.hash.BuildHasher S H) (hashQ : core.hash.Hash Q)
    (s : S) (q : Q) : Result UInt64 := do
  let st ← bh.build_hasher s
  let st ← hashQ.hash bh.HasherInst q st
  let h ← bh.HasherInst.finish st
  ok (UInt64.ofNat h.bv.toNat)

/-- `make_hasher`: hash of the key of an entry. -/
def makeHasher {K V S H : Type} (bh : core.hash.BuildHasher S H) (hashK : core.hash.Hash K)
    (s : S) : K × V → Result UInt64 :=
  fun kv => makeHash bh hashK s kv.1

/-- `Equivalent<K> for K` with `K: Eq` (blanket, `Borrow` = identity): `PartialEq::eq`. -/
def eqKey {K V : Type} (eqK : core.cmp.Eq K) (k : K) : K × V → Result Bool :=
  fun kv => eqK.partialEqInst.eq k kv.1

/-- `equivalent_key(q)`: `q.equivalent(&x.0)`. -/
def equivKey {Q K V : Type} (eqv : hashbrown_2.Equivalent Q K) (q : Q) : K × V → Result Bool :=
  fun kv => eqv.equivalent q kv.1

/-- `iter.size_hint().0`. -/
def sizeHintLower {I Item : Type} (inst : core.iter.traits.iterator.Iterator I Item) (it : I) :
    Result Nat := do
  let (lo, _) ← inst.size_hint it
  ok lo.bv.toNat

/-- Drive an iterator to exhaustion with `next` (the `for_each` of `extend` / `from_iter`). -/
def forEach {I Item St : Type} (inst : core.iter.traits.iterator.Iterator I Item) (it : I)
    (st : St) (f : St → Item → Result St) : Result St :=
  loop (fun (p : I × St) => do
    let (o, it) ← inst.next p.1
    match o with
    | none => ok (done p.2)
    | some x => do let st ← f p.2 x; ok (cont (it, st)))
    (it, st)

namespace Map
variable {K V S A H : Type}

/-- `HashMap::insert`. -/
def insert (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K) (bh : core.hash.BuildHasher S H)
    (m : hashbrown_2.map.HashMap K V S A) (k : K) (v : V) :
    Result (Option V × hashbrown_2.map.HashMap K V S A) := do
  let hash ← makeHash bh hashK m.hash_builder k
  let t ← m.table.reserve 1 (makeHasher bh hashK m.hash_builder)
  let r ← t.findOrFindInsertIndexInner hash (eqKey eqK k)
  match r with
  | .inl i =>
    let (k0, old) ← t.getSlot i
    ok (some old, { m with table := t.setSlot i (some (k0, v)) })
  | .inr i =>
    ok (none, { m with table := t.insertAtIndex hash i (k, v) })

/-- `HashMap::reserve`. -/
def reserve (hashK : core.hash.Hash K) (bh : core.hash.BuildHasher S H)
    (m : hashbrown_2.map.HashMap K V S A) (additional : Nat) :
    Result (hashbrown_2.map.HashMap K V S A) := do
  let t ← m.table.reserve additional (makeHasher bh hashK m.hash_builder)
  ok { m with table := t }

/-- Lookup of `q` (`HashMap::get` & co.): `none` without hashing on an empty table. -/
def findQ {Q : Type} (bh : core.hash.BuildHasher S H) (hashQ : core.hash.Hash Q)
    (eqv : hashbrown_2.Equivalent Q K) (m : hashbrown_2.map.HashMap K V S A) (q : Q) :
    Result (Option Nat) := do
  if m.table.items = 0 then ok none
  else
    let hash ← makeHash bh hashQ m.hash_builder q
    m.table.find hash (equivKey eqv q)

/-- `FromIterator<(K, V)>::from_iter` once `iter.into_iter()` is `it` with `size_hint().0 = lo`:
`with_capacity_and_hasher_in(lo, S::default(), A::default())`, then insert each item. -/
def fromIterCore {I : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : core.hash.BuildHasher S H) (defS : core.default.Default S)
    (defA : core.default.Default A) (inst : core.iter.traits.iterator.Iterator I (K × V))
    (it : I) (lo : Nat) : Result (hashbrown_2.map.HashMap K V S A) := do
  let s ← defS.default
  let a ← defA.default
  let t ← RawTable.withCapacity lo
  let m : hashbrown_2.map.HashMap K V S A := { hash_builder := s, table := t, alloc := a }
  forEach inst it m fun m kv => do
    let (_, m) ← Map.insert eqK hashK bh m kv.1 kv.2
    ok m

/-- `Extend<(K, ())>::extend` (the set's `extend`) once `iter.into_iter()` is `it` with
`size_hint().0 = lo`: reserve `lo` (empty map) or `lo.div_ceil(2)`, then insert each item. -/
def extendKeysCore {I : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : core.hash.BuildHasher S H) (inst : core.iter.traits.iterator.Iterator I K)
    (m : hashbrown_2.map.HashMap K Unit S A) (it : I) (lo : Nat) :
    Result (hashbrown_2.map.HashMap K Unit S A) := do
  let reserve := if m.table.items = 0 then lo else (lo + 1) / 2
  let m ← Map.reserve hashK bh m reserve
  forEach inst it m fun m k => do
    let (_, m) ← Map.insert eqK hashK bh m k ()
    ok m

end Map

/-- `Debug` of a sequence of entries (`debug_map().entries(..).finish()` with the library's
formatter model): format key then value per entry, stop at the first error. -/
def fmtEntries {K V : Type} (dK : core.fmt.Debug K) (dV : core.fmt.Debug V)
    (es : List (K × V)) (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  es.foldlM (init := (core.result.Result.Ok (), f)) fun (r, f) (k, v) =>
    match r with
    | .Err e => ok (.Err e, f)
    | .Ok () => do
      let (r, f) ← dK.fmt k f
      match r with
      | .Err e => ok (.Err e, f)
      | .Ok () => dV.fmt v f

end ClifvModels.Hashbrown

open ClifvModels.Hashbrown

/-- [hashbrown#2::alloc::inner::{core::default::Default<hashbrown#2::alloc::inner::Global>}::default] -/
def hashbrown_2.alloc.inner.Global.Insts.CoreDefaultDefault.default
  : Result hashbrown_2.alloc.inner.Global :=
  ok ()

/-- [hashbrown#2::alloc::inner::{core::clone::Clone<hashbrown#2::alloc::inner::Global>}::clone] -/
def hashbrown_2.alloc.inner.Global.Insts.CoreCloneClone.clone
  : hashbrown_2.alloc.inner.Global → Result hashbrown_2.alloc.inner.Global :=
  fun _ => ok ()

/-- [hashbrown#2::alloc::inner::{hashbrown#2::alloc::inner::Allocator<hashbrown#2::alloc::inner::Global>}::deallocate]:
freeing has no observable effect in the model. -/
def hashbrown_2.alloc.inner.Global.Insts.Hashbrown_2AllocInnerAllocator.deallocate
  :
  hashbrown_2.alloc.inner.Global → core.ptr.non_null.NonNull Std.U8 →
    core.alloc.layout.Layout → Result Unit :=
  fun _ _ _ => ok ()

/-- [hashbrown#2::alloc::inner::{hashbrown#2::alloc::inner::Allocator<hashbrown#2::alloc::inner::Global>}::allocate]:
`Ok` with a fresh block of `layout.size()` bytes (zeros: the native contents are uninitialized)
in the library's value-based `NonNull` model; allocation failure (`alloc` returning null) is not
modeled. -/
def hashbrown_2.alloc.inner.Global.Insts.Hashbrown_2AllocInnerAllocator.allocate
  :
  hashbrown_2.alloc.inner.Global → core.alloc.layout.Layout → Result
    (core.result.Result (core.ptr.non_null.NonNull (Slice Std.U8)) Unit) :=
  fun _ layout =>
    ok (.Ok ⟨⟨Slice.ofListClamp (List.replicate layout.size.bv.toNat ⟨BitVec.ofNat 8 0⟩)⟩⟩)

/-- [hashbrown#2::{hashbrown#2::Equivalent<@Q, @K>}::equivalent]:
`PartialEq::eq(self, key.borrow())`. -/
def hashbrown_2.Equivalent.Blanket.equivalent
  {Q : Type _} {K : Type _} (corecmpEqInst : core.cmp.Eq Q)
  (coreborrowBorrowInst : core.borrow.Borrow K Q) :
  Q → K → Result Bool :=
  fun q k => do
    let k ← coreborrowBorrowInst.borrow k
    corecmpEqInst.partialEqInst.eq q k

/-! ## HashMap -/

/-- [hashbrown#2::map::{core::default::Default<hashbrown#2::map::HashMap<@K, @V, @S, @A>>}::default]:
`with_hasher_in(S::default(), A::default())`. -/
def hashbrown_2.map.HashMap.Insts.CoreDefaultDefault.default
  (K : Type _) (V : Type _) {S : Type _} {A : Type _} (coredefaultDefaultInst :
  core.default.Default S) (coredefaultDefaultInst1 : core.default.Default A)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A) :
  Result (hashbrown_2.map.HashMap K V S A) := do
  let s ← coredefaultDefaultInst.default
  let a ← coredefaultDefaultInst1.default
  ok { hash_builder := s, table := RawTable.new, alloc := a }

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, hashbrown#2::alloc::inner::Global>}::with_capacity_and_hasher] -/
def hashbrown_2.map.HashMapKVSGlobal.with_capacity_and_hasher
  (K : Type _) (V : Type _) {S : Type _} :
  Std.Usize → S → Result (hashbrown_2.map.HashMap K V S
    hashbrown_2.alloc.inner.Global) :=
  fun cap s => do
    let t ← RawTable.withCapacity cap.bv.toNat
    ok { hash_builder := s, table := t, alloc := () }

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::len] -/
def hashbrown_2.map.HashMap.len
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Result Std.Usize :=
  fun m => ok (toUsize m.table.items)

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::clear] -/
def hashbrown_2.map.HashMap.clear
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Result (hashbrown_2.map.HashMap K V S A) :=
  fun m => ok { m with table := m.table.clear }

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::insert] -/
def hashbrown_2.map.HashMap.insert
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Clause2_Hasher : Type _}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → K → V → Result ((Option V) ×
    (hashbrown_2.map.HashMap K V S A)) :=
  Map.insert corecmpEqInst corehashHashInst corehashBuildHasherInst

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::get] -/
def hashbrown_2.map.HashMap.get
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Q : Type _}
  {Clause2_Hasher : Type _} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst :
  core.hash.Hash K) (corehashBuildHasherInst : core.hash.BuildHasher S
  Clause2_Hasher) (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator
  A) (corehashHashInst1 : core.hash.Hash Q) (EquivalentInst :
  hashbrown_2.Equivalent Q K) :
  hashbrown_2.map.HashMap K V S A → Q → Result (Option V) :=
  fun m q => do
    let r ← Map.findQ corehashBuildHasherInst corehashHashInst1 EquivalentInst m q
    match r with
    | none => ok none
    | some i => do let (_, v) ← m.table.getSlot i; ok (some v)

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::contains_key] -/
def hashbrown_2.map.HashMap.contains_key
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Q : Type _}
  {Clause2_Hasher : Type _} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst :
  core.hash.Hash K) (corehashBuildHasherInst : core.hash.BuildHasher S
  Clause2_Hasher) (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator
  A) (corehashHashInst1 : core.hash.Hash Q) (EquivalentInst :
  hashbrown_2.Equivalent Q K) :
  hashbrown_2.map.HashMap K V S A → Q → Result Bool :=
  fun m q => do
    let r ← Map.findQ corehashBuildHasherInst corehashHashInst1 EquivalentInst m q
    ok r.isSome

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::get_mut] -/
def hashbrown_2.map.HashMap.get_mut
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Q : Type _}
  {Clause2_Hasher : Type _} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst :
  core.hash.Hash K) (corehashBuildHasherInst : core.hash.BuildHasher S
  Clause2_Hasher) (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator
  A) (corehashHashInst1 : core.hash.Hash Q) (EquivalentInst :
  hashbrown_2.Equivalent Q K) :
  hashbrown_2.map.HashMap K V S A → Q → Result ((Option V) × (Option V →
    hashbrown_2.map.HashMap K V S A)) :=
  fun m q => do
    let r ← Map.findQ corehashBuildHasherInst corehashHashInst1 EquivalentInst m q
    match r with
    | none => ok (none, fun _ => m)
    | some i => do
      let (k, v) ← m.table.getSlot i
      ok (some v, fun o => match o with
        | some v' => { m with table := m.table.setSlot i (some (k, v')) }
        | none => m)

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::remove]: hashes the key
even when the map is empty (`remove_entry` has no emptiness check). -/
def hashbrown_2.map.HashMap.remove
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Q : Type _}
  {Clause2_Hasher : Type _} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst :
  core.hash.Hash K) (corehashBuildHasherInst : core.hash.BuildHasher S
  Clause2_Hasher) (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator
  A) (corehashHashInst1 : core.hash.Hash Q) (EquivalentInst :
  hashbrown_2.Equivalent Q K) :
  hashbrown_2.map.HashMap K V S A → Q → Result ((Option V) ×
    (hashbrown_2.map.HashMap K V S A)) :=
  fun m q => do
    let hash ← makeHash corehashBuildHasherInst corehashHashInst1 m.hash_builder q
    let r ← m.table.find hash (equivKey EquivalentInst q)
    match r with
    | none => ok (none, m)
    | some i => do
      let (_, v) ← m.table.getSlot i
      ok (some v, { m with table := m.table.erase i })

/-- [hashbrown#2::map::{core::ops::index::Index<hashbrown#2::map::HashMap<@K, @V, @S, @A>, &'0 @Q, @V>}::index]:
`self.get(key).expect("no entry found for key")`. -/
def hashbrown_2.map.HashMap.Insts.CoreOpsIndexIndexShared0QV.index
  {K : Type _} {Q : Type _} {V : Type _} {S : Type _} {A : Type _}
  {Clause4_Hasher : Type _} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst :
  core.hash.Hash K) (corehashHashInst1 : core.hash.Hash Q) (EquivalentInst :
  hashbrown_2.Equivalent Q K) (corehashBuildHasherInst : core.hash.BuildHasher
  S Clause4_Hasher) (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Q → Result V :=
  fun m q => do
    let r ← hashbrown_2.map.HashMap.get corecmpEqInst corehashHashInst corehashBuildHasherInst
        allocinnerAllocatorInst corehashHashInst1 EquivalentInst m q
    match r with
    | some v => ok v
    | none => fail .panic

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::entry] -/
def hashbrown_2.map.HashMap.entry
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Clause2_Hasher : Type _}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → K → Result ((hashbrown_2.map.Entry K V
    S A) × (hashbrown_2.map.Entry K V S A → hashbrown_2.map.HashMap K V S
    A)) :=
  fun m k => do
    let hash ← makeHash corehashBuildHasherInst corehashHashInst m.hash_builder k
    let back : hashbrown_2.map.Entry K V S A → hashbrown_2.map.HashMap K V S A :=
      fun e => match e with
        | .Occupied o => o.map
        | .Vacant v => v.map
    let r ← m.table.find hash (eqKey corecmpEqInst k)
    match r with
    | some i => ok (.Occupied { map := m, hash := hash, index := i }, back)
    | none => ok (.Vacant { map := m, hash := hash, key := k }, back)

/-- [hashbrown#2::map::{hashbrown#2::map::VacantEntry<'a, @K, @V, @S, @A>}::insert]:
`RawTable::insert` of `(key, value)`; returns `&'a mut V` (backward: write the final value). -/
def hashbrown_2.map.VacantEntry.insert
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Clause2_Hasher : Type _}
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A)
  (corehashHashInst : core.hash.Hash K) (corehashBuildHasherInst :
  core.hash.BuildHasher S Clause2_Hasher) :
  hashbrown_2.map.VacantEntry K V S A → V → Result (V × (V →
    hashbrown_2.map.VacantEntry K V S A)) :=
  fun e v => do
    let m := e.map
    let (t, i) ← m.table.insert e.hash (e.key, v)
      (makeHasher corehashBuildHasherInst corehashHashInst m.hash_builder)
    ok (v, fun v' => { e with map := { m with table := t.setSlot i (some (e.key, v')) } })

/-- [hashbrown#2::map::{hashbrown#2::map::OccupiedEntry<'a, @K, @V, @S, @A>}::get] -/
def hashbrown_2.map.OccupiedEntry.get
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.OccupiedEntry K V S A → Result V :=
  fun e => do let (_, v) ← e.map.table.getSlot e.index; ok v

/-- [hashbrown#2::map::{hashbrown#2::map::OccupiedEntry<'a, @K, @V, @S, @A>}::insert]:
`mem::replace(self.get_mut(), value)`. -/
def hashbrown_2.map.OccupiedEntry.insert
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.OccupiedEntry K V S A → V → Result (V ×
    (hashbrown_2.map.OccupiedEntry K V S A) × (hashbrown_2.map.OccupiedEntry K
    V S A → hashbrown_2.map.OccupiedEntry K V S A)) :=
  fun e v => do
    let (k, old) ← e.map.table.getSlot e.index
    let e' := { e with map := { e.map with table := e.map.table.setSlot e.index (some (k, v)) } }
    ok (old, e', fun e'' => e'')

/-- `OccupiedEntry::into_mut` as `(value, backward)`. -/
def ClifvModels.Hashbrown.OccupiedEntry.intoMut {K V S A : Type}
    (e : hashbrown_2.map.OccupiedEntry K V S A) :
    Result (V × (V → hashbrown_2.map.OccupiedEntry K V S A)) := do
  let (k, v) ← e.map.table.getSlot e.index
  ok (v, fun v' => { e with map := { e.map with table := e.map.table.setSlot e.index (some (k, v')) } })

/-- [hashbrown#2::map::{hashbrown#2::map::Entry<'a, @K, @V, @S, @A>}::or_insert] -/
def hashbrown_2.map.Entry.or_insert
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Clause2_Hasher : Type _}
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A)
  (corehashHashInst : core.hash.Hash K) (corehashBuildHasherInst :
  core.hash.BuildHasher S Clause2_Hasher) :
  hashbrown_2.map.Entry K V S A → V → Result (V × (V →
    hashbrown_2.map.Entry K V S A)) :=
  fun e d => match e with
    | .Occupied o => do
      let (v, back) ← ClifvModels.Hashbrown.OccupiedEntry.intoMut o
      ok (v, fun v' => .Occupied (back v'))
    | .Vacant ve => do
      let (v, back) ← hashbrown_2.map.VacantEntry.insert allocinnerAllocatorInst
        corehashHashInst corehashBuildHasherInst ve d
      ok (v, fun v' => .Vacant (back v'))

/-- [hashbrown#2::map::{hashbrown#2::map::Entry<'a, @K, @V, @S, @A>}::or_insert_with]: `default`
is called only for a vacant entry. -/
def hashbrown_2.map.Entry.or_insert_with
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {F : Type _}
  {Clause3_Hasher : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) (coreopsfunctionFnOnceFTupleVInst :
  core.ops.function.FnOnce F Unit V) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause3_Hasher) :
  hashbrown_2.map.Entry K V S A → F → Result (V × (V →
    hashbrown_2.map.Entry K V S A)) :=
  fun e f => match e with
    | .Occupied o => do
      let (v, back) ← ClifvModels.Hashbrown.OccupiedEntry.intoMut o
      ok (v, fun v' => .Occupied (back v'))
    | .Vacant ve => do
      let d ← coreopsfunctionFnOnceFTupleVInst.call_once f ()
      let (v, back) ← hashbrown_2.map.VacantEntry.insert allocinnerAllocatorInst
        corehashHashInst corehashBuildHasherInst ve d
      ok (v, fun v' => .Vacant (back v'))

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::retain]: visits the entries
in iteration order, erasing those for which `f` returns `false`. (The `FnMut` model of the
closure returns no updated `V`, so values are left as they are.) -/
def hashbrown_2.map.HashMap.retain
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {F : Type _}
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A)
  (coreopsfunctionFnMutFPairShared0KMutVBoolInst : core.ops.function.FnMut F (K
  × V) Bool) :
  hashbrown_2.map.HashMap K V S A → F → Result (hashbrown_2.map.HashMap K V
    S A) :=
  fun m f => do
    let (t, _) ← m.table.fullIndices.foldlM (init := (m.table, f)) fun (t, f) i => do
      let kv ← t.getSlot i
      let (keep, f) ← coreopsfunctionFnMutFPairShared0KMutVBoolInst.call_mut f kv
      ok (if keep then t else t.erase i, f)
    ok { m with table := t }

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::iter] -/
def hashbrown_2.map.HashMap.iter
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Result (hashbrown_2.map.Iter K V) :=
  fun m => ok ⟨m.table.elems⟩

/-- [hashbrown#2::map::{core::iter::traits::collect::IntoIterator<&'a hashbrown#2::map::HashMap<@K, @V, @S, @A>, (&'a @K, &'a @V), hashbrown#2::map::Iter<'a, @K, @V>>}::into_iter] -/
def hashbrown_2.map.SharedAHashMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Result (hashbrown_2.map.Iter K V) :=
  fun m => ok ⟨m.table.elems⟩

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::next] -/
def hashbrown_2.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next
  {K : Type _} {V : Type _} :
  hashbrown_2.map.Iter K V → Result ((Option (K × V)) ×
    (hashbrown_2.map.Iter K V)) :=
  fun it => match it.rest with
    | [] => ok (none, it)
    | x :: xs => ok (some x, ⟨xs⟩)

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::values] -/
def hashbrown_2.map.HashMap.values
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Result (hashbrown_2.map.Values K V) :=
  fun m => ok ⟨m.table.elems⟩

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::Values<'a, @K, @V>, &'a @V>}::next] -/
def hashbrown_2.map.Values.Insts.CoreIterTraitsIteratorIteratorSharedAV.next
  {K : Type _} {V : Type _} :
  hashbrown_2.map.Values K V → Result ((Option V) × (hashbrown_2.map.Values
    K V)) :=
  fun it => match it.rest with
    | [] => ok (none, it)
    | x :: xs => ok (some x.2, ⟨xs⟩)

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::Values<'a, @K, @V>, &'a @V>}::size_hint]:
exact (`RawIter`: `(items, Some(items))`). -/
def hashbrown_2.map.Values.Insts.CoreIterTraitsIteratorIteratorSharedAV.size_hint
  {K : Type _} {V : Type _} :
  hashbrown_2.map.Values K V → Result (Std.Usize × (Option Std.Usize)) :=
  fun it => ok (toUsize it.rest.length, some (toUsize it.rest.length))

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::Values<'a, @K, @V>, &'a @V>}::fold] -/
def hashbrown_2.map.Values.Insts.CoreIterTraitsIteratorIteratorSharedAV.fold
  {K : Type _} {V : Type _} {B : Type _} {F : Type _}
  (coreopsfunctionFnMutFPairBSharedAVBInst : core.ops.function.FnMut F (B × V)
  B) :
  hashbrown_2.map.Values K V → B → F → Result B :=
  fun it init f => do
    let (acc, _) ← it.rest.foldlM (init := (init, f)) fun (acc, f) kv =>
      coreopsfunctionFnMutFPairBSharedAVBInst.call_mut f (acc, kv.2)
    ok acc

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::iter_mut] -/
def hashbrown_2.map.HashMap.iter_mut
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Result ((hashbrown_2.map.IterMut K V) ×
    (hashbrown_2.map.IterMut K V → hashbrown_2.map.HashMap K V S A)) :=
  fun m => ok (⟨m.table.slots, m.table.fullIndices⟩,
    fun it => { m with table := { m.table with slots := it.slots } })

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::IterMut<'a, @K, @V>, (&'a @K, &'a mut @V)>}::next]:
the backward function writes the final value of the yielded `&mut V` back into its bucket. -/
def hashbrown_2.map.IterMut.Insts.CoreIterTraitsIteratorIteratorPairSharedAKMutAV.next
  {K : Type _} {V : Type _} :
  hashbrown_2.map.IterMut K V → Result ((Option (K × V)) ×
    (hashbrown_2.map.IterMut K V) × (hashbrown_2.map.IterMut K V → Option (K
    × V) → hashbrown_2.map.IterMut K V)) :=
  fun it => match it.rest with
    | [] => ok (none, it, fun it' _ => it')
    | i :: is =>
      match it.slots[i]? with
      | some (some (k, v)) =>
        ok (some (k, v), { it with rest := is }, fun it' o => match o with
          | some (_, v') => { it' with slots := it'.slots.set! i (some (k, v')) }
          | none => it')
      | _ => fail .panic

/-- [hashbrown#2::map::{hashbrown#2::map::HashMap<@K, @V, @S, @A>}::values_mut] -/
def hashbrown_2.map.HashMap.values_mut
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → Result ((hashbrown_2.map.ValuesMut K V)
    × (hashbrown_2.map.ValuesMut K V → hashbrown_2.map.HashMap K V S A)) :=
  fun m => ok (⟨m.table.slots, m.table.fullIndices⟩,
    fun it => { m with table := { m.table with slots := it.slots } })

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::ValuesMut<'a, @K, @V>, &'a mut @V>}::next] -/
def hashbrown_2.map.ValuesMut.Insts.CoreIterTraitsIteratorIteratorMutAV.next
  {K : Type _} {V : Type _} :
  hashbrown_2.map.ValuesMut K V → Result ((Option V) ×
    (hashbrown_2.map.ValuesMut K V) × (hashbrown_2.map.ValuesMut K V →
    Option V → hashbrown_2.map.ValuesMut K V)) :=
  fun it => match it.rest with
    | [] => ok (none, it, fun it' _ => it')
    | i :: is =>
      match it.slots[i]? with
      | some (some (k, v)) =>
        ok (some v, { it with rest := is }, fun it' o => match o with
          | some v' => { it' with slots := it'.slots.set! i (some (k, v')) }
          | none => it')
      | _ => fail .panic

/-- [hashbrown#2::map::{core::iter::traits::collect::FromIterator<hashbrown#2::map::HashMap<@K, @V, @S, @A>, (@K, @V)>}::from_iter]:
`into_iter`, `with_capacity_and_hasher_in(size_hint().0, S::default(), A::default())`, insert
each item. -/
def hashbrown_2.map.HashMap.Insts.CoreIterTraitsCollectFromIteratorPair.from_iter
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {T : Type _}
  {Clause2_Hasher : Type _} {Clause6_IntoIter : Type _} (corecmpEqInst :
  core.cmp.Eq K) (corehashHashInst : core.hash.Hash K) (corehashBuildHasherInst
  : core.hash.BuildHasher S Clause2_Hasher) (coredefaultDefaultInst :
  core.default.Default S) (coredefaultDefaultInst1 : core.default.Default A)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A)
  (coreitertraitscollectIntoIteratorTPairClause6_IntoIterInst :
  core.iter.traits.collect.IntoIterator T (K × V) Clause6_IntoIter) :
  T → Result (hashbrown_2.map.HashMap K V S A) :=
  fun x => do
    let ii := coreitertraitscollectIntoIteratorTPairClause6_IntoIterInst
    let it ← ii.into_iter x
    let lo ← sizeHintLower ii.iteratorInst it
    Map.fromIterCore corecmpEqInst corehashHashInst corehashBuildHasherInst
      coredefaultDefaultInst coredefaultDefaultInst1 ii.iteratorInst it lo

/-- [hashbrown#2::map::{core::clone::Clone<hashbrown#2::map::HashMap<@K, @V, @S, @A>>}::clone]:
`hash_builder.clone()`, then the table (allocator clone, then the entries in bucket order, key
before value); the clone has the same layout. -/
def hashbrown_2.map.HashMap.Insts.CoreCloneClone.clone
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (corecloneCloneInst :
  core.clone.Clone K) (corecloneCloneInst1 : core.clone.Clone V)
  (corecloneCloneInst2 : core.clone.Clone S) (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) (corecloneCloneInst3 : core.clone.Clone
  A) :
  hashbrown_2.map.HashMap K V S A → Result (hashbrown_2.map.HashMap K V S A) :=
  fun m => do
    let s ← corecloneCloneInst2.clone m.hash_builder
    let a ← corecloneCloneInst3.clone m.alloc
    let t ← m.table.clone fun (k, v) => do
      let k ← corecloneCloneInst.clone k
      let v ← corecloneCloneInst1.clone v
      ok (k, v)
    ok { hash_builder := s, table := t, alloc := a }

/-- [hashbrown#2::map::{core::cmp::PartialEq<hashbrown#2::map::HashMap<@K, @V, @S, @A>, hashbrown#2::map::HashMap<@K, @V, @S, @A>>}::eq]:
equal lengths and every `(k, v)` of `self` (in iteration order, short-circuiting) has
`other.get(k) == Some(v')` with `v == v'`. -/
def hashbrown_2.map.HashMap.Insts.CoreCmpPartialEqHashMap.eq
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} {Clause3_Hasher : Type _}
  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corecmpPartialEqInst : core.cmp.PartialEq V V) (corehashBuildHasherInst :
  core.hash.BuildHasher S Clause3_Hasher) (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → hashbrown_2.map.HashMap K V S A →
    Result Bool :=
  fun m o =>
    if m.table.items != o.table.items then ok false
    else m.table.elems.foldlM (init := true) fun acc (k, v) =>
      if !acc then ok false
      else do
        let eqv : hashbrown_2.Equivalent K K :=
          { equivalent := fun q k' => corecmpEqInst.partialEqInst.eq q k' }
        let r ← Map.findQ corehashBuildHasherInst corehashHashInst eqv o k
        match r with
        | none => ok false
        | some i => do
          let (_, v') ← o.table.getSlot i
          corecmpPartialEqInst.eq v v'

/-- [hashbrown#2::map::{core::fmt::Debug<hashbrown#2::map::HashMap<@K, @V, @S, @A>>}::fmt]:
`f.debug_map().entries(self.iter()).finish()`. -/
def hashbrown_2.map.HashMap.Insts.CoreFmtDebug.fmt
  {K : Type _} {V : Type _} {S : Type _} {A : Type _} (corefmtDebugInst :
  core.fmt.Debug K) (corefmtDebugInst1 : core.fmt.Debug V)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.map.HashMap K V S A → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun m f => fmtEntries corefmtDebugInst corefmtDebugInst1 m.table.elems f

/-! ## HashSet (`HashMap<T, (), S, A>`) -/

/-- The `Eq`-based `Equivalent<T> for T`. -/
def ClifvModels.Hashbrown.selfEquiv {T : Type} (eqT : core.cmp.Eq T) : hashbrown_2.Equivalent T T :=
  { equivalent := fun q k => eqT.partialEqInst.eq q k }

/-- [hashbrown#2::set::{core::default::Default<hashbrown#2::set::HashSet<@T, @S, @A>>}::default] -/
def hashbrown_2.set.HashSet.Insts.CoreDefaultDefault.default
  (T : Type _) {S : Type _} {A : Type _} (coredefaultDefaultInst :
  core.default.Default S) (coredefaultDefaultInst1 : core.default.Default A)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A) :
  Result (hashbrown_2.set.HashSet T S A) := do
  let m ← hashbrown_2.map.HashMap.Insts.CoreDefaultDefault.default T Unit coredefaultDefaultInst
    coredefaultDefaultInst1 allocinnerAllocatorInst
  ok ⟨m⟩

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::len] -/
def hashbrown_2.set.HashSet.len
  {T : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.HashSet T S A → Result Std.Usize :=
  fun s => ok (toUsize s.map.table.items)

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::clear] -/
def hashbrown_2.set.HashSet.clear
  {T : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.HashSet T S A → Result (hashbrown_2.set.HashSet T S A) :=
  fun s => ok ⟨{ s.map with table := s.map.table.clear }⟩

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::insert]:
`self.map.insert(value, ()).is_none()`. -/
def hashbrown_2.set.HashSet.insert
  {T : Type _} {S : Type _} {A : Type _} {Clause2_Hasher : Type _}
  (corecmpEqInst : core.cmp.Eq T) (corehashHashInst : core.hash.Hash T)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.HashSet T S A → T → Result (Bool ×
    (hashbrown_2.set.HashSet T S A)) :=
  fun s x => do
    let (o, m) ← Map.insert corecmpEqInst corehashHashInst corehashBuildHasherInst s.map x ()
    ok (o.isNone, ⟨m⟩)

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::contains] -/
def hashbrown_2.set.HashSet.contains
  {T : Type _} {S : Type _} {A : Type _} {Q : Type _} {Clause2_Hasher : Type _}
  (corecmpEqInst : core.cmp.Eq T) (corehashHashInst : core.hash.Hash T)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A)
  (corehashHashInst1 : core.hash.Hash Q) (EquivalentInst :
  hashbrown_2.Equivalent Q T) :
  hashbrown_2.set.HashSet T S A → Q → Result Bool :=
  fun s q => do
    let r ← Map.findQ corehashBuildHasherInst corehashHashInst1 EquivalentInst s.map q
    ok r.isSome

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::remove] -/
def hashbrown_2.set.HashSet.remove
  {T : Type _} {S : Type _} {A : Type _} {Q : Type _} {Clause2_Hasher : Type _}
  (corecmpEqInst : core.cmp.Eq T) (corehashHashInst : core.hash.Hash T)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A)
  (corehashHashInst1 : core.hash.Hash Q) (EquivalentInst :
  hashbrown_2.Equivalent Q T) :
  hashbrown_2.set.HashSet T S A → Q → Result (Bool ×
    (hashbrown_2.set.HashSet T S A)) :=
  fun s q => do
    let (o, m) ← hashbrown_2.map.HashMap.remove corecmpEqInst corehashHashInst
      corehashBuildHasherInst allocinnerAllocatorInst corehashHashInst1 EquivalentInst s.map q
    ok (o.isSome, ⟨m⟩)

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::retain]:
`self.map.retain(|k, _| f(k))`. -/
def hashbrown_2.set.HashSet.retain
  {T : Type _} {S : Type _} {A : Type _} {F : Type _} (allocinnerAllocatorInst
  : hashbrown_2.alloc.inner.Allocator A)
  (coreopsfunctionFnMutFTupleShared0TBoolInst : core.ops.function.FnMut F T
  Bool) :
  hashbrown_2.set.HashSet T S A → F → Result (hashbrown_2.set.HashSet T S
    A) :=
  fun s f => do
    let (t, _) ← s.map.table.fullIndices.foldlM (init := (s.map.table, f)) fun (t, f) i => do
      let (k, _) ← t.getSlot i
      let (keep, f) ← coreopsfunctionFnMutFTupleShared0TBoolInst.call_mut f k
      ok (if keep then t else t.erase i, f)
    ok ⟨{ s.map with table := t }⟩

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::drain]: the elements in
iteration order; the set keeps its buckets, cleared by `clear_no_drop` (as when the native
`Drain` is dropped). -/
def hashbrown_2.set.HashSet.drain
  {T : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.HashSet T S A → Result ((hashbrown_2.set.Drain T A) ×
    (hashbrown_2.set.HashSet T S A)) :=
  fun s => ok (⟨s.map.table.elems.map (·.1)⟩,
    ⟨{ s.map with table := s.map.table.clearNoDrop }⟩)

/-- [hashbrown#2::set::{core::iter::traits::iterator::Iterator<hashbrown#2::set::Drain<'0, @K, @A>, @K>}::next] -/
def hashbrown_2.set.Drain.Insts.CoreIterTraitsIteratorIterator.next
  {K : Type _} {A : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.Drain K A → Result ((Option K) × (hashbrown_2.set.Drain K
    A)) :=
  fun d => match d.rest with
    | [] => ok (none, d)
    | x :: xs => ok (some x, ⟨xs⟩)

/-- [hashbrown#2::set::{hashbrown#2::set::HashSet<@T, @S, @A>}::iter] -/
def hashbrown_2.set.HashSet.iter
  {T : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.HashSet T S A → Result (hashbrown_2.set.Iter T) :=
  fun s => ok ⟨s.map.table.elems.map (·.1)⟩

/-- [hashbrown#2::set::{core::iter::traits::collect::IntoIterator<&'a hashbrown#2::set::HashSet<@T, @S, @A>, &'a @T, hashbrown#2::set::Iter<'a, @T>>}::into_iter] -/
def hashbrown_2.set.SharedAHashSet.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  {T : Type _} {S : Type _} {A : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.HashSet T S A → Result (hashbrown_2.set.Iter T) :=
  fun s => ok ⟨s.map.table.elems.map (·.1)⟩

/-- [hashbrown#2::set::{core::iter::traits::iterator::Iterator<hashbrown#2::set::Iter<'a, @K>, &'a @K>}::next] -/
def hashbrown_2.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAK.next
  {K : Type _} :
  hashbrown_2.set.Iter K → Result ((Option K) × (hashbrown_2.set.Iter K)) :=
  fun it => match it.rest with
    | [] => ok (none, it)
    | x :: xs => ok (some x, ⟨xs⟩)

/-! The exact `size_hint`s (`RawIter`: `(items, Some(items))`) of the other iterators, for the
trait instances of a run with `size_hint` in the `Iterator` model (not yet template items). -/

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::size_hint] -/
def hashbrown_2.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.size_hint
  {K : Type _} {V : Type _} :
  hashbrown_2.map.Iter K V → Result (Std.Usize × (Option Std.Usize)) :=
  fun it => ok (toUsize it.rest.length, some (toUsize it.rest.length))

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::IterMut<'a, @K, @V>, (&'a @K, &'a mut @V)>}::size_hint] -/
def hashbrown_2.map.IterMut.Insts.CoreIterTraitsIteratorIteratorPairSharedAKMutAV.size_hint
  {K : Type _} {V : Type _} :
  hashbrown_2.map.IterMut K V → Result (Std.Usize × (Option Std.Usize)) :=
  fun it => ok (toUsize it.rest.length, some (toUsize it.rest.length))

/-- [hashbrown#2::map::{core::iter::traits::iterator::Iterator<hashbrown#2::map::ValuesMut<'a, @K, @V>, &'a mut @V>}::size_hint] -/
def hashbrown_2.map.ValuesMut.Insts.CoreIterTraitsIteratorIteratorMutAV.size_hint
  {K : Type _} {V : Type _} :
  hashbrown_2.map.ValuesMut K V → Result (Std.Usize × (Option Std.Usize)) :=
  fun it => ok (toUsize it.rest.length, some (toUsize it.rest.length))

/-- [hashbrown#2::set::{core::iter::traits::iterator::Iterator<hashbrown#2::set::Iter<'a, @K>, &'a @K>}::size_hint] -/
def hashbrown_2.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAK.size_hint
  {K : Type _} :
  hashbrown_2.set.Iter K → Result (Std.Usize × (Option Std.Usize)) :=
  fun it => ok (toUsize it.rest.length, some (toUsize it.rest.length))

/-- [hashbrown#2::set::{core::iter::traits::iterator::Iterator<hashbrown#2::set::Drain<'0, @K, @A>, @K>}::size_hint] -/
def hashbrown_2.set.Drain.Insts.CoreIterTraitsIteratorIterator.size_hint
  {K : Type _} {A : Type _} (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.Drain K A → Result (Std.Usize × (Option Std.Usize)) :=
  fun d => ok (toUsize d.rest.length, some (toUsize d.rest.length))

/-- [hashbrown#2::set::{core::iter::traits::collect::Extend<hashbrown#2::set::HashSet<@T, @S, @A>, @T>}::extend]:
`self.map.extend(iter.into_iter().map(|k| (k, ())))` (`Map` keeps the inner `size_hint`). -/
def hashbrown_2.set.HashSet.Insts.CoreIterTraitsCollectExtend.extend
  {T : Type _} {S : Type _} {A : Type _} {I : Type _} {Clause2_Hasher : Type _}
  {Clause4_IntoIter : Type _} (corecmpEqInst : core.cmp.Eq T) (corehashHashInst
  : core.hash.Hash T) (corehashBuildHasherInst : core.hash.BuildHasher S
  Clause2_Hasher) (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator
  A) (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I T Clause4_IntoIter) :
  hashbrown_2.set.HashSet T S A → I → Result (hashbrown_2.set.HashSet T S
    A) :=
  fun s x => do
    let ii := coreitertraitscollectIntoIteratorInst
    let it ← ii.into_iter x
    let lo ← sizeHintLower ii.iteratorInst it
    let m ← Map.extendKeysCore corecmpEqInst corehashHashInst corehashBuildHasherInst
      ii.iteratorInst s.map it lo
    ok ⟨m⟩

/-- [hashbrown#2::set::{core::iter::traits::collect::Extend<hashbrown#2::set::HashSet<@T, @S, @A>, &'a @T>}::extend]:
`self.extend(iter.into_iter().copied())` (`Copied` keeps the inner `size_hint`). -/
def hashbrown_2.set.HashSet.Insts.CoreIterTraitsCollectExtendSharedAT.extend
  {T : Type _} {S : Type _} {A : Type _} {I : Type _} {Clause3_Hasher : Type _}
  {Clause5_IntoIter : Type _} (corecmpEqInst : core.cmp.Eq T) (corehashHashInst
  : core.hash.Hash T) (coremarkerCopyInst : core.marker.Copy T)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause3_Hasher)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A)
  (coreitertraitscollectIntoIteratorISharedATClause5_IntoIterInst :
  core.iter.traits.collect.IntoIterator I T Clause5_IntoIter) :
  hashbrown_2.set.HashSet T S A → I → Result (hashbrown_2.set.HashSet T S
    A) :=
  hashbrown_2.set.HashSet.Insts.CoreIterTraitsCollectExtend.extend corecmpEqInst
    corehashHashInst corehashBuildHasherInst allocinnerAllocatorInst
    coreitertraitscollectIntoIteratorISharedATClause5_IntoIterInst

/-- [hashbrown#2::set::{core::iter::traits::collect::FromIterator<hashbrown#2::set::HashSet<@T, @S, @A>, @T>}::from_iter]:
`with_hasher_in(S::default(), A::default())` then `extend`. -/
def hashbrown_2.set.HashSet.Insts.CoreIterTraitsCollectFromIterator.from_iter
  {T : Type _} {S : Type _} {A : Type _} {I : Type _} {Clause2_Hasher : Type _}
  {Clause6_IntoIter : Type _} (corecmpEqInst : core.cmp.Eq T) (corehashHashInst
  : core.hash.Hash T) (corehashBuildHasherInst : core.hash.BuildHasher S
  Clause2_Hasher) (coredefaultDefaultInst : core.default.Default S)
  (coredefaultDefaultInst1 : core.default.Default A) (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I T Clause6_IntoIter) :
  I → Result (hashbrown_2.set.HashSet T S A) :=
  fun x => do
    let s ← hashbrown_2.set.HashSet.Insts.CoreDefaultDefault.default T coredefaultDefaultInst
      coredefaultDefaultInst1 allocinnerAllocatorInst
    hashbrown_2.set.HashSet.Insts.CoreIterTraitsCollectExtend.extend corecmpEqInst
      corehashHashInst corehashBuildHasherInst allocinnerAllocatorInst
      coreitertraitscollectIntoIteratorInst s x

/-- [hashbrown#2::set::{core::clone::Clone<hashbrown#2::set::HashSet<@T, @S, @A>>}::clone] -/
def hashbrown_2.set.HashSet.Insts.CoreCloneClone.clone
  {T : Type _} {S : Type _} {A : Type _} (corecloneCloneInst : core.clone.Clone
  T) (corecloneCloneInst1 : core.clone.Clone S) (allocinnerAllocatorInst :
  hashbrown_2.alloc.inner.Allocator A) (corecloneCloneInst2 : core.clone.Clone
  A) :
  hashbrown_2.set.HashSet T S A → Result (hashbrown_2.set.HashSet T S A) :=
  fun s => do
    let m ← hashbrown_2.map.HashMap.Insts.CoreCloneClone.clone corecloneCloneInst
      { clone := fun (_ : Unit) => ok () } corecloneCloneInst1 allocinnerAllocatorInst
      corecloneCloneInst2 s.map
    ok ⟨m⟩

/-- [hashbrown#2::set::{core::cmp::PartialEq<hashbrown#2::set::HashSet<@T, @S, @A>, hashbrown#2::set::HashSet<@T, @S, @A>>}::eq]:
equal lengths and every element of `self` (iteration order, short-circuiting) is in `other`. -/
def hashbrown_2.set.HashSet.Insts.CoreCmpPartialEqHashSet.eq
  {T : Type _} {S : Type _} {A : Type _} {Clause2_Hasher : Type _}
  (corecmpEqInst : core.cmp.Eq T) (corehashHashInst : core.hash.Hash T)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (allocinnerAllocatorInst : hashbrown_2.alloc.inner.Allocator A) :
  hashbrown_2.set.HashSet T S A → hashbrown_2.set.HashSet T S A → Result
    Bool :=
  fun s o =>
    if s.map.table.items != o.map.table.items then ok false
    else s.map.table.elems.foldlM (init := true) fun acc (k, _) =>
      if !acc then ok false
      else do
        let r ← Map.findQ corehashBuildHasherInst corehashHashInst
          (selfEquiv corecmpEqInst) o.map k
        ok r.isSome

/-
Handwritten executable models of the `hashbrown` 0.17.0 types (`hashbrown#2` in the Aeneas
names) used by the extracted Cranelift/regalloc2 code.

The hash table is a faithful port of hashbrown's SwissTable `RawTable` as compiled natively on
x86_64 (SSE2 group width 16): the control bytes and the bucket array are represented explicitly,
so that every operation (probing, insertion slot choice, tombstones, growth, in-place rehash)
leaves the table in exactly the native layout, and iteration (ascending bucket index) yields the
native order. The algorithms are in `ClifvModels.Funs.Hashbrown`.
-/
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.Hashbrown

/-- hashbrown `RawTable<T, A>` (with its `RawTableInner`), SSE2 layout.

- `bucket_mask`: number of buckets minus one (`0` for the unallocated empty singleton).
- `ctrl`: the `num_buckets + 16` control bytes (`0xFF` EMPTY, `0x80` DELETED, `0..0x7F` FULL
  with the 7-bit tag); the last 16 replicate the first ones exactly as natively (for tables with
  fewer than 16 buckets, bytes `num_buckets..15` stay EMPTY and bytes `16..16+num_buckets`
  replicate). The empty singleton uses 17 EMPTY bytes (natively: a static group of EMPTYs).
- `slots`: the buckets (`some` exactly where the control byte is FULL). -/
structure RawTable (T : Type) where
  bucket_mask : Nat
  ctrl : Array UInt8
  slots : Array (Option T)
  items : Nat
  growth_left : Nat

end ClifvModels.Hashbrown

/-- [hashbrown#2::map::HashMap]: `{ hash_builder: S, table: RawTable<(K, V), A> }`. -/
structure hashbrown_2.map.HashMap (K : Type) (V : Type) (S : Type) (A : Type) : Type where
  hash_builder : S
  table : ClifvModels.Hashbrown.RawTable (K × V)
  alloc : A

/-- [hashbrown#2::set::HashSet]: `{ map: HashMap<T, (), S, A> }`. -/
structure hashbrown_2.set.HashSet (T : Type) (S : Type) (A : Type) : Type where
  map : hashbrown_2.map.HashMap T Unit S A

/-- [hashbrown#2::set::Drain]: the elements not yet yielded, in native iteration order. (The
drained set itself is already cleared when `HashSet::drain` returns, as when the native `Drain`
is dropped.) -/
structure hashbrown_2.set.Drain (K : Type) (A : Type) : Type where
  rest : List K

/-- [hashbrown#2::map::VacantEntry]: the map (borrowed mutably for `'a`), the key's hash, the
key. -/
structure hashbrown_2.map.VacantEntry (K : Type) (V : Type) (S : Type) (A : Type) : Type where
  map : hashbrown_2.map.HashMap K V S A
  hash : UInt64
  key : K

/-- [hashbrown#2::map::OccupiedEntry]: the map, the key's hash and the bucket index. -/
structure hashbrown_2.map.OccupiedEntry (K : Type) (V : Type) (S : Type) (A : Type) : Type where
  map : hashbrown_2.map.HashMap K V S A
  hash : UInt64
  index : Nat

/-- [hashbrown#2::map::Iter]: the remaining entries, in native iteration order. -/
structure hashbrown_2.map.Iter (K : Type) (V : Type) : Type where
  rest : List (K × V)

/-- [hashbrown#2::map::Values]: the remaining entries, in native iteration order. -/
structure hashbrown_2.map.Values (K : Type) (V : Type) : Type where
  rest : List (K × V)

/-- [hashbrown#2::map::IterMut]: the map's buckets (carrying the writes done through the yielded
`&mut V`s) and the remaining full bucket indices in native iteration order. -/
structure hashbrown_2.map.IterMut (K : Type) (V : Type) : Type where
  slots : Array (Option (K × V))
  rest : List Nat

/-- [hashbrown#2::map::ValuesMut]: as `IterMut`. -/
structure hashbrown_2.map.ValuesMut (K : Type) (V : Type) : Type where
  slots : Array (Option (K × V))
  rest : List Nat

/-- [hashbrown#2::set::Iter]: the remaining elements, in native iteration order. -/
structure hashbrown_2.set.Iter (K : Type) : Type where
  rest : List K

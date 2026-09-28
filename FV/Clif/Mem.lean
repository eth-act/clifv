import FV.Clif.Syntax

/-!
# Byte-addressed memory with explicit allocations, and the result monad `Res`

* Addresses are natural numbers (`< 2^64` in practice).
* `Mem.allocs` lists the live allocations. An access is valid iff all of its bytes lie in a
  single live allocation.
* Bytes are `Option (BitVec 8)`: `none` is uninitialised. Reading an uninitialised byte is
  `stuck` (a precondition violation), never a value.
* Allocation is a bump allocator (`Mem.next`): addresses are never reused, so a stale
  pointer never aliases a newer allocation. Consecutive allocations are separated by a
  16-byte gap.
* Multi-byte values are little-endian unless the access carries the `big` flag.
-/

namespace Clif

/-- Result of an instruction or memory operation. -/
inductive Res (α : Type) where
  | ok (a : α)
  | trap (code : TrapCode)
  | stuck (msg : String)
  deriving Repr, Inhabited

namespace Res

def bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok a, f => f a
  | .trap c, _ => .trap c
  | .stuck m, _ => .stuck m

instance : Monad Res where
  pure := .ok
  bind := Res.bind

instance : LawfulMonad Res := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : Res α) = .ok a := rfl
@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → Res β) : (Res.ok a >>= f) = f a := rfl
@[simp] theorem trap_bind {α β : Type} (c : TrapCode) (f : α → Res β) :
    (Res.trap c >>= f) = .trap c := rfl
@[simp] theorem stuck_bind {α β : Type} (m : String) (f : α → Res β) :
    (Res.stuck m >>= f) = .stuck m := rfl

/-- `some a ↦ ok a`, `none ↦ stuck msg`. -/
def ofOption {α : Type} (msg : String) : Option α → Res α
  | some a => .ok a
  | none => .stuck msg

@[simp] theorem ofOption_some {α : Type} (msg : String) (a : α) :
    ofOption msg (some a) = .ok a := rfl
@[simp] theorem ofOption_none {α : Type} (msg : String) :
    ofOption msg (none : Option α) = .stuck msg := rfl

/-- `ok ↦ ok`, `error c ↦ trap c`. -/
def ofExcept {α : Type} : Except TrapCode α → Res α
  | .ok a => .ok a
  | .error c => .trap c

@[simp] theorem ofExcept_ok {α : Type} (a : α) : ofExcept (.ok a : Except TrapCode α) = .ok a :=
  rfl
@[simp] theorem ofExcept_error {α : Type} (c : TrapCode) :
    ofExcept (.error c : Except TrapCode α) = .trap c := rfl

/-- Precondition check: `stuck msg` unless `b`. -/
def check (b : Bool) (msg : String) : Res Unit := if b then .ok () else .stuck msg

@[simp] theorem check_true (msg : String) : check true msg = .ok () := rfl
@[simp] theorem check_false (msg : String) : check false msg = .stuck msg := rfl

end Res

/-- A live allocation `[base, base + size)`. Stores into a `readonly` allocation (link-time
data not marked writable) are `stuck`. -/
structure Alloc where
  base : Nat
  size : Nat
  readonly : Bool := false
  deriving DecidableEq, Repr, Inhabited

def Alloc.contains (a : Alloc) (addr n : Nat) : Bool :=
  a.base ≤ addr && addr + n ≤ a.base + a.size

/-- Memory state. -/
structure Mem where
  allocs : List Alloc := []
  bytes : Nat → Option (BitVec 8) := fun _ => none
  /-- Next free address for the bump allocator. -/
  next : Nat := 0x10000
  /-- Link-time symbol addresses (`symbol_value`), fixed by the initial image
  (`Clif.Image.mem`); never changed by execution. -/
  symbols : String → Option Nat := fun _ => none

namespace Mem

def empty : Mem := {}

instance : Inhabited Mem := ⟨empty⟩

/-- Is `[addr, addr + n)` inside one live allocation? -/
def valid (m : Mem) (addr n : Nat) : Bool := m.allocs.any (·.contains addr n)

/-- Round `n` up to a multiple of `a` (`a > 0`). -/
def alignUp (n a : Nat) : Nat := (n + a - 1) / a * a

/-- Allocate `size` fresh, uninitialised bytes aligned to `align` (at least 16). Returns the
base address. -/
def alloc (m : Mem) (size align : Nat) : Nat × Mem :=
  let base := alignUp m.next (max align 16)
  (base, { m with allocs := { base, size } :: m.allocs, next := base + size + 16 })

/-- Free the allocations with the given base addresses. Their bytes become unreachable
(addresses are never reused). -/
def free (m : Mem) (bases : List Nat) : Mem :=
  { m with allocs := m.allocs.filter (fun a => !bases.contains a.base) }

/-- Byte `i` of an `n`-byte access in the given byte order. -/
def byteIndex (big : Bool) (n i : Nat) : Nat := if big then n - 1 - i else i

/-- Read `n` bytes at `addr` as a `w`-bit value (`w = 8 * n`); `none` if a byte is
uninitialised. No bounds check. -/
def readBits (m : Mem) (big : Bool) (addr n w : Nat) : Option (BitVec w) :=
  (List.range n).foldlM (init := 0) fun acc i => do
    let b ← m.bytes (addr + byteIndex big n i)
    pure (acc ||| (b.zeroExtend w <<< (8 * i)))

/-- Write the low `8 * n` bits of `x` as `n` bytes at `addr`. No bounds check. -/
def writeBits {w : Nat} (m : Mem) (big : Bool) (addr n : Nat) (x : BitVec w) : Mem :=
  { m with bytes := fun a =>
      if addr ≤ a ∧ a < addr + n then
        some (x.extractLsb' (8 * byteIndex big n (a - addr)) 8)
      else m.bytes a }

/-- Bounds and alignment preconditions of an `n`-byte access with `flags`. Out of bounds
traps with the flags' trap code (default `heap_oob`) and is `stuck` if the access is
`notrap`; a misaligned `aligned` access is `stuck`. -/
def checkAccess (m : Mem) (flags : MemFlags) (addr n : Nat) : Res Unit :=
  if m.valid addr n then
    if flags.aligned && addr % n != 0 then .stuck s!"misaligned `aligned` access at {addr}"
    else .ok ()
  else
    match flags.trapCode with
    | some c => .trap c
    | none => .stuck s!"`notrap` access out of bounds at {addr}"

/-- Checked load of `n` bytes as a `w`-bit value. -/
def load (m : Mem) (flags : MemFlags) (addr n w : Nat) : Res (BitVec w) := do
  m.checkAccess flags addr n
  Res.ofOption s!"read of uninitialised memory at {addr}"
    (m.readBits (flags.endianness == some .big) addr n w)

/-- Does `[addr, addr + n)` overlap a read-only allocation? -/
def readonlyAt (m : Mem) (addr n : Nat) : Bool :=
  m.allocs.any fun a => a.readonly && a.base < addr + n && addr < a.base + a.size

/-- Checked store of the low `n` bytes of `x`. A store into read-only data is `stuck`. -/
def store {w : Nat} (m : Mem) (flags : MemFlags) (addr n : Nat) (x : BitVec w) : Res Mem := do
  m.checkAccess flags addr n
  Res.check (!m.readonlyAt addr n) s!"store to read-only data at {addr}"
  pure (m.writeBits (flags.endianness == some .big) addr n x)

end Mem

/-! ## Link-time image: data objects and `symbol_value` addresses -/

namespace Image

def itemSize : DataItem → Nat
  | .byte _ => 1
  | .addr .. => 8

def size (o : DataObject) : Nat := (o.items.map itemSize).sum

/-- Allocate the objects in order (bump allocator, alignment `max align 16`), read-only
unless `writable`. Returns each object's address. -/
def place (m : Mem) : List DataObject → List (String × Nat) × Mem
  | [] => ([], m)
  | o :: os =>
    let (base, m1) := m.alloc (size o) o.align
    let m1 := { m1 with allocs := m1.allocs.map fun a =>
      if a.base == base then { a with readonly := !o.writable } else a }
    let (rest, m2) := place m1 os
    ((o.name, base) :: rest, m2)

/-- Write the contents `items` at `addr`; relocations resolve through `syms`. -/
def writeItems (syms : List (String × Nat)) (m : Mem) (addr : Nat) :
    List DataItem → Res Mem
  | [] => .ok m
  | .byte b :: is => writeItems syms (m.writeBits false addr 1 b) (addr + 1) is
  | .addr n off :: is => do
    let base ← Res.ofOption s!"data relocation to unknown symbol %{n}" (syms.lookup n)
    writeItems syms (m.writeBits false addr 8 (BitVec.ofInt 64 (base + off))) (addr + 8) is

/-- The initial memory of a program with data objects `ds`: the objects allocated and
initialised, and `symbols` mapping each object name to its address. Names must be distinct;
relocations may only name objects of `ds`. -/
def mem (ds : List DataObject) : Res Mem := do
  let names := ds.map (·.name)
  Res.check (names.eraseDups.length == names.length) "duplicate data object name"
  let (syms, m) := place Mem.empty ds
  let m ← ds.foldlM (init := m) fun m o => do
    let base ← Res.ofOption "data object not placed" (syms.lookup o.name)
    writeItems syms m base o.items
  pure { m with symbols := fun n => syms.lookup n }

end Image

/-- Initial memory of a program: `Mem.empty` without data objects, else `Image.mem`
extended with one entry-stub address per function (and per extern declaration), so
`func_addr` and data-object relocations to function symbols resolve to the same
addresses (`Clif.Rust`). Function symbols are only registered when the program has data
objects — `run_of_data_nil` keeps `Clif.run` starting from `Mem.empty` otherwise. -/
def Program.initMem (p : Program) : Res Mem :=
  match p.data with
  | [] => .ok Mem.empty
  | ds => do
    let m ← Image.mem ds
    -- one stub slot per function/extern name, 16-aligned after the data objects
    let names := (p.funcs.map (·.name) ++
      (p.funcs.flatMap fun f => f.externs.map (·.2.name))).eraseDups
    let names := names.filter fun n => (m.symbols n).isNone
    let start := (m.next + 15) / 16 * 16
    let addrs := names.zip ((List.range names.length).map fun i => start + 16 * i)
    pure { m with
      next := start + 16 * names.length
      symbols := fun n => match addrs.lookup n with
        | some a => some a
        | none => m.symbols n }

end Clif

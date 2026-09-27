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

/-- Resource check: `trap code` unless `b`. -/
def trapUnless (b : Bool) (code : TrapCode) : Res Unit := if b then .ok () else .trap code

@[simp] theorem trapUnless_true (code : TrapCode) : trapUnless true code = .ok () := rfl
@[simp] theorem trapUnless_false (code : TrapCode) : trapUnless false code = .trap code := rfl

end Res

/-- A live allocation `[base, base + size)`. -/
structure Alloc where
  base : Nat
  size : Nat
  deriving DecidableEq, Repr, Inhabited

def Alloc.contains (a : Alloc) (addr n : Nat) : Bool :=
  a.base ≤ addr && addr + n ≤ a.base + a.size

/-- Memory state. -/
structure Mem where
  allocs : List Alloc := []
  bytes : Nat → Option (BitVec 8) := fun _ => none
  /-- Next free address for the bump allocator. -/
  next : Nat := 0x10000

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
  (base, { m with allocs := ⟨base, size⟩ :: m.allocs, next := base + size + 16 })

/-- The address space is 64 bits: every allocation must end below `2^64`
(`18446744073709551616`, a literal so that the check reduces by `rfl`/`decide`). -/
@[simp] def fits (m : Mem) : Bool := m.next ≤ 18446744073709551616

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

/-- Checked store of the low `n` bytes of `x`. -/
def store {w : Nat} (m : Mem) (flags : MemFlags) (addr n : Nat) (x : BitVec w) : Res Mem := do
  m.checkAccess flags addr n
  pure (m.writeBits (flags.endianness == some .big) addr n x)

end Mem

end Clif

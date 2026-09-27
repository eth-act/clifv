import FV.Clif.Syntax

/-!
# Per-opcode semantics of the CLIF integer subset

Every opcode of subset S is a small, separately unfoldable definition on `BitVec`. These
are the definitions M4 proves ISLE lowering rules against, and the ones cross-read against
VeriISLE in `docs/contracts/clif-spec-crossread.md`.

Each definition follows Cranelift 0.136.1 (`cranelift/codegen/meta/src/shared/instructions.rs`
for the documented meaning, `cranelift/interpreter/src/step.rs` and `value.rs` for the
reference implementation). Differences from the interpreter are listed in
`docs/contracts/clif.md`.

Trapping operations return `Except TrapCode`.
-/

namespace Clif.Sem

variable {w : Nat}

/-! ## Arithmetic -/

/-- `iadd`: wrapping addition. -/
def iadd (x y : BitVec w) : BitVec w := x + y
/-- `isub`: wrapping subtraction. -/
def isub (x y : BitVec w) : BitVec w := x - y
/-- `ineg`: wrapping negation. -/
def ineg (x : BitVec w) : BitVec w := -x
/-- `imul`: wrapping multiplication (low half of the product). -/
def imul (x y : BitVec w) : BitVec w := x * y

/-- `umulhi`: high half of the unsigned double-width product. -/
def umulhi (x y : BitVec w) : BitVec w :=
  ((x.zeroExtend (w + w)) * (y.zeroExtend (w + w))).extractLsb' w w

/-- `smulhi`: high half of the signed double-width product. -/
def smulhi (x y : BitVec w) : BitVec w :=
  ((x.signExtend (w + w)) * (y.signExtend (w + w))).extractLsb' w w

/-- `iabs`: absolute value; `iabs MIN = MIN`. -/
def iabs (x : BitVec w) : BitVec w := if x.msb then -x else x

/-! ## Division (trapping) -/

/-- `udiv`: traps `int_divz` on a zero divisor. -/
def udiv (x y : BitVec w) : Except TrapCode (BitVec w) :=
  if y = 0 then .error .intDivz else .ok (x / y)

/-- `sdiv`: rounds toward zero; traps `int_divz` on a zero divisor and `int_ovf` on
`MIN / -1`. -/
def sdiv (x y : BitVec w) : Except TrapCode (BitVec w) :=
  if y = 0 then .error .intDivz
  else if x = BitVec.intMin w ∧ y = BitVec.allOnes w then .error .intOvf
  else .ok (x.sdiv y)

/-- `urem`: traps `int_divz` on a zero divisor. -/
def urem (x y : BitVec w) : Except TrapCode (BitVec w) :=
  if y = 0 then .error .intDivz else .ok (x % y)

/-- `srem`: remainder with the sign of the dividend; traps `int_divz` on a zero divisor.
`srem MIN, -1 = 0` (it does not trap). -/
def srem (x y : BitVec w) : Except TrapCode (BitVec w) :=
  if y = 0 then .error .intDivz else .ok (x.srem y)

/-! ## Bitwise -/

def band (x y : BitVec w) : BitVec w := x &&& y
def bor (x y : BitVec w) : BitVec w := x ||| y
def bxor (x y : BitVec w) : BitVec w := x ^^^ y
def bnot (x : BitVec w) : BitVec w := ~~~x

/-- `bitselect c, x, y`: bits of `x` where `c` is set, bits of `y` elsewhere. -/
def bitselect (c x y : BitVec w) : BitVec w := (c &&& x) ||| (~~~c &&& y)

/-! ## Shifts and rotates

The amount `y` may have any integer type; it is taken modulo the width of `x`. -/

/-- Effective shift amount: `y mod w`. -/
def shiftAmt (w : Nat) {v : Nat} (y : BitVec v) : Nat := y.toNat % w

def ishl {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x <<< shiftAmt w y
def ushr {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x >>> shiftAmt w y
def sshr {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x.sshiftRight (shiftAmt w y)
def rotl {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x.rotateLeft (shiftAmt w y)
def rotr {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x.rotateRight (shiftAmt w y)

/-! ## Bit counting -/

/-- `clz`: number of leading zero bits (`w` for zero). -/
def clz (x : BitVec w) : BitVec w := x.clz
/-- `ctz`: number of trailing zero bits (`w` for zero). -/
def ctz (x : BitVec w) : BitVec w := x.ctz
/-- `popcnt`: number of one bits. -/
def popcnt (x : BitVec w) : BitVec w := x.cpop
/-- `cls`: number of leading bits equal to the sign bit, not counting the sign bit. -/
def cls (x : BitVec w) : BitVec w := if x.msb then (~~~x).clz - 1 else x.clz - 1
/-- `bitrev`: reverse the bit order. -/
def bitrev (x : BitVec w) : BitVec w := x.reverse

/-- `bswap`: reverse the byte order (`w` a multiple of 8). Byte `i` of the result is byte
`w/8 - 1 - i` of `x`. -/
def bswap (x : BitVec w) : BitVec w :=
  (List.range (w / 8)).foldl
    (fun acc i => acc ||| (((x >>> (8 * i)) &&& BitVec.ofNat w 0xff) <<< (w - 8 * (i + 1))))
    0

/-! ## Min / max -/

def smin (x y : BitVec w) : BitVec w := if x.sle y then x else y
def smax (x y : BitVec w) : BitVec w := if y.sle x then x else y
def umin (x y : BitVec w) : BitVec w := if x.ule y then x else y
def umax (x y : BitVec w) : BitVec w := if y.ule x then x else y

/-! ## Saturating arithmetic -/

def uaddSat (x y : BitVec w) : BitVec w :=
  if BitVec.uaddOverflow x y then BitVec.allOnes w else x + y
def saddSat (x y : BitVec w) : BitVec w :=
  if BitVec.saddOverflow x y then (if x.msb then BitVec.intMin w else BitVec.intMax w)
  else x + y
def usubSat (x y : BitVec w) : BitVec w := if x.ult y then 0 else x - y
def ssubSat (x y : BitVec w) : BitVec w :=
  if BitVec.ssubOverflow x y then (if x.msb then BitVec.intMin w else BitVec.intMax w)
  else x - y

/-! ## Overflow-flag arithmetic: `(wrapped result, overflow)` -/

def uaddOverflow (x y : BitVec w) : BitVec w × Bool := (x + y, BitVec.uaddOverflow x y)
def saddOverflow (x y : BitVec w) : BitVec w × Bool := (x + y, BitVec.saddOverflow x y)
def usubOverflow (x y : BitVec w) : BitVec w × Bool := (x - y, BitVec.usubOverflow x y)
def ssubOverflow (x y : BitVec w) : BitVec w × Bool := (x - y, BitVec.ssubOverflow x y)
def umulOverflow (x y : BitVec w) : BitVec w × Bool := (x * y, BitVec.umulOverflow x y)
def smulOverflow (x y : BitVec w) : BitVec w × Bool := (x * y, BitVec.smulOverflow x y)

/-- Is `i` representable as a signed `w`-bit integer? -/
def sInRange (w : Nat) (i : Int) : Bool := -(2 ^ (w - 1) : Int) ≤ i && i < 2 ^ (w - 1)

/-- `uadd_overflow_cin`: `x + y + c`; the flag is set iff the exact sum is `≥ 2^w`. -/
def uaddOverflowCin (x y : BitVec w) (c : Bool) : BitVec w × Bool :=
  (x + y + BitVec.ofNat w c.toNat, decide (2 ^ w ≤ x.toNat + y.toNat + c.toNat))

/-- `sadd_overflow_cin`: `x + y + c`; the flag is set iff the exact signed sum is not
representable. -/
def saddOverflowCin (x y : BitVec w) (c : Bool) : BitVec w × Bool :=
  (x + y + BitVec.ofNat w c.toNat,
   !sInRange w (x.toInt + y.toInt + (c.toNat : Int)))

/-- `usub_overflow_bin`: `x - (y + b)`; the flag is set iff the exact difference is
negative. -/
def usubOverflowBin (x y : BitVec w) (b : Bool) : BitVec w × Bool :=
  (x - y - BitVec.ofNat w b.toNat, decide (x.toNat < y.toNat + b.toNat))

/-- `ssub_overflow_bin`: `x - (y + b)`; the flag is set iff the exact signed difference is
not representable. -/
def ssubOverflowBin (x y : BitVec w) (b : Bool) : BitVec w × Bool :=
  (x - y - BitVec.ofNat w b.toNat,
   !sInRange w (x.toInt - y.toInt - (b.toNat : Int)))

/-- `uadd_overflow_trap`: traps with `code` if the unsigned sum overflows. -/
def uaddOverflowTrap (x y : BitVec w) (code : TrapCode) : Except TrapCode (BitVec w) :=
  if BitVec.uaddOverflow x y then .error code else .ok (x + y)

/-! ## Comparisons -/

/-- The truth value of `icmp cc x y`. -/
def intcc (cc : IntCC) (x y : BitVec w) : Bool :=
  match cc with
  | .eq => x == y
  | .ne => x != y
  | .slt => x.slt y
  | .sge => y.sle x
  | .sgt => y.slt x
  | .sle => x.sle y
  | .ult => x.ult y
  | .uge => y.ule x
  | .ugt => y.ult x
  | .ule => x.ule y

/-- CLIF booleans are `i8` 0/1. -/
def bool8 (b : Bool) : BitVec 8 := if b then 1#8 else 0#8

/-- `icmp cc x y`: `i8` 1 if the condition holds, else 0. -/
def icmp (cc : IntCC) (x y : BitVec w) : BitVec 8 := bool8 (intcc cc x y)

/-- Truthiness of a condition operand (`brif`, `select`, `trapz`, `bmask`): non-zero. -/
def truthy (x : BitVec w) : Bool := x != 0

/-- `select c, x, y`. -/
def select {v : Nat} (c : BitVec v) (x y : BitVec w) : BitVec w := if truthy c then x else y

/-- `bmask x`: all ones if `x` is non-zero, else zero. -/
def bmask {v : Nat} (x : BitVec v) : BitVec w := if truthy x then BitVec.allOnes w else 0

/-! ## Width changes -/

/-- `uextend`: zero-extend to width `v` (`v > w`). -/
def uextend (v : Nat) (x : BitVec w) : BitVec v := x.zeroExtend v
/-- `sextend`: sign-extend to width `v` (`v > w`). -/
def sextend (v : Nat) (x : BitVec w) : BitVec v := x.signExtend v
/-- `ireduce`: keep the low `v` bits (`v < w`). -/
def ireduce (v : Nat) (x : BitVec w) : BitVec v := x.setWidth v
/-- `iconcat lo, hi`: `hi` in the upper half. -/
def iconcat (lo hi : BitVec w) : BitVec (w + w) := hi ++ lo
/-- `isplit x` with half width `v` (`w = v + v`): `(low half, high half)`. -/
def isplit (v : Nat) (x : BitVec w) : BitVec v × BitVec v := (x.extractLsb' 0 v, x.extractLsb' v v)

/-! ## Atomics (single-threaded: a load followed by a store) -/

/-- The value `atomic_rmw op` stores, given the old memory value and the operand. -/
def atomicRmw (op : AtomicRmwOp) (old x : BitVec w) : BitVec w :=
  match op with
  | .add => old + x | .sub => old - x | .and => old &&& x | .nand => ~~~(old &&& x)
  | .or => old ||| x | .xor => old ^^^ x | .xchg => x
  | .umin => umin old x | .umax => umax old x | .smin => smin old x | .smax => smax old x

/-! ## Opcode dispatch on `BitVec` -/

def unary (op : UnaryOp) (x : BitVec w) : BitVec w :=
  match op with
  | .ineg => ineg x | .bnot => bnot x | .iabs => iabs x | .clz => clz x | .ctz => ctz x
  | .cls => cls x | .popcnt => popcnt x | .bitrev => bitrev x | .bswap => bswap x

/-- Binary operations where both operands have the controlling type. -/
def binary (op : BinaryOp) (x y : BitVec w) : BitVec w :=
  match op with
  | .iadd => iadd x y | .isub => isub x y | .imul => imul x y
  | .umulhi => umulhi x y | .smulhi => smulhi x y
  | .band => band x y | .bor => bor x y | .bxor => bxor x y
  | .ishl => ishl x y | .ushr => ushr x y | .sshr => sshr x y
  | .rotl => rotl x y | .rotr => rotr x y
  | .smin => smin x y | .smax => smax x y | .umin => umin x y | .umax => umax x y
  | .uaddSat => uaddSat x y | .saddSat => saddSat x y
  | .usubSat => usubSat x y | .ssubSat => ssubSat x y

/-- Shift/rotate with an amount of a different width. -/
def shift (op : BinaryOp) {v : Nat} (x : BitVec w) (y : BitVec v) : Option (BitVec w) :=
  match op with
  | .ishl => some (ishl x y) | .ushr => some (ushr x y) | .sshr => some (sshr x y)
  | .rotl => some (rotl x y) | .rotr => some (rotr x y)
  | _ => none

def _root_.Clif.BinaryOp.isShift : BinaryOp → Bool
  | .ishl | .ushr | .sshr | .rotl | .rotr => true
  | _ => false

def div (op : DivOp) (x y : BitVec w) : Except TrapCode (BitVec w) :=
  match op with
  | .udiv => udiv x y | .sdiv => sdiv x y | .urem => urem x y | .srem => srem x y

def overflow (op : OverflowOp) (x y : BitVec w) : BitVec w × Bool :=
  match op with
  | .uaddOverflow => uaddOverflow x y | .saddOverflow => saddOverflow x y
  | .usubOverflow => usubOverflow x y | .ssubOverflow => ssubOverflow x y
  | .umulOverflow => umulOverflow x y | .smulOverflow => smulOverflow x y

def carry (op : CarryOp) (x y : BitVec w) (c : Bool) : BitVec w × Bool :=
  match op with
  | .uaddOverflowCin => uaddOverflowCin x y c | .saddOverflowCin => saddOverflowCin x y c
  | .usubOverflowBin => usubOverflowBin x y c | .ssubOverflowBin => ssubOverflowBin x y c

end Clif.Sem

import FV.Backend.Asm

/-!
# `Inst::load_constant`: Cranelift's constant load, case by case

`loadConstLines rd value` is the instruction sequence of Cranelift's
`Inst::load_constant(rd, value)` (`isa/aarch64/inst/mod.rs`, `pub fn load_constant`), with the
same signature as `loadConst64` (`FV/Backend/Asm.lean`; `value` is taken mod 2^64). Its cases,
in Cranelift's order:

1. `MoveWideConst::maybe_from_u64(value)` (at most one nonzero halfword; 0 gives `movz #0`):
   one `movz xd, #imm16, lsl #16*k`;
2. else `MoveWideConst::maybe_from_u64(!value)`: one `movn xd, #imm16, lsl #16*k`;
3. else `ImmLogic::maybe_from_u64(value, I64)`: one `orr xd, xzr, #value` (the
   `AluRRImmLogic { alu_op: Orr, size: Size64, rn: zero_reg() }` that `MInst.lines` expands
   to `.logicImm .orr true rd .xzr (mask64 value)`);
4. else: the 32-bit forms (`OperandSize::Size32`, 2 halfwords) when `value >> 32 == 0`,
   otherwise the 64-bit forms (4 halfwords); the first instruction is `movn` when the
   (operand-size) complement has more zero halfwords than `value` (`first_is_inverted`),
   otherwise `movz`; the halfwords equal to `0xffff` (after `movn`) or `0` (after `movz`)
   are skipped; the first kept halfword is the `movz`/`movn` (`movn` with `!imm16 & 0xffff`),
   the others are `movk` at their shift.

The helpers `MoveWideConst.ofNat?` and `ImmLogic.ofNat?` (`FV/Backend/MInst.lean`) are the
Lean models of `MoveWideConst::maybe_from_u64` and `ImmLogic::maybe_from_u64` that the
instruction selector already uses.

Phase 1 of AG-2j (#554): the definition and its proofs (`FV/Backend/Proof/LoadConstant.lean`)
are new leaf modules; `loadConst64` is unchanged.
-/

namespace Backend

/-- Halfword `i` of `v`: `(value >> (16 * i)) & 0xffff`. -/
def halfword (v i : Nat) : Nat := (v / 2 ^ (16 * i)) % 2 ^ 16

/-- `count_zero_half_words(value, num_half_words)` (`inst/mod.rs`): the number of zero
halfwords among the low `n`. -/
def countZeroHalfWords (v n : Nat) : Nat :=
  ((List.range n).filter fun i => halfword v i == 0).length

/-- The kept `(i, imm16)` pairs of `load_constant`'s general case: the halfwords `i < n` of `v`
that are not `ignored`, in increasing `i` (the `filter_map` over `0..num_half_words`). -/
def keptHalfwords (v n ignored : Nat) : List (Nat × Nat) :=
  (List.range n).filterMap fun i =>
    if halfword v i == ignored then none else some (i, halfword v i)

/-- The lines of `load_constant`'s general case for the kept halfwords: the first is
`movn` (with `!imm16 & 0xffff`) when `inv` (`first_is_inverted`), otherwise `movz`; the rest
are `movk`; all at the operand size `is64`. -/
def movSeqLines (rd : Reg) (is64 inv : Bool) : List (Nat × Nat) → List Line
  | [] => []
  | (i, c) :: rest =>
    .ins (if inv then .movWide .movN is64 rd ⟨2 ^ 16 - 1 - c, i⟩
          else .movWide .movZ is64 rd ⟨c, i⟩) ::
      rest.map fun p => .ins (.movk is64 rd ⟨p.2, p.1⟩)

/-- `load_constant`'s general case (the `else` branch) for `value < 2^64`: the 32-bit forms
(2 halfwords) when `value >> 32 == 0`, else the 64-bit forms (4 halfwords); `movn` first when
the complement at that size (`negated`) has more zero halfwords than `value`; the halfwords
equal to the ignored one (`0xffff` after `movn`, `0` after `movz`) are skipped. -/
def generalLines (rd : Reg) (value : Nat) : List Line :=
  -- `if value >> 32 == 0 { (2, Size32, (!value << 32) >> 32) } else { (4, Size64, !value) }`
  let is64 : Bool := 2 ^ 32 ≤ value
  let n := if is64 then 4 else 2
  let negated := if is64 then 2 ^ 64 - 1 - value else 2 ^ 32 - 1 - value
  let inv : Bool := countZeroHalfWords value n < countZeroHalfWords negated n
  movSeqLines rd is64 inv (keptHalfwords value n (if inv then 2 ^ 16 - 1 else 0))

/-- **`Inst::load_constant(rd, value)`** (`isa/aarch64/inst/mod.rs`), with `value` taken mod
2^64. -/
def loadConstLines (rd : Reg) (value : Nat) : List Line :=
  let value := mask64 value
  match MoveWideConst.ofNat? value with
  | some imm => [.ins (.movWide .movZ true rd imm)]
  | none =>
  match MoveWideConst.ofNat? (2 ^ 64 - 1 - value) with
  | some imm => [.ins (.movWide .movN true rd imm)]
  | none =>
  match ImmLogic.ofNat? value .size64 with
  | some _ => [.ins (.logicImm .orr true rd .xzr value)]
  | none => generalLines rd value

end Backend

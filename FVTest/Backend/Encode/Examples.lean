import FV.Backend.Encode

/-!
# `decode (encode i) = i` on concrete instructions, checked by the kernel

Instances of the M5 statement (`docs/contracts/encoder.md`, "Planned theorem") proven by
`decide`: the kernel evaluates `Insn.toArmInst`, `armBits` and `decode_raw_inst`. One per
encoding class the backend emits (register 31 in its SP and ZR roles, a negative branch
offset, a relocated form). The general, operand-quantified versions are the M5 proof work.
-/

namespace Backend.EncodeExamples

open Backend

/-- No labels; the instruction at offset 0. -/
def env0 : Env := ⟨0, fun _ => none⟩

/-- At offset 64, block 1 at offset 16 (a backward branch), block 2 at 128. -/
def envB : Env := ⟨64, fun | .block 1 => some 16 | .block 2 => some 128 | _ => none⟩

-- Add/subtract (immediate): `add x0, sp, #16`, `subs wzr, w3, #1, lsl #12`
example : (Insn.aluImm12 .add true (.x 0) .sp ⟨16, false⟩).decodeOk env0 = true := by decide
example : (Insn.aluImm12 .subS false .xzr (.x 3) ⟨1, true⟩).decodeOk env0 = true := by decide
-- Logical (immediate): `and w1, w2, #0x1`, `orr x5, xzr, #0xff00ff00ff00ff00`
example : (Insn.logicImm .and false (.x 1) (.x 2) 1).decodeOk env0 = true := by decide
example : (Insn.logicImm .orr true (.x 5) .xzr 0xff00ff00ff00ff00).decodeOk env0 = true := by
  decide
-- Move wide, bitfield, extract
example : (Insn.movWide .movZ true (.x 16) ⟨0x1234, 3⟩).decodeOk env0 = true := by decide
example : (Insn.shiftImm .lsl false (.x 9) (.x 10) 3).decodeOk env0 = true := by decide
example : (Insn.extr true (.x 1) (.x 2) (.x 3) 17).decodeOk env0 = true := by decide
-- Data processing (register)
example : (Insn.aluRRR .subS true .xzr (.x 9) (.x 10)).decodeOk env0 = true := by decide
example : (Insn.aluRRR .sDiv false (.x 9) (.x 10) (.x 11)).decodeOk env0 = true := by decide
example : (Insn.aluRRRR .mSub true (.x 9) (.x 10) (.x 11) (.x 12)).decodeOk env0 = true := by
  decide
example : (Insn.aluRRRExtend .sub true .sp .sp (.x 16) .uxtx).decodeOk env0 = true := by decide
example : (Insn.cset (.x 9) .hs).decodeOk env0 = true := by decide
example : (Insn.ccmpImm true (.x 9) 1 ⟨false, false, false, false⟩ .eq).decodeOk env0 = true := by
  decide
-- Loads and stores: `ldur x9, [sp, #-8]`, `ldrsw x10, [x9, w10, uxtw #2]`, `stp` pre-index
example : (Insn.load .uload64 (.x 9) (.unscaled .sp (-8))).decodeOk env0 = true := by decide
example : (Insn.load .sload32 (.x 10) (.regScaledExtended (.x 9) (.x 10) .uxtw)).decodeOk env0
    = true := by decide
example : (Insn.stp (.x 29) (.x 30) (.spPreIndexed (-16))).decodeOk env0 = true := by decide
-- Branches: backward `b.eq`, forward `cbnz`, `tbz`, `ret`, `udf`
example : (Insn.bcond .eq (.block 1)).decodeOk envB = true := by decide
example : (Insn.cbz true false (.x 9) (.block 2)).decodeOk envB = true := by decide
example : (Insn.tbz false (.x 9) 40 (.block 1)).decodeOk envB = true := by decide
example : Insn.ret.decodeOk env0 = true := by decide
example : (Insn.udf 0xc11f).decodeOk env0 = true := by decide
-- PC-relative and relocated: `adr`, `adrp :got:`, `bl`
example : (Insn.adr (.x 9) (.block 2)).decodeOk envB = true := by decide
example : (Insn.adrpGot (.x 9) "f").decodeOk env0 = true := by decide
example : (Insn.bl "f").decodeOk env0 = true := by decide
-- SIMD&FP: `fmov d16, x9`, `cnt v16.8b, v16.8b`, `umov w9, v16.b[0]`
example : (Insn.fmovToFp .size64 (.v 16) (.x 9)).decodeOk env0 = true := by decide
example : (Insn.cnt .size8x8 (.v 16) (.v 16)).decodeOk env0 = true := by decide
example : (Insn.umov .size8 (.x 9) (.v 16) 0).decodeOk env0 = true := by decide

/-- Encoding is checked, not just decoded: the word for `stp x29, x30, [sp, #-16]!` is
`0xa9bf7bfd` (the value in `FV/Arm/Decode.lean`'s own examples and `llvm-mc`'s). -/
example : ((Insn.stp (.x 29) (.x 30) (.spPreIndexed (-16))).encode env0).toOption =
    some 0xa9bf7bfd#32 := by
  decide

/-- Invalid operands are rejected: `xzr` as the base of `add (immediate)` is not encodable
(register 31 is SP there). -/
example : ((Insn.aluImm12 .add true (.x 0) .xzr ⟨1, false⟩).encode env0).toOption = none := by
  decide

end Backend.EncodeExamples

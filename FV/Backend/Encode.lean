import FV.Backend.Asm
import FV.Arm.Decode

/-!
# Machine-code encoder (M5, proven against the Arm model's decoder)

`Insn.encode env i = armBits <$> Insn.toArmInst env i`:

* `Insn.toArmInst` gives the **field values** of an instruction: the encoding class of the Lean
  Arm model (`Arm.ArmInst`, the type `Arm.decode_raw_inst` returns) and each field, as the
  instruction's page in the Arm ARM (DDI 0487, chapter C6 "A64 Base Instruction Descriptions",
  chapter C7 "A64 Advanced SIMD and Floating-point Instruction Descriptions") fixes them, with
  aliases translated per their "Alias conditions"/"is equivalent to" rules. Operand
  constraints (register 31 as SP or ZR, immediate ranges, branch ranges) are checked here.
  (`Insn.armFields` builds the structure literals; `toArmInst` = `ArmInst.norm <$> armFields`.)
* `armBits` concatenates the fields of an encoding class in the order of the class's
  encoding diagram (Arm ARM C4.1 "A64 instruction set encoding").

M5 theorem (`FV/Backend/Proof/Encode.lean`): `Insn.decode_encode` —
`i.encode env = .ok w → ∃ a, i.toArmInst env = .ok a ∧ decode_raw_inst w = some a`, for every
`Insn` and position. Layout correctness and the branch-range policy:
`FV/Backend/Proof/EncodeLayout.lean`, `EncodeBranch.lean`; the `stepi` link:
`EncodeStep.lean`. `Insn.decodeOk` is the executable form (`lean-backend-encode-test decode`).

Relocatable operands (`bl`, `adrp`, `:got_lo12:`, `:lo12:`) are encoded with a zero
immediate; `Insn.reloc?` gives the ELF relocation (`R_AARCH64_*`, RELA addend), which is what
`llvm-mc` emits for them. Cross-checked with Cranelift's `enc_*` functions in
`cranelift/codegen/src/isa/aarch64/inst/emit.rs` (noted per form below).
-/

namespace Backend

open Arm

/-! ## Operand fields -/

/-- A general-purpose register where encoding 31 means the zero register. -/
def Reg.encZR : Reg → Except String (BitVec 5)
  | .x n => if n ≤ 30 then pure (BitVec.ofNat 5 n) else throw s!"x{n} is not a register"
  | .xzr => pure 31#5
  | r => throw s!"{repr r} where a GPR or ZR is required"

/-- A general-purpose register where encoding 31 means the stack pointer. -/
def Reg.encSP : Reg → Except String (BitVec 5)
  | .x n => if n ≤ 30 then pure (BitVec.ofNat 5 n) else throw s!"x{n} is not a register"
  | .sp => pure 31#5
  | r => throw s!"{repr r} where a GPR or SP is required"

/-- A SIMD&FP register. -/
def Reg.encV : Reg → Except String (BitVec 5)
  | .v n => if n ≤ 31 then pure (BitVec.ofNat 5 n) else throw s!"v{n} is not a register"
  | r => throw s!"{repr r} where a SIMD&FP register is required"

/-- `cond` field (the `Cond` constructors are in hardware order; Arm ARM chapter C1, "Condition code" table). -/
def Cond.bits : Cond → BitVec 4
  | .eq => 0 | .ne => 1 | .hs => 2 | .lo => 3 | .mi => 4 | .pl => 5 | .vs => 6 | .vc => 7
  | .hi => 8 | .ls => 9 | .ge => 10 | .lt => 11 | .gt => 12 | .le => 13 | .al => 14 | .nv => 15

/-- `option` field of extended-register operands (Arm ARM `DecodeRegExtend`). -/
def ExtendOp.bits : ExtendOp → BitVec 3
  | .uxtb => 0 | .uxth => 1 | .uxtw => 2 | .uxtx => 3
  | .sxtb => 4 | .sxth => 5 | .sxtw => 6 | .sxtx => 7

def b1 (b : Bool) : BitVec 1 := if b then 1#1 else 0#1

/-- `n` as an unsigned field of `w` bits, or an error. -/
def uField (what : String) (w n : Nat) : Except String (BitVec w) :=
  if n < 2 ^ w then pure (BitVec.ofNat w n) else throw s!"{what} {n} does not fit in {w} bits"

/-- `i` as a signed field of `w` bits, or an error. -/
def sField (what : String) (w : Nat) (i : Int) : Except String (BitVec w) :=
  if -(2 ^ (w - 1) : Int) ≤ i ∧ i < 2 ^ (w - 1) then pure (BitVec.ofInt w i)
  else throw s!"{what} {i} does not fit in {w} signed bits"

/-- Rotate the `e`-bit value `x` right by `r`. -/
def rorN (e x r : Nat) : Nat := (x >>> r) ||| ((x <<< (e - r)) % 2 ^ e)

/-- `N:immr:imms` of a bitmask immediate for `value` at 32 or 64 bits: the inverse of the
Arm ARM's `DecodeBitMasks` (shared pseudocode `aarch64/instrs/integer/bitmasks`): the value is
the replication of an `e`-bit element (smallest `e`, 2 ≤ e ≤ size) that is `ROR(Ones(c), r)`
with `0 < c < e`; then `N = (e = 64)`, `immr = r`, `imms = NOT(2e-1)<5:0> OR (c-1)`. The same
search as Cranelift's `ImmLogic::maybe_from_u64` (`inst/imms.rs`). The encoding is unique:
an element of twice the minimal period consists of two runs. -/
def bitmaskEnc? (is64 : Bool) (value : Nat) : Option (BitVec 1 × BitVec 6 × BitVec 6) :=
  let size := if is64 then 64 else 32
  if value ≥ 2 ^ size then none else
  let rep (e : Nat) : Nat :=
    (List.range (size / e)).foldl (fun acc i => acc + (value % 2 ^ e) * 2 ^ (e * i)) 0
  match [2, 4, 8, 16, 32, 64].find? (fun e => e ≤ size && rep e == value) with
  | none => none
  | some e =>
    let elem := value % 2 ^ e
    let c := (List.range e).foldl (fun n i => if elem.testBit i then n + 1 else n) 0
    if c == 0 || c == e then none else
    match (List.range e).find? (fun r => rorN e (2 ^ c - 1) r == elem) with
    | none => none
    | some r =>
      some (b1 (e == 64), BitVec.ofNat 6 r,
            BitVec.ofNat 6 (if e == 64 then c - 1 else (64 - 2 * e) + (c - 1)))

/-! ## Encoding classes (Arm ARM C4.1 encoding diagrams) -/

/-- The 32-bit word of a decoded instruction: the fields of its class concatenated from bit
31 down to bit 0, with the class's fixed bits written out, as in the class's encoding diagram
in Arm ARM C4.1 (class names are the model's, after the C4.1 headings). The model structures'
`_fixed` fields are not read (the decoder always fills them with their defaults). -/
def armBits : ArmInst → BitVec 32
  -- C4.1 Data Processing -- Immediate
  | .DPI (.Add_sub_imm x) => x.sf ++ x.op ++ x.S ++ 0b100010#6 ++ x.sh ++ x.imm12 ++ x.Rn ++ x.Rd
  | .DPI (.Logical_imm x) => x.sf ++ x.opc ++ 0b100100#6 ++ x.N ++ x.immr ++ x.imms ++ x.Rn ++ x.Rd
  | .DPI (.PC_rel_addressing x) => x.op ++ x.immlo ++ 0b10000#5 ++ x.immhi ++ x.Rd
  | .DPI (.Bitfield x) => x.sf ++ x.opc ++ 0b100110#6 ++ x.N ++ x.immr ++ x.imms ++ x.Rn ++ x.Rd
  | .DPI (.Move_wide_imm x) => x.sf ++ x.opc ++ 0b100101#6 ++ x.hw ++ x.imm16 ++ x.Rd
  | .DPI (.Extract x) =>
    x.sf ++ x.op21 ++ 0b100111#6 ++ x.N ++ x.o0 ++ x.Rm ++ x.imms ++ x.Rn ++ x.Rd
  -- C4.1 Branches, Exception Generating and System instructions
  | .BR (.Compare_branch x) => x.sf ++ 0b011010#6 ++ x.op ++ x.imm19 ++ x.Rt
  | .BR (.Uncond_branch_imm x) => x.op ++ 0b00101#5 ++ x.imm26
  | .BR (.Uncond_branch_reg x) => 0b1101011#7 ++ x.opc ++ x.op2 ++ x.op3 ++ x.Rn ++ x.op4
  | .BR (.Cond_branch_imm x) => 0b01010100#8 ++ x.imm19 ++ x.o0 ++ x.cond
  | .BR (.Hints x) => 0b11010101000000110010#20 ++ x.CRm ++ x.op2 ++ 0b11111#5
  | .BR (.Barrier x) => 0b11010101000000110011#20 ++ x.CRm ++ x.op2 ++ 0b11111#5
  | .BR (.Test_branch x) => x.b5 ++ 0b011011#6 ++ x.op ++ x.b40 ++ x.imm14 ++ x.Rt
  | .BR (.Mrs x) => 0b110101010011#12 ++ x.o0 ++ x.op1 ++ x.CRn ++ x.CRm ++ x.op2 ++ x.Rt
  -- C4.1 Data Processing -- Register
  | .DPR (.Add_sub_carry x) =>
    x.sf ++ x.op ++ x.S ++ 0b11010000#8 ++ x.Rm ++ 0b000000#6 ++ x.Rn ++ x.Rd
  | .DPR (.Add_sub_shifted_reg x) =>
    x.sf ++ x.op ++ x.S ++ 0b01011#5 ++ x.shift ++ 0#1 ++ x.Rm ++ x.imm6 ++ x.Rn ++ x.Rd
  | .DPR (.Conditional_select x) =>
    x.sf ++ x.op ++ x.S ++ 0b11010100#8 ++ x.Rm ++ x.cond ++ x.op2 ++ x.Rn ++ x.Rd
  | .DPR (.Data_processing_one_source x) =>
    x.sf ++ 1#1 ++ x.S ++ 0b11010110#8 ++ x.opcode2 ++ x.opcode ++ x.Rn ++ x.Rd
  | .DPR (.Data_processing_two_source x) =>
    x.sf ++ 0#1 ++ x.S ++ 0b11010110#8 ++ x.Rm ++ x.opcode ++ x.Rn ++ x.Rd
  | .DPR (.Logical_shifted_reg x) =>
    x.sf ++ x.opc ++ 0b01010#5 ++ x.shift ++ x.N ++ x.Rm ++ x.imm6 ++ x.Rn ++ x.Rd
  | .DPR (.Data_processing_three_source x) =>
    x.sf ++ x.op54 ++ 0b11011#5 ++ x.op31 ++ x.Rm ++ x.o0 ++ x.Ra ++ x.Rn ++ x.Rd
  | .DPR (.Add_sub_ext_reg x) =>
    x.sf ++ x.op ++ x.S ++ 0b01011#5 ++ x.opt ++ 1#1 ++ x.Rm ++ x.option ++ x.imm3 ++ x.Rn ++ x.Rd
  | .DPR (.Conditional_compare_imm x) =>
    x.sf ++ x.op ++ x.S ++ 0b11010010#8 ++ x.imm5 ++ x.cond ++ 1#1 ++ x.o2 ++ x.Rn ++ x.o3 ++ x.nzcv
  | .DPR (.Conditional_compare_reg x) =>
    x.sf ++ x.op ++ x.S ++ 0b11010010#8 ++ x.Rm ++ x.cond ++ 0#1 ++ x.o2 ++ x.Rn ++ x.o3 ++ x.nzcv
  -- C4.1 Data Processing -- Scalar Floating-Point and Advanced SIMD
  | .DPSFP (.Advanced_simd_two_reg_misc x) =>
    0#1 ++ x.Q ++ x.U ++ 0b01110#5 ++ x.size ++ 0b10000#5 ++ x.opcode ++ 0b10#2 ++ x.Rn ++ x.Rd
  | .DPSFP (.Advanced_simd_copy x) =>
    0#1 ++ x.Q ++ x.op ++ 0b01110000#8 ++ x.imm5 ++ 0#1 ++ x.imm4 ++ 1#1 ++ x.Rn ++ x.Rd
  | .DPSFP (.Advanced_simd_three_same x) =>
    0#1 ++ x.Q ++ x.U ++ 0b01110#5 ++ x.size ++ 1#1 ++ x.Rm ++ x.opcode ++ 1#1 ++ x.Rn ++ x.Rd
  | .DPSFP (.Conversion_between_FP_and_Int x) =>
    x.sf ++ 0#1 ++ x.S ++ 0b11110#5 ++ x.ftype ++ 1#1 ++ x.rmode ++ x.opcode ++ 0b000000#6 ++
      x.Rn ++ x.Rd
  | .DPSFP (.Advanced_simd_across_lanes x) =>
    0#1 ++ x.Q ++ x.U ++ 0b01110#5 ++ x.size ++ 0b11000#5 ++ x.opcode ++ 0b10#2 ++ x.Rn ++ x.Rd
  -- C4.1 Loads and Stores
  | .LDST (.Reg_imm_post_indexed x) =>
    x.size ++ 0b111#3 ++ x.V ++ 0b00#2 ++ x.opc ++ 0#1 ++ x.imm9 ++ 0b01#2 ++ x.Rn ++ x.Rt
  | .LDST (.Reg_unsigned_imm x) =>
    x.size ++ 0b111#3 ++ x.V ++ 0b01#2 ++ x.opc ++ x.imm12 ++ x.Rn ++ x.Rt
  | .LDST (.Reg_unscaled_imm x) =>
    x.size ++ 0b111#3 ++ x.VR ++ 0b00#2 ++ x.opc ++ 0#1 ++ x.imm9 ++ 0b00#2 ++ x.Rn ++ x.Rt
  | .LDST (.Reg_pair_pre_indexed x) =>
    x.opc ++ 0b101#3 ++ x.V ++ 0b011#3 ++ x.L ++ x.imm7 ++ x.Rt2 ++ x.Rn ++ x.Rt
  | .LDST (.Reg_pair_post_indexed x) =>
    x.opc ++ 0b101#3 ++ x.V ++ 0b001#3 ++ x.L ++ x.imm7 ++ x.Rt2 ++ x.Rn ++ x.Rt
  | .LDST (.Reg_pair_signed_offset x) =>
    x.opc ++ 0b101#3 ++ x.V ++ 0b010#3 ++ x.L ++ x.imm7 ++ x.Rt2 ++ x.Rn ++ x.Rt
  | .LDST (.Reg_imm_pre_indexed x) =>
    x.size ++ 0b111#3 ++ x.V ++ 0b00#2 ++ x.opc ++ 0#1 ++ x.imm9 ++ 0b11#2 ++ x.Rn ++ x.Rt
  | .LDST (.Reg_reg_offset x) =>
    x.size ++ 0b111#3 ++ x.V ++ 0b00#2 ++ x.opc ++ 1#1 ++ x.Rm ++ x.option ++ x.S ++ 0b10#2 ++
      x.Rn ++ x.Rt
  | .LDST (.Reg_exclusive x) =>
    x.size ++ 0b001000#6 ++ x.ord ++ x.L ++ 0#1 ++ x.Rs ++ x.o0 ++ 0b11111#5 ++ x.Rn ++ x.Rt
  -- C4.1 Reserved: UDF
  | .RES (.Udf x) => 0#16 ++ x.imm16

/-- `a` with every `_fixed` field reset to the value the decoder puts there (the structure's
default): the fields `armBits` ignores. Identity on every value `Insn.armFields` builds (they
are structure literals that leave `_fixed` at its default); `decode_raw_inst (armBits a) =
some a.norm` for every `a` (`Backend.decode_armBits`, `FV/Backend/Proof/Encode.lean`). -/
def _root_.Arm.ArmInst.norm : ArmInst → ArmInst
  | .DPI (.Add_sub_imm x) =>
    .DPI (.Add_sub_imm { sf := x.sf, op := x.op, S := x.S, sh := x.sh, imm12 := x.imm12,
                         Rn := x.Rn, Rd := x.Rd })
  | .DPI (.Logical_imm x) =>
    .DPI (.Logical_imm { sf := x.sf, opc := x.opc, N := x.N, immr := x.immr, imms := x.imms,
                         Rn := x.Rn, Rd := x.Rd })
  | .DPI (.PC_rel_addressing x) =>
    .DPI (.PC_rel_addressing { op := x.op, immlo := x.immlo, immhi := x.immhi, Rd := x.Rd })
  | .DPI (.Bitfield x) =>
    .DPI (.Bitfield { sf := x.sf, opc := x.opc, N := x.N, immr := x.immr, imms := x.imms,
                      Rn := x.Rn, Rd := x.Rd })
  | .DPI (.Move_wide_imm x) =>
    .DPI (.Move_wide_imm { sf := x.sf, opc := x.opc, hw := x.hw, imm16 := x.imm16, Rd := x.Rd })
  | .DPI (.Extract x) =>
    .DPI (.Extract { sf := x.sf, op21 := x.op21, N := x.N, o0 := x.o0, Rm := x.Rm,
                     imms := x.imms, Rn := x.Rn, Rd := x.Rd })
  | .BR (.Compare_branch x) =>
    .BR (.Compare_branch { sf := x.sf, op := x.op, imm19 := x.imm19, Rt := x.Rt })
  | .BR (.Uncond_branch_imm x) => .BR (.Uncond_branch_imm { op := x.op, imm26 := x.imm26 })
  | .BR (.Uncond_branch_reg x) =>
    .BR (.Uncond_branch_reg { opc := x.opc, op2 := x.op2, op3 := x.op3, Rn := x.Rn, op4 := x.op4 })
  | .BR (.Cond_branch_imm x) =>
    .BR (.Cond_branch_imm { imm19 := x.imm19, o0 := x.o0, cond := x.cond })
  | .BR (.Hints x) => .BR (.Hints { CRm := x.CRm, op2 := x.op2 })
  | .BR (.Barrier x) => .BR (.Barrier { CRm := x.CRm, op2 := x.op2 })
  | .BR (.Test_branch x) =>
    .BR (.Test_branch { b5 := x.b5, op := x.op, b40 := x.b40, imm14 := x.imm14, Rt := x.Rt })
  | .BR (.Mrs x) =>
    .BR (.Mrs { o0 := x.o0, op1 := x.op1, CRn := x.CRn, CRm := x.CRm, op2 := x.op2, Rt := x.Rt })
  | .DPR (.Add_sub_carry x) =>
    .DPR (.Add_sub_carry { sf := x.sf, op := x.op, S := x.S, Rm := x.Rm, Rn := x.Rn, Rd := x.Rd })
  | .DPR (.Add_sub_shifted_reg x) =>
    .DPR (.Add_sub_shifted_reg { sf := x.sf, op := x.op, S := x.S, shift := x.shift, Rm := x.Rm,
                                 imm6 := x.imm6, Rn := x.Rn, Rd := x.Rd })
  | .DPR (.Add_sub_ext_reg x) =>
    .DPR (.Add_sub_ext_reg { sf := x.sf, op := x.op, S := x.S, opt := x.opt, Rm := x.Rm,
                             option := x.option, imm3 := x.imm3, Rn := x.Rn, Rd := x.Rd })
  | .DPR (.Conditional_compare_imm x) =>
    .DPR (.Conditional_compare_imm { sf := x.sf, op := x.op, S := x.S, imm5 := x.imm5,
                                     cond := x.cond, o2 := x.o2, Rn := x.Rn, o3 := x.o3,
                                     nzcv := x.nzcv })
  | .DPR (.Conditional_compare_reg x) =>
    .DPR (.Conditional_compare_reg { sf := x.sf, op := x.op, S := x.S, Rm := x.Rm,
                                     cond := x.cond, o2 := x.o2, Rn := x.Rn, o3 := x.o3,
                                     nzcv := x.nzcv })
  | .DPR (.Conditional_select x) =>
    .DPR (.Conditional_select { sf := x.sf, op := x.op, S := x.S, Rm := x.Rm, cond := x.cond,
                                op2 := x.op2, Rn := x.Rn, Rd := x.Rd })
  | .DPR (.Data_processing_one_source x) =>
    .DPR (.Data_processing_one_source { sf := x.sf, S := x.S, opcode2 := x.opcode2,
                                        opcode := x.opcode, Rn := x.Rn, Rd := x.Rd })
  | .DPR (.Data_processing_two_source x) =>
    .DPR (.Data_processing_two_source { sf := x.sf, S := x.S, Rm := x.Rm, opcode := x.opcode,
                                        Rn := x.Rn, Rd := x.Rd })
  | .DPR (.Logical_shifted_reg x) =>
    .DPR (.Logical_shifted_reg { sf := x.sf, opc := x.opc, shift := x.shift, N := x.N,
                                 Rm := x.Rm, imm6 := x.imm6, Rn := x.Rn, Rd := x.Rd })
  | .DPR (.Data_processing_three_source x) =>
    .DPR (.Data_processing_three_source { sf := x.sf, op54 := x.op54, op31 := x.op31,
                                          Rm := x.Rm, o0 := x.o0, Ra := x.Ra, Rn := x.Rn,
                                          Rd := x.Rd })
  | .DPSFP (.Advanced_simd_two_reg_misc x) =>
    .DPSFP (.Advanced_simd_two_reg_misc { Q := x.Q, U := x.U, size := x.size,
                                          opcode := x.opcode, Rn := x.Rn, Rd := x.Rd })
  | .DPSFP (.Advanced_simd_copy x) =>
    .DPSFP (.Advanced_simd_copy { Q := x.Q, op := x.op, imm5 := x.imm5, imm4 := x.imm4,
                                  Rn := x.Rn, Rd := x.Rd })
  | .DPSFP (.Advanced_simd_three_same x) =>
    .DPSFP (.Advanced_simd_three_same { Q := x.Q, U := x.U, size := x.size, Rm := x.Rm,
                                        opcode := x.opcode, Rn := x.Rn, Rd := x.Rd })
  | .DPSFP (.Conversion_between_FP_and_Int x) =>
    .DPSFP (.Conversion_between_FP_and_Int { sf := x.sf, S := x.S, ftype := x.ftype,
                                             rmode := x.rmode, opcode := x.opcode, Rn := x.Rn,
                                             Rd := x.Rd })
  | .DPSFP (.Advanced_simd_across_lanes x) =>
    .DPSFP (.Advanced_simd_across_lanes { Q := x.Q, U := x.U, size := x.size,
                                          opcode := x.opcode, Rn := x.Rn, Rd := x.Rd })
  | .LDST (.Reg_imm_post_indexed x) =>
    .LDST (.Reg_imm_post_indexed { size := x.size, V := x.V, opc := x.opc, imm9 := x.imm9,
                                   Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_unsigned_imm x) =>
    .LDST (.Reg_unsigned_imm { size := x.size, V := x.V, opc := x.opc, imm12 := x.imm12,
                               Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_unscaled_imm x) =>
    .LDST (.Reg_unscaled_imm { size := x.size, VR := x.VR, opc := x.opc, imm9 := x.imm9,
                               Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_pair_pre_indexed x) =>
    .LDST (.Reg_pair_pre_indexed { opc := x.opc, V := x.V, L := x.L, imm7 := x.imm7,
                                   Rt2 := x.Rt2, Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_pair_post_indexed x) =>
    .LDST (.Reg_pair_post_indexed { opc := x.opc, V := x.V, L := x.L, imm7 := x.imm7,
                                    Rt2 := x.Rt2, Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_pair_signed_offset x) =>
    .LDST (.Reg_pair_signed_offset { opc := x.opc, V := x.V, L := x.L, imm7 := x.imm7,
                                     Rt2 := x.Rt2, Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_imm_pre_indexed x) =>
    .LDST (.Reg_imm_pre_indexed { size := x.size, V := x.V, opc := x.opc, imm9 := x.imm9,
                                  Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_reg_offset x) =>
    .LDST (.Reg_reg_offset { size := x.size, V := x.V, opc := x.opc, Rm := x.Rm,
                             option := x.option, S := x.S, Rn := x.Rn, Rt := x.Rt })
  | .LDST (.Reg_exclusive x) =>
    .LDST (.Reg_exclusive { size := x.size, ord := x.ord, L := x.L, Rs := x.Rs, o0 := x.o0,
                            Rn := x.Rn, Rt := x.Rt })
  | .RES (.Udf x) => .RES (.Udf { imm16 := x.imm16 })

/-! ## Instruction → fields (Arm ARM C6/C7 instruction pages) -/

/-- Where the encoder is: the instruction's byte offset and the byte offsets of the
function's labels (both from the function start). -/
structure Env where
  pc : Nat
  lbl : Lbl → Option Nat

/-- Where a label operand points: `Lbl.skip` is the instruction after the next one (`pc + 8`,
the inverted short branch of a relaxed branch); other labels are the function's labels. -/
def Env.target (env : Env) : Lbl → Option Nat
  | .skip => some (env.pc + 8)
  | l => env.lbl l

/-- Byte offset from the instruction to `l`. -/
def Env.rel (env : Env) (l : Lbl) : Except String Int :=
  match env.target l with
  | some t => pure ((t : Int) - env.pc)
  | none => throw s!"undefined label {repr l}"

/-- `n` bytes as text (`128 MiB`, `1 MiB`, `32 KiB`). -/
def byteSizeText (n : Nat) : String :=
  if n % 2 ^ 20 == 0 then s!"{n / 2 ^ 20} MiB"
  else if n % 2 ^ 10 == 0 then s!"{n / 2 ^ 10} KiB" else s!"{n} bytes"

/-- The PC-relative immediate of a label operand: the byte offset to `l` divided by `scale`,
as a `bits`-bit signed field (C6.2 B: 26 bits, B.cond/CBZ/CBNZ: 19, TBZ/TBNZ: 14, all
`scale` 4; ADR: 21 bits, `scale` 1).

**Branch-range policy** (PLAN.md §3.4): `emitFunc` relaxes every conditional branch to a block or
trap label that would be out of range (`relaxLine`), so the encoder sees short branches only
where they reach. A target that is still outside the field's range (±128 MiB, ±1 MiB, ±32 KiB,
±1 MiB) is a compile error naming the instruction and the distance; the word is never
truncated. `Insn.encode_inRange` (`FV/Backend/Proof/EncodeBranch.lean`) proves every encoded
label operand is in range. -/
def Env.pcRel (env : Env) (what : String) (bits scale : Nat) (l : Lbl) :
    Except String (BitVec bits) := do
  let off ← env.rel l
  if off % scale != 0 then throw s!"{what} offset {off} is not a multiple of {scale}"
  let q := off / scale
  if -(2 ^ (bits - 1) : Int) ≤ q ∧ q < 2 ^ (bits - 1) then pure (BitVec.ofInt bits q)
  else throw s!"branch out of range: {what} to {repr l} is {off} bytes away, beyond the \
    ±{byteSizeText (2 ^ (bits - 1) * scale)} of {what} (PLAN.md §3.4: the function is too large)"

/-- `sf`, `opc`, `N` of the logical (shifted register / immediate) instructions
(C6.2 AND, BIC, ORR, ORN, EOR, EON, ANDS, BICS: `opc` 00 and, 01 orr, 10 eor, 11 ands). -/
def ALUOp.logic? : ALUOp → Option (BitVec 2 × BitVec 1)
  | .and => some (0, 0) | .andNot => some (0, 1) | .orr => some (1, 0) | .orrNot => some (1, 1)
  | .eor => some (2, 0) | .eorNot => some (2, 1) | .andS => some (3, 0)
  | _ => none

/-- `op`, `S` of the add/subtract instructions (C6.2 ADD, ADDS, SUB, SUBS). -/
def ALUOp.addSub? : ALUOp → Option (BitVec 1 × BitVec 1)
  | .add => some (0, 0) | .addS => some (0, 1) | .sub => some (1, 0) | .subS => some (1, 1)
  | _ => none

/-- `shift` field (C6.2 shifted-register forms: 00 LSL, 01 LSR, 10 ASR, 11 ROR). -/
def ShiftOp.bits : ShiftOp → BitVec 2
  | .lsl => 0 | .lsr => 1 | .asr => 2 | .ror => 3

/-- `(Q, size)` of an arrangement (C7.2 `<T>` tables). -/
def VectorSize.qsize : VectorSize → BitVec 1 × BitVec 2
  | .size8x8 => (0, 0) | .size8x16 => (1, 0) | .size16x4 => (0, 1) | .size16x8 => (1, 1)
  | .size32x2 => (0, 2) | .size32x4 => (1, 2) | .size64x2 => (1, 3)

/-- `(size, V, opc)` of a single-register load (C6.2 LDRB, LDRSB (64), LDRH, LDRSH (64), LDR
(32), LDRSW, LDR (64); C7.2 LDR (SIMD&FP) 128-bit), and its register-field encoder. -/
def LoadOp.fields : LoadOp → BitVec 2 × BitVec 1 × BitVec 2
  | .uload8 => (0, 0, 1) | .sload8 => (0, 0, 2) | .uload16 => (1, 0, 1) | .sload16 => (1, 0, 2)
  | .uload32 => (2, 0, 1) | .sload32 => (2, 0, 2) | .uload64 => (3, 0, 1)
  | .fpuLoad128 => (0, 1, 3)

/-- `(size, V, opc)` of a single-register store (C6.2 STRB, STRH, STR (32/64); C7.2 STR
(SIMD&FP) 128-bit). -/
def StoreOp.fields : StoreOp → BitVec 2 × BitVec 1 × BitVec 2
  | .store8 => (0, 0, 0) | .store16 => (1, 0, 0) | .store32 => (2, 0, 0) | .store64 => (3, 0, 0)
  | .fpuStore128 => (0, 1, 2)

/-- Single-register load/store with a final addressing mode: C4.1 classes "Load/store register
(unsigned immediate)", "(unscaled immediate)", "(register offset)", "(immediate pre-indexed)",
"(immediate post-indexed)" (Cranelift `enc_ldst_uimm12`, `enc_ldst_simm9`, `enc_ldst_reg`). -/
def ldstFields (size : BitVec 2) (V : BitVec 1) (opc : BitVec 2) (bytes : Nat) (Rt : BitVec 5)
    (m : AMode) : Except String ArmInst := do
  match m with
  | .unsignedOffset rn off =>
    if off % bytes != 0 then throw s!"offset {off} is not a multiple of {bytes}"
    let imm12 ← uField "scaled offset" 12 (off / bytes)
    pure (.LDST (.Reg_unsigned_imm { size, V, opc, imm12, Rn := ← rn.encSP, Rt }))
  | .unscaled rn s =>
    pure (.LDST (.Reg_unscaled_imm { size, VR := V, opc, imm9 := ← sField "simm9" 9 s,
                                     Rn := ← rn.encSP, Rt }))
  | .spPreIndexed s =>
    pure (.LDST (.Reg_imm_pre_indexed { size, V, opc, imm9 := ← sField "simm9" 9 s, Rn := 31#5, Rt }))
  | .spPostIndexed s =>
    pure (.LDST (.Reg_imm_post_indexed { size, V, opc, imm9 := ← sField "simm9" 9 s, Rn := 31#5, Rt }))
  | .regReg rn rm =>
    pure (.LDST (.Reg_reg_offset { size, V, opc, Rm := ← rm.encZR, option := 3, S := 0,
                                   Rn := ← rn.encSP, Rt }))
  | .regScaled rn rm =>
    pure (.LDST (.Reg_reg_offset { size, V, opc, Rm := ← rm.encZR, option := 3, S := 1,
                                   Rn := ← rn.encSP, Rt }))
  | .regScaledExtended rn rm e | .regExtended rn rm e =>
    -- option<1> must be 1 (UXTW 010, LSL/UXTX 011, SXTW 110, SXTX 111)
    if !(e == .uxtw || e == .uxtx || e == .sxtw || e == .sxtx) then
      throw s!"extend {repr e} is not allowed in a register-offset address"
    let S := match m with | .regScaledExtended .. => 1#1 | _ => 0#1
    pure (.LDST (.Reg_reg_offset { size, V, opc, Rm := ← rm.encZR, option := e.bits, S,
                                   Rn := ← rn.encSP, Rt }))
  | m => throw s!"addressing mode {repr m} is not final"

/-- The encoding-class fields of one instruction at `env.pc` (structure literals: the
`_fixed` fields keep their defaults). -/
def Insn.armFields (env : Env) (i : Insn) : Except String ArmInst := do
  match i with
  | .aluRRR op w rd rn rm =>
    let sf := b1 w
    let Rd ← rd.encZR
    let Rn ← rn.encZR
    let Rm ← rm.encZR
    match op.addSub?, op.logic? with
    | some (o, S), _ =>
      -- C6.2 ADD/ADDS/SUB/SUBS (shifted register), LSL #0 (Cranelift `enc_arith_rrr`)
      pure (.DPR (.Add_sub_shifted_reg { sf, op := o, S, shift := 0, Rm, imm6 := 0, Rn, Rd }))
    | none, some (opc, N) =>
      -- C6.2 AND/ORR/EOR/ANDS/BIC/ORN/EON (shifted register), LSL #0
      pure (.DPR (.Logical_shifted_reg { sf, opc, shift := 0, N, Rm, imm6 := 0, Rn, Rd }))
    | none, none =>
      match op with
      -- C6.2 UDIV, SDIV, LSLV, LSRV, ASRV, RORV (Data-processing (2 source))
      | .uDiv => pure (dp2 sf 0b000010 Rm Rn Rd)
      | .sDiv => pure (dp2 sf 0b000011 Rm Rn Rd)
      | .lsl => pure (dp2 sf 0b001000 Rm Rn Rd)
      | .lsr => pure (dp2 sf 0b001001 Rm Rn Rd)
      | .asr => pure (dp2 sf 0b001010 Rm Rn Rd)
      | .extr => pure (dp2 sf 0b001011 Rm Rn Rd)
      -- C6.2 SMULH, UMULH (Data-processing (3 source), Ra = 11111, 64-bit only)
      | .sMulH | .uMulH =>
        if !w then throw "smulh/umulh are 64-bit only"
        pure (.DPR (.Data_processing_three_source
          { sf := 1, op54 := 0, op31 := if op == .sMulH then 0b010 else 0b110, Rm, o0 := 0,
            Ra := 31, Rn, Rd }))
      -- C6.2 ADC, ADCS, SBC, SBCS (Add/subtract (with carry))
      | .adc | .adcS | .sbc | .sbcS =>
        pure (.DPR (.Add_sub_carry { sf, op := b1 (op == .sbc || op == .sbcS),
                                     S := b1 (op == .adcS || op == .sbcS), Rm, Rn, Rd }))
      | _ => throw s!"aluRRR {repr op}"
  | .aluRRRR op w rd rn rm ra =>
    -- C6.2 MADD, MSUB, SMADDL, UMADDL (Data-processing (3 source); Cranelift `enc_arith_rrrr`)
    let (op31, o0) : BitVec 3 × BitVec 1 := match op with
      | .mAdd => (0, 0) | .mSub => (0, 1) | .sMAddL => (1, 0) | .uMAddL => (5, 0)
    let sf := match op with | .mAdd | .mSub => b1 w | _ => 1
    pure (.DPR (.Data_processing_three_source
      { sf, op54 := 0, op31, Rm := ← rm.encZR, o0, Ra := ← ra.encZR, Rn := ← rn.encZR,
        Rd := ← rd.encZR }))
  | .aluImm12 op w rd rn imm =>
    -- C6.2 ADD/ADDS/SUB/SUBS (immediate) (Cranelift `enc_arith_rr_imm12`); Rd is SP for
    -- ADD/SUB and ZR for ADDS/SUBS (CMN/CMP), Rn is SP
    let some (o, S) := op.addSub? | throw s!"aluImm12 {repr op}"
    let Rd ← if S == 1 then rd.encZR else rd.encSP
    pure (.DPI (.Add_sub_imm { sf := b1 w, op := o, S, sh := b1 imm.shift12,
                               imm12 := ← uField "imm12" 12 imm.bits, Rn := ← rn.encSP, Rd }))
  | .logicImm op w rd rn v =>
    -- C6.2 AND/ORR/EOR/ANDS (immediate) (Cranelift `enc_arith_rr_imml`); Rd is SP except ANDS
    let some (opc, 0) := op.logic? | throw s!"logicImm {repr op}"
    let some (N, immr, imms) := bitmaskEnc? w v | throw s!"{hex v} is not a bitmask immediate"
    let Rd ← if opc == 3 then rd.encZR else rd.encSP
    pure (.DPI (.Logical_imm { sf := b1 w, opc, N, immr, imms, Rn := ← rn.encZR, Rd }))
  | .shiftImm op w rd rn amt =>
    let size := if w then 64 else 32
    if amt ≥ size then throw s!"shift amount {amt} ≥ {size}"
    let Rd ← rd.encZR
    let Rn ← rn.encZR
    let bf (opc : BitVec 2) (immr imms : Nat) : ArmInst :=
      .DPI (.Bitfield { sf := b1 w, opc, N := b1 w, immr := BitVec.ofNat 6 immr,
                        imms := BitVec.ofNat 6 imms, Rn, Rd })
    match op with
    -- C6.2 LSL (immediate) = UBFM Rd, Rn, #(-shift MOD size), #(size-1-shift)
    | .lsl => pure (bf 2 ((size - amt) % size) (size - 1 - amt))
    -- C6.2 LSR (immediate) = UBFM Rd, Rn, #shift, #(size-1)
    | .lsr => pure (bf 2 amt (size - 1))
    -- C6.2 ASR (immediate) = SBFM Rd, Rn, #shift, #(size-1)
    | .asr => pure (bf 0 amt (size - 1))
    -- C6.2 ROR (immediate) = EXTR Rd, Rs, Rs, #shift (Cranelift `Inst::AluRRImmShift`, `ALUOp::Extr`)
    | .ror => pure (.DPI (.Extract { sf := b1 w, op21 := 0, N := b1 w, o0 := 0, Rm := Rn,
                                     imms := BitVec.ofNat 6 amt, Rn, Rd }))
  | .aluRRRShift op w rd rn rm sh =>
    let size := if w then 64 else 32
    if sh.amt ≥ size then throw s!"shift amount {sh.amt} ≥ {size}"
    let sf := b1 w
    let Rd ← rd.encZR
    let Rn ← rn.encZR
    let Rm ← rm.encZR
    let imm6 := BitVec.ofNat 6 sh.amt
    match op.addSub?, op.logic? with
    | some (o, S), _ =>
      -- C6.2 ADD/SUB… (shifted register): shift = 11 (ROR) is reserved
      if sh.op == .ror then throw "ror is not allowed in add/sub (shifted register)"
      pure (.DPR (.Add_sub_shifted_reg { sf, op := o, S, shift := sh.op.bits, Rm, imm6, Rn, Rd }))
    | none, some (opc, N) =>
      pure (.DPR (.Logical_shifted_reg { sf, opc, shift := sh.op.bits, N, Rm, imm6, Rn, Rd }))
    | none, none => throw s!"aluRRRShift {repr op}"
  | .extr w rd rn rm lsb =>
    -- C6.2 EXTR (Cranelift `Inst::AluRRRShift`, `ALUOp::Extr`)
    if lsb ≥ (if w then 64 else 32) then throw s!"extr lsb {lsb}"
    pure (.DPI (.Extract { sf := b1 w, op21 := 0, N := b1 w, o0 := 0, Rm := ← rm.encZR,
                           imms := BitVec.ofNat 6 lsb, Rn := ← rn.encZR, Rd := ← rd.encZR }))
  | .aluRRRExtend op w rd rn rm e =>
    -- C6.2 ADD/ADDS/SUB/SUBS (extended register), amount 0 (Cranelift `Inst::AluRRRExtend`)
    let some (o, S) := op.addSub? | throw s!"aluRRRExtend {repr op}"
    let Rd ← if S == 1 then rd.encZR else rd.encSP
    pure (.DPR (.Add_sub_ext_reg { sf := b1 w, op := o, S, opt := 0, Rm := ← rm.encZR,
                                   option := e.bits, imm3 := 0, Rn := ← rn.encSP, Rd }))
  | .bitRR op w rd rn =>
    -- C6.2 RBIT, REV16, REV32, REV, CLZ, CLS (Data-processing (1 source); Cranelift `enc_bit_rr`)
    -- `Rev32` at `Size32` is opcode `0b000010` with `sf = 0` (`emit.rs:971`) = `rev w`; the
    -- printer's `rev w` for `rev64` at `w` is the same instruction.
    let opcode : BitVec 6 := match op, w with
      | .rbit, _ => 0 | .rev16, _ => 1 | .rev32, _ => 2
      | .rev64, true => 3 | .rev64, false => 2 | .clz, _ => 4 | .cls, _ => 5
    pure (.DPR (.Data_processing_one_source { sf := b1 w, S := 0, opcode2 := 0, opcode,
                                              Rn := ← rn.encZR, Rd := ← rd.encZR }))
  | .load op rt m =>
    let (size, V, opc) := op.fields
    let Rt ← if V == 1 then rt.encV else rt.encZR
    ldstFields size V opc op.bytes Rt m
  | .store op rt m =>
    let (size, V, opc) := op.fields
    let Rt ← if V == 1 then rt.encV else rt.encZR
    ldstFields size V opc op.bytes Rt m
  | .ldp rt rt2 m | .stp rt rt2 m =>
    -- C6.2 LDP/STP (64-bit, opc = 10), imm7 = offset / 8 (Cranelift `enc_ldst_pair`)
    let L := match i with | .ldp .. => 1#1 | _ => 0#1
    let Rt ← rt.encZR
    let Rt2 ← rt2.encZR
    let imm (s : Int) : Except String (BitVec 7) :=
      if s % 8 != 0 then throw s!"pair offset {s}" else sField "imm7" 7 (s / 8)
    match m with
    | .spPreIndexed s =>
      pure (.LDST (.Reg_pair_pre_indexed { opc := 2, V := 0, L, imm7 := ← imm s, Rt2, Rn := 31, Rt }))
    | .spPostIndexed s =>
      pure (.LDST (.Reg_pair_post_indexed { opc := 2, V := 0, L, imm7 := ← imm s, Rt2, Rn := 31, Rt }))
    | m => throw s!"ldp/stp mode {repr m}"
  | .mov w rd rm =>
    if rd == .sp || rm == .sp then
      -- C6.2 MOV (to/from SP) = ADD Rd, Rn, #0
      pure (.DPI (.Add_sub_imm { sf := b1 w, op := 0, S := 0, sh := 0, imm12 := 0,
                                 Rn := ← rm.encSP, Rd := ← rd.encSP }))
    else
      -- C6.2 MOV (register) = ORR Rd, ZR, Rm (Cranelift `Inst::Mov` → `enc_arith_rrr`)
      pure (.DPR (.Logical_shifted_reg { sf := b1 w, opc := 1, shift := 0, N := 0,
                                         Rm := ← rm.encZR, imm6 := 0, Rn := 31, Rd := ← rd.encZR }))
  | .movWide op w rd imm =>
    -- C6.2 MOVN (opc 00), MOVZ (opc 10) (Cranelift `enc_move_wide`)
    if imm.shift ≥ (if w then 4 else 2) then throw s!"movz/movn shift {imm.shift}"
    pure (.DPI (.Move_wide_imm { sf := b1 w, opc := if op == .movZ then 2 else 0,
                                 hw := BitVec.ofNat 2 imm.shift,
                                 imm16 := ← uField "imm16" 16 imm.bits, Rd := ← rd.encZR }))
  | .movk w rd imm =>
    -- C6.2 MOVK (opc 11) (Cranelift `enc_movk`)
    if imm.shift ≥ (if w then 4 else 2) then throw s!"movk shift {imm.shift}"
    pure (.DPI (.Move_wide_imm { sf := b1 w, opc := 3, hw := BitVec.ofNat 2 imm.shift,
                                 imm16 := ← uField "imm16" 16 imm.bits, Rd := ← rd.encZR }))
  | .bfm op w rd rn immr imms =>
    -- C6.2 SBFM (opc 00), UBFM (opc 10); N = sf (Cranelift `enc_bfm`)
    let size := if w then 64 else 32
    if immr ≥ size || imms ≥ size then throw s!"bfm #{immr}, #{imms}"
    pure (.DPI (.Bitfield { sf := b1 w, opc := if op == .sBfm then 0 else 2, N := b1 w,
                            immr := BitVec.ofNat 6 immr, imms := BitVec.ofNat 6 imms,
                            Rn := ← rn.encZR, Rd := ← rd.encZR }))
  | .cset rd c =>
    -- C6.2 CSET = CSINC Rd, ZR, ZR, invert(cond), cond ≠ 111x (Cranelift `enc_csel` op2 01)
    if c == .al || c == .nv then throw "cset al/nv"
    pure (.DPR (.Conditional_select { sf := 1, op := 0, S := 0, Rm := 31, cond := c.invert.bits,
                                      op2 := 1, Rn := 31, Rd := ← rd.encZR }))
  | .csel rd rn rm c =>
    -- C6.2 CSEL (64-bit)
    pure (.DPR (.Conditional_select { sf := 1, op := 0, S := 0, Rm := ← rm.encZR, cond := c.bits,
                                      op2 := 0, Rn := ← rn.encZR, Rd := ← rd.encZR }))
  | .ccmp w rn rm f c =>
    -- C6.2 CCMP (register) (Cranelift `enc_ccmp`)
    pure (.DPR (.Conditional_compare_reg { sf := b1 w, op := 1, S := 1, Rm := ← rm.encZR,
                                           cond := c.bits, o2 := 0, Rn := ← rn.encZR, o3 := 0,
                                           nzcv := BitVec.ofNat 4 f.bits }))
  | .ccmpImm w rn imm f c =>
    -- C6.2 CCMP (immediate) (Cranelift `enc_ccmp_imm`)
    pure (.DPR (.Conditional_compare_imm { sf := b1 w, op := 1, S := 1,
                                           imm5 := ← uField "imm5" 5 imm, cond := c.bits, o2 := 0,
                                           Rn := ← rn.encZR, o3 := 0,
                                           nzcv := BitVec.ofNat 4 f.bits }))
  | .fmovToFp s rd rn =>
    -- C7.2 FMOV (general): Hd←Wn (sf 0, ftype 11), Sd←Wn (0, 00), Dd←Xn (1, 01); rmode 00,
    -- opcode 111 (Cranelift `Inst::MovToFpu`)
    let (sf, ftype) : BitVec 1 × BitVec 2 ← match s with
      | .size16 => pure (0, 3) | .size32 => pure (0, 0) | .size64 => pure (1, 1)
      | _ => throw s!"fmov size {repr s}"
    pure (.DPSFP (.Conversion_between_FP_and_Int { sf, S := 0, ftype, rmode := 0, opcode := 7,
                                                   Rn := ← rn.encZR, Rd := ← rd.encV }))
  | .umov s rd rn idx =>
    -- C7.2 UMOV: imm5 = idx:1, idx:10, idx:100, idx:1000 (B/H/S/D), imm4 = 0111, Q = (D)
    -- (Cranelift `Inst::MovFromVec`)
    let (q, imm5) : BitVec 1 × Nat ← match s with
      | .size8 => pure (0, idx * 2 + 1) | .size16 => pure (0, idx * 4 + 2)
      | .size32 => pure (0, idx * 8 + 4) | .size64 => pure (1, idx * 16 + 8)
      | _ => throw s!"umov size {repr s}"
    pure (.DPSFP (.Advanced_simd_copy { Q := q, op := 0, imm5 := ← uField "umov index" 5 imm5,
                                        imm4 := 7, Rn := ← rn.encV, Rd := ← rd.encZR }))
  | .cnt s rd rn =>
    -- C7.2 CNT (Advanced SIMD two-register miscellaneous, U 0, size 00, opcode 00101;
    -- Cranelift `Inst::VecMisc`)
    let (Q, size) := s.qsize
    if size != 0 then throw s!"cnt arrangement {repr s}"
    pure (.DPSFP (.Advanced_simd_two_reg_misc { Q, U := 0, size, opcode := 5, Rn := ← rn.encV,
                                                Rd := ← rd.encV }))
  | .vecLanes op s rd rn =>
    -- C7.2 ADDV (U 0, opcode 11011), UADDLV (U 1, opcode 00011) (Advanced SIMD across lanes);
    -- arrangements 8B 16B 4H 8H 4S (Cranelift `enc_vec_lanes`)
    let (Q, size) := s.qsize
    if s == .size32x2 || s == .size64x2 then throw s!"addv/uaddlv arrangement {repr s}"
    pure (.DPSFP (.Advanced_simd_across_lanes
      { Q, U := b1 (op == .uaddlv), size, opcode := if op == .addv then 0b11011 else 0b00011,
        Rn := ← rn.encV, Rd := ← rd.encV }))
  | .addp s rd rn rm =>
    -- C7.2 ADDP (vector) (Advanced SIMD three same, U 0, opcode 10111; Cranelift `enc_vec_rrr`)
    let (Q, size) := s.qsize
    pure (.DPSFP (.Advanced_simd_three_same { Q, U := 0, size, Rm := ← rm.encV, opcode := 0b10111,
                                              Rn := ← rn.encV, Rd := ← rd.encV }))
  | .b t =>
    -- C6.2 B: imm26 = offset / 4, ±128 MiB (Cranelift `enc_jump26`)
    pure (.BR (.Uncond_branch_imm { op := 0, imm26 := ← env.pcRel "b" 26 4 t }))
  | .bcond c t =>
    -- C6.2 B.cond: imm19, ±1 MiB (Cranelift `enc_cbr`)
    pure (.BR (.Cond_branch_imm { imm19 := ← env.pcRel "b.cond" 19 4 t, o0 := 0,
                                  cond := c.bits }))
  | .cbz nz w rt t =>
    -- C6.2 CBZ/CBNZ (Compare and branch (immediate), imm19, ±1 MiB; Cranelift `enc_cmpbr`)
    pure (.BR (.Compare_branch { sf := b1 w, op := b1 nz, imm19 := ← env.pcRel "cbz" 19 4 t,
                                 Rt := ← rt.encZR }))
  | .tbz nz rt bit t =>
    -- C6.2 TBZ/TBNZ: b5:b40 = bit number, imm14, ±32 KiB (Cranelift `enc_test_bit_and_branch`)
    if bit ≥ 64 then throw s!"tbz bit {bit}"
    pure (.BR (.Test_branch { b5 := BitVec.ofNat 1 (bit / 32), op := b1 nz,
                              b40 := BitVec.ofNat 5 (bit % 32),
                              imm14 := ← env.pcRel "tbz" 14 4 t, Rt := ← rt.encZR }))
  | .bl _ =>
    -- C6.2 BL, imm26 from R_AARCH64_CALL26
    pure (.BR (.Uncond_branch_imm { op := 1, imm26 := 0 }))
  | .blr rn =>
    -- C6.2 BLR (Unconditional branch (register), opc 0001, op2 11111)
    pure (.BR (.Uncond_branch_reg { opc := 1, op2 := 31, op3 := 0, Rn := ← rn.encZR, op4 := 0 }))
  | .br rn =>
    -- C6.2 BR (opc 0000)
    pure (.BR (.Uncond_branch_reg { opc := 0, op2 := 31, op3 := 0, Rn := ← rn.encZR, op4 := 0 }))
  | .ret =>
    -- C6.2 RET (opc 0010), Rn = x30
    pure (.BR (.Uncond_branch_reg { opc := 2, op2 := 31, op3 := 0, Rn := 30, op4 := 0 }))
  | .udf imm =>
    -- C6.2 UDF (Reserved, bits 31:16 zero)
    pure (.RES (.Udf { imm16 := ← uField "udf immediate" 16 imm }))
  | .adr rd t =>
    -- C6.2 ADR: immhi:immlo = byte offset, ±1 MiB (Cranelift `enc_adr`)
    let imm ← env.pcRel "adr" 21 1 t
    pure (.DPI (.PC_rel_addressing { op := 0, immlo := imm.extractLsb' 0 2,
                                     immhi := imm.extractLsb' 2 19, Rd := ← rd.encZR }))
  | .adrpGot rd _ | .adrp rd _ _ =>
    -- C6.2 ADRP, immhi:immlo from R_AARCH64_ADR_GOT_PAGE / R_AARCH64_ADR_PREL_PG_HI21
    pure (.DPI (.PC_rel_addressing { op := 1, immlo := 0, immhi := 0, Rd := ← rd.encZR }))
  | .ldrGotLo12 rd rn _ =>
    -- C6.2 LDR (immediate, unsigned offset, 64-bit), imm12 from R_AARCH64_LD64_GOT_LO12_NC
    pure (.LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := ← rn.encSP,
                                     Rt := ← rd.encZR }))
  | .addLo12 rd rn _ _ =>
    -- C6.2 ADD (immediate, 64-bit), imm12 from R_AARCH64_ADD_ABS_LO12_NC
    pure (.DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := ← rn.encSP,
                               Rd := ← rd.encSP }))
  | .ldar bits rt rn => exclFields bits 1 1 31 rt rn
  | .stlr bits rt rn => exclFields bits 1 0 31 rt rn
  | .ldaxr bits rt rn => exclFields bits 0 1 31 rt rn
  | .stlxr bits rs rt rn => exclFields bits 0 0 (← rs.encZR) rt rn
  | .dmbish =>
    -- C6.2 DMB (option ISH: op1 = 11, CRm = 1011, op2 = 101; Cranelift `enc_dmb_ish`)
    pure (.BR (.Barrier { CRm := 0b1011#4, op2 := 0b101#3 }))
  | .csetm rd c =>
    -- C6.2 CSETM = CSINV Rd, ZR, ZR, invert(cond) (Cranelift `enc_csel` op2 00)
    if c == .al || c == .nv then throw "csetm al/nv"
    pure (.DPR (.Conditional_select { sf := 1, op := 1, S := 0, Rm := 31,
                                      cond := c.invert.bits, op2 := 0, Rn := 31,
                                      Rd := ← rd.encZR }))
  -- the TLSDESC sequence (`emit.rs` `ElfTlsGetAddr`); the immediates come from the
  -- `R_AARCH64_TLSDESC_*` relocations, as for the GOT forms above
  | .adrpTlsDesc rd _ =>
    pure (.DPI (.PC_rel_addressing { op := 1, immlo := 0, immhi := 0, Rd := ← rd.encZR }))
  | .ldrTlsDescLo12 rt rn _ =>
    pure (.LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := ← rn.encSP,
                                     Rt := ← rt.encZR }))
  | .addTlsDescLo12 rd rn _ =>
    pure (.DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := ← rn.encSP,
                               Rd := ← rd.encSP }))
  | .blrTlsDesc rn _ =>
    pure (.BR (.Uncond_branch_reg { opc := 1, op2 := 31, op3 := 0, Rn := ← rn.encZR, op4 := 0 }))
  | .mrsTpidrEl0 rt =>
    -- C6.2 MRS, TPIDR_EL0 = (op0 3, op1 011, CRn 1101, CRm 0000, op2 010) (Cranelift
    -- `0xd53bd040 | rt`)
    pure (.BR (.Mrs { o0 := 1, op1 := 0b011#3, CRn := 0b1101#4, CRm := 0, op2 := 0b010#3,
                      Rt := ← rt.encZR }))
where
  /-- `Reg_exclusive` fields of `ldar`/`stlr`/`ldaxr`/`stlxr` (`bits` = the access size;
  `ord`/`L`/`Rs`/`o0` per C6.2 "Load/store exclusive / … acquire-release"). -/
  exclFields (bits o2 L : Nat) (Rs : BitVec 5) (rt rn : Reg) : Except String ArmInst := do
    let size : BitVec 2 ←
      match bits with
      | 8 => pure 0b00#2 | 16 => pure 0b01#2 | 32 => pure 0b10#2 | 64 => pure 0b11#2
      | _ => throw s!"unsupported atomic access size {bits}"
    pure (.LDST (.Reg_exclusive { size, ord := BitVec.ofNat 1 o2, L := BitVec.ofNat 1 L,
                                  Rs, o0 := 1#1, Rn := ← rn.encSP, Rt := ← rt.encZR }))
  /-- Data-processing (2 source) with `S = 0`. -/
  dp2 (sf : BitVec 1) (opcode : BitVec 6) (Rm Rn Rd : BitVec 5) : ArmInst :=
    .DPR (.Data_processing_two_source { sf, S := 0, Rm, opcode, Rn, Rd })

/-- The encoding-class fields of one instruction at `env.pc`, as the decoder returns them
(`ArmInst.norm` is the identity on `armFields`' literals; it makes the `_fixed` fields
irrelevant by construction, so `decode_encode` needs no per-constructor case analysis). -/
def Insn.toArmInst (env : Env) (i : Insn) : Except String ArmInst :=
  ArmInst.norm <$> i.armFields env

/-- The machine word of an instruction at `env.pc`. -/
def Insn.encode (env : Env) (i : Insn) : Except String (BitVec 32) :=
  armBits <$> i.toArmInst env

/-- The M5 round-trip property for one instruction: the decoder of the Lean Arm model reads
the encoded word back as the intended instruction. -/
def Insn.decodeOk (env : Env) (i : Insn) : Bool :=
  match i.toArmInst env with
  | .ok a => decode_raw_inst (armBits a) == some a
  | .error _ => false

/-! ## Relocations -/

/-- AArch64 ELF relocation types used (AAELF64 "ELF for the Arm 64-bit Architecture", relocation codes table). -/
inductive RelocType where
  | call26 | adrGotPage | ld64GotLo12Nc | adrPrelPgHi21 | addAbsLo12Nc
  | tlsDescAdrPage21 | tlsDescLd64Lo12 | tlsDescAddLo12 | tlsDescCall
  deriving DecidableEq, Repr, Inhabited, BEq

/-- ELF `R_AARCH64_*` number. -/
def RelocType.elf : RelocType → Nat
  | .call26 => 283 | .adrGotPage => 311 | .ld64GotLo12Nc => 312 | .adrPrelPgHi21 => 275
  | .addAbsLo12Nc => 277
  | .tlsDescAdrPage21 => 562 | .tlsDescLd64Lo12 => 563 | .tlsDescAddLo12 => 564
  | .tlsDescCall => 569

/-- ELF name (as `llvm-readelf` prints it). -/
def RelocType.elfName : RelocType → String
  | .call26 => "R_AARCH64_CALL26" | .adrGotPage => "R_AARCH64_ADR_GOT_PAGE"
  | .ld64GotLo12Nc => "R_AARCH64_LD64_GOT_LO12_NC" | .adrPrelPgHi21 => "R_AARCH64_ADR_PREL_PG_HI21"
  | .addAbsLo12Nc => "R_AARCH64_ADD_ABS_LO12_NC"
  | .tlsDescAdrPage21 => "R_AARCH64_TLSDESC_ADR_PAGE21"
  | .tlsDescLd64Lo12 => "R_AARCH64_TLSDESC_LD64_LO12"
  | .tlsDescAddLo12 => "R_AARCH64_TLSDESC_ADD_LO12" | .tlsDescCall => "R_AARCH64_TLSDESC_CALL"

/-- Cranelift's `binemit::Reloc` name (the `relocs.json` schema of `docs/contracts/drivers.md`). -/
def RelocType.craneliftName : RelocType → String
  | .call26 => "Arm64Call" | .adrGotPage => "Aarch64AdrGotPage21"
  | .ld64GotLo12Nc => "Aarch64Ld64GotLo12Nc" | .adrPrelPgHi21 => "Aarch64AdrPrelPgHi21"
  | .addAbsLo12Nc => "Aarch64AddAbsLo12Nc"
  | .tlsDescAdrPage21 => "Aarch64TlsDescAdrPage21" | .tlsDescLd64Lo12 => "Aarch64TlsDescLd64Lo12"
  | .tlsDescAddLo12 => "Aarch64TlsDescAddLo12" | .tlsDescCall => "Aarch64TlsDescCall"

/-- A TLS relocation: its symbol is a thread-local variable (`STT_TLS`). -/
def RelocType.isTls : RelocType → Bool
  | .tlsDescAdrPage21 | .tlsDescLd64Lo12 | .tlsDescAddLo12 | .tlsDescCall => true
  | _ => false

/-- A relocation: byte offset of the instruction, type, target symbol, RELA addend. -/
structure Reloc where
  offset : Nat
  type : RelocType
  sym : String
  addend : Int
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The relocation an instruction needs (its immediate field is left zero). -/
def Insn.reloc? : Insn → Option (RelocType × String × Int)
  | .bl s => some (.call26, s, 0)
  | .adrpGot _ s => some (.adrGotPage, s, 0)
  | .ldrGotLo12 _ _ s => some (.ld64GotLo12Nc, s, 0)
  | .adrp _ s a => some (.adrPrelPgHi21, s, a)
  | .addLo12 _ _ s a => some (.addAbsLo12Nc, s, a)
  | .adrpTlsDesc _ s => some (.tlsDescAdrPage21, s, 0)
  | .ldrTlsDescLo12 _ _ s => some (.tlsDescLd64Lo12, s, 0)
  | .addTlsDescLo12 _ _ s => some (.tlsDescAddLo12, s, 0)
  | .blrTlsDesc _ s => some (.tlsDescCall, s, 0)
  | _ => none

/-! ## Layout -/

/-- A laid-out function: code words (instructions and jump-table data, in order),
relocations and trap sites (offsets from the function start), and each instruction with its
offset (for the decode check). -/
structure FnBin where
  name : String
  words : Array (BitVec 32)
  relocs : List Reloc
  traps : List TrapSite
  insns : Array (Nat × Insn)
  deriving Inhabited

def FnBin.size (f : FnBin) : Nat := 4 * f.words.size

/-- Byte offset of line `j` of a line list: the sizes of the lines before it. -/
def lineOffset (lines : List Line) (j : Nat) : Nat := ((lines.take j).map Line.size).sum

def Line.isLabel : Line → Bool
  | .label _ => true
  | _ => false

/-- The code lines (instructions and jump-table words, 4 bytes each): the `k`-th one is at
byte offset `4 * k`, and is word `k` of the function. -/
def codeLines (lines : List Line) : List Line := lines.filter (!·.isLabel)

/-- The word of a code line at byte offset `pc`; jump-table words are `target - base`
(signed 32-bit). -/
def Line.encodeAt (lbl : Lbl → Option Nat) (pc : Nat) : Line → Except String (BitVec 32)
  | .ins i _ => i.encode { pc, lbl }
  | .word t b =>
    match lbl t, lbl b with
    | some t, some b => sField "jump-table entry" 32 ((t : Int) - b)
    | _, _ => throw "undefined label in jump table"
  | .label _ => throw "a label has no word"

/-- Encode code lines, appending to `acc` (word `k` at byte offset `4 * k`); `ctx pc ln e`
is the error message. -/
def encodeCode (ctx : Nat → Line → String → String) (lbl : Lbl → Option Nat) :
    List Line → Array (BitVec 32) → Except String (Array (BitVec 32))
  | [], acc => pure acc
  | ln :: rest, acc =>
    match ln.encodeAt lbl (4 * acc.size) with
    | .ok w => encodeCode ctx lbl rest (acc.push w)
    | .error e => throw (ctx (4 * acc.size) ln e)

/-- Relocations of code lines (at the instruction's offset). -/
def codeRelocs (code : List Line) : List Reloc :=
  code.zipIdx.filterMap fun (ln, k) => match ln with
    | .ins i _ => i.reloc?.map fun (type, sym, addend) => { offset := 4 * k, type, sym, addend }
    | _ => none

/-- Trap sites of code lines: the offsets of the instructions that carry a trap code. -/
def codeTraps (code : List Line) : List TrapSite :=
  code.zipIdx.filterMap fun (ln, k) => match ln with
    | .ins _ (some c) => some ⟨4 * k, c⟩
    | _ => none

/-- Instructions of code lines with their offsets. -/
def codeInsns (code : List Line) : List (Nat × Insn) :=
  code.zipIdx.filterMap fun (ln, k) => match ln with
    | .ins i _ => some (4 * k, i)
    | _ => none

/-- Lay out a function: resolve labels, encode every code line at its offset, collect
relocations and trap sites (checked against `emitFunc`'s trap table). Specification and
proof: `FnAsm.layout_*` in `FV/Backend/Proof/EncodeLayout.lean`. -/
def FnAsm.layout (f : FnAsm) : Except String FnBin := do
  let lbls ← (labelOffsets f.lines).mapError (s!"{f.name}: " ++ ·)
  let lbl (l : Lbl) : Option Nat := lbls[l]?
  let code := codeLines f.lines.toList
  let ctx (pc : Nat) (ln : Line) (e : String) : String := match ln with
    | .ins i _ => s!"{f.name}+{pc}: `{i.asm f.k}`: {e}"
    | _ => s!"{f.name}+{pc}: {e}"
  let words ← encodeCode ctx lbl code #[]
  if 4 * words.size != f.size then throw s!"{f.name}: size {4 * words.size} ≠ {f.size}"
  let traps := codeTraps code
  if traps != f.traps then throw s!"{f.name}: trap table differs from the trap sites"
  pure { name := f.name, words, relocs := codeRelocs code, traps,
         insns := (codeInsns code).toArray }

/-- Little-endian bytes of code words. -/
def wordsBytes (ws : Array (BitVec 32)) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * ws.size)
  for w in ws do
    let n := w.toNat
    b := b.push (UInt8.ofNat n) |>.push (UInt8.ofNat (n >>> 8)) |>.push (UInt8.ofNat (n >>> 16))
      |>.push (UInt8.ofNat (n >>> 24))
  return b

end Backend

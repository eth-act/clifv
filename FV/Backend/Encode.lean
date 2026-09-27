import FV.Backend.Asm
import FV.Arm.Decode

/-!
# Machine-code encoder (M5, unproven)

`Insn.encode env i = armBits <$> Insn.toArmInst env i`:

* `Insn.toArmInst` gives the **field values** of an instruction: the encoding class of the Lean
  Arm model (`Arm.ArmInst`, the type `Arm.decode_raw_inst` returns) and each field, as the
  instruction's page in the Arm ARM (DDI 0487, chapter C6 "A64 Base Instruction Descriptions",
  chapter C7 "A64 Advanced SIMD and Floating-point Instruction Descriptions") fixes them, with
  aliases translated per their "Alias conditions"/"is equivalent to" rules. Operand
  constraints (register 31 as SP or ZR, immediate ranges, branch ranges) are checked here.
* `armBits` concatenates the fields of an encoding class in the order of the class's
  encoding diagram (Arm ARM C4.1 "A64 instruction set encoding").

The executable check `decode_raw_inst (encode env i) = some (toArmInst env i)` is the M5
theorem `decode ∘ encode = id` restricted to what the backend emits
(`FVTest/Backend/Encode/DecodeCheck.lean`); `Insn.decodeOk` states it per instruction.

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

/-- `cond` field (the `Cond` constructors are in hardware order; Arm ARM C1.2.4). -/
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

/-- `i / 4` for a 4-byte aligned byte offset. -/
def wordOffset (what : String) (i : Int) : Except String Int :=
  if i % 4 == 0 then pure (i / 4) else throw s!"{what} offset {i} is not a multiple of 4"

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
  | .BR (.Test_branch x) => x.b5 ++ 0b011011#6 ++ x.op ++ x.b40 ++ x.imm14 ++ x.Rt
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
  -- C4.1 Reserved: UDF
  | .RES (.Udf x) => 0#16 ++ x.imm16

/-! ## Instruction → fields (Arm ARM C6/C7 instruction pages) -/

/-- Where the encoder is: the instruction's byte offset and the byte offsets of the
function's labels (both from the function start). -/
structure Env where
  pc : Nat
  lbl : Lbl → Option Nat

/-- Byte offset from the instruction to `l`. -/
def Env.rel (env : Env) (l : Lbl) : Except String Int :=
  match env.lbl l with
  | some t => pure ((t : Int) - env.pc)
  | none => throw s!"undefined label {repr l}"

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

/-- The encoding-class fields of one instruction at `env.pc`. -/
def Insn.toArmInst (env : Env) (i : Insn) : Except String ArmInst := do
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
    -- C6.2 ROR (immediate) = EXTR Rd, Rs, Rs, #shift
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
    -- C6.2 EXTR (Cranelift `enc_extr`… `0x13800000`)
    if lsb ≥ (if w then 64 else 32) then throw s!"extr lsb {lsb}"
    pure (.DPI (.Extract { sf := b1 w, op21 := 0, N := b1 w, o0 := 0, Rm := ← rm.encZR,
                           imms := BitVec.ofNat 6 lsb, Rn := ← rn.encZR, Rd := ← rd.encZR }))
  | .aluRRRExtend op w rd rn rm e =>
    -- C6.2 ADD/ADDS/SUB/SUBS (extended register), amount 0 (Cranelift `enc_arith_rr_extend`)
    let some (o, S) := op.addSub? | throw s!"aluRRRExtend {repr op}"
    let Rd ← if S == 1 then rd.encZR else rd.encSP
    pure (.DPR (.Add_sub_ext_reg { sf := b1 w, op := o, S, opt := 0, Rm := ← rm.encZR,
                                   option := e.bits, imm3 := 0, Rn := ← rn.encSP, Rd }))
  | .bitRR op w rd rn =>
    -- C6.2 RBIT, REV16, REV32, REV, CLZ, CLS (Data-processing (1 source); Cranelift `enc_bit_rr`)
    let opcode : BitVec 6 ← match op, w with
      | .rbit, _ => pure 0 | .rev16, _ => pure 1 | .rev32, true => pure 2
      | .rev64, true => pure 3 | .rev64, false => pure 2 | .clz, _ => pure 4 | .cls, _ => pure 5
      | .rev32, false => throw "rev32 has no 32-bit form"
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
    -- opcode 111 (Cranelift `enc_fpurr`… `MovToFpu`)
    let (sf, ftype) : BitVec 1 × BitVec 2 ← match s with
      | .size16 => pure (0, 3) | .size32 => pure (0, 0) | .size64 => pure (1, 1)
      | _ => throw s!"fmov size {repr s}"
    pure (.DPSFP (.Conversion_between_FP_and_Int { sf, S := 0, ftype, rmode := 0, opcode := 7,
                                                   Rn := ← rn.encZR, Rd := ← rd.encV }))
  | .umov s rd rn idx =>
    -- C7.2 UMOV: imm5 = idx:1, idx:10, idx:100, idx:1000 (B/H/S/D), imm4 = 0111, Q = (D)
    -- (Cranelift `MovFromVec`)
    let (q, imm5) : BitVec 1 × Nat ← match s with
      | .size8 => pure (0, idx * 2 + 1) | .size16 => pure (0, idx * 4 + 2)
      | .size32 => pure (0, idx * 8 + 4) | .size64 => pure (1, idx * 16 + 8)
      | _ => throw s!"umov size {repr s}"
    pure (.DPSFP (.Advanced_simd_copy { Q := q, op := 0, imm5 := ← uField "umov index" 5 imm5,
                                        imm4 := 7, Rn := ← rn.encV, Rd := ← rd.encZR }))
  | .cnt s rd rn =>
    -- C7.2 CNT (Advanced SIMD two-register miscellaneous, U 0, size 00, opcode 00101)
    let (Q, size) := s.qsize
    if size != 0 then throw s!"cnt arrangement {repr s}"
    pure (.DPSFP (.Advanced_simd_two_reg_misc { Q, U := 0, size, opcode := 5, Rn := ← rn.encV,
                                                Rd := ← rd.encV }))
  | .vecLanes op s rd rn =>
    -- C7.2 ADDV (U 0, opcode 11011), UADDLV (U 1, opcode 00011) (Advanced SIMD across lanes);
    -- arrangements 8B 16B 4H 8H 4S
    let (Q, size) := s.qsize
    if s == .size32x2 || s == .size64x2 then throw s!"addv/uaddlv arrangement {repr s}"
    pure (.DPSFP (.Advanced_simd_across_lanes
      { Q, U := b1 (op == .uaddlv), size, opcode := if op == .addv then 0b11011 else 0b00011,
        Rn := ← rn.encV, Rd := ← rd.encV }))
  | .addp s rd rn rm =>
    -- C7.2 ADDP (vector) (Advanced SIMD three same, U 0, opcode 10111)
    let (Q, size) := s.qsize
    pure (.DPSFP (.Advanced_simd_three_same { Q, U := 0, size, Rm := ← rm.encV, opcode := 0b10111,
                                              Rn := ← rn.encV, Rd := ← rd.encV }))
  | .b t =>
    -- C6.2 B: imm26 = offset / 4, ±128 MiB (Cranelift `enc_jump26`)
    let off ← wordOffset "b" (← env.rel t)
    pure (.BR (.Uncond_branch_imm { op := 0, imm26 := ← sField "b offset" 26 off }))
  | .bcond c t =>
    -- C6.2 B.cond: imm19, ±1 MiB (Cranelift `enc_cbr`)
    let off ← wordOffset "b.cond" (← env.rel t)
    pure (.BR (.Cond_branch_imm { imm19 := ← sField "b.cond offset" 19 off, o0 := 0,
                                  cond := c.bits }))
  | .cbz nz w rt t =>
    -- C6.2 CBZ/CBNZ (Compare and branch (immediate); Cranelift `enc_cmpbr`)
    let off ← wordOffset "cbz" (← env.rel t)
    pure (.BR (.Compare_branch { sf := b1 w, op := b1 nz, imm19 := ← sField "cbz offset" 19 off,
                                 Rt := ← rt.encZR }))
  | .tbz nz rt bit t =>
    -- C6.2 TBZ/TBNZ: b5:b40 = bit number, imm14, ±32 KiB (Cranelift `enc_test_bit_and_branch`)
    if bit ≥ 64 then throw s!"tbz bit {bit}"
    let off ← wordOffset "tbz" (← env.rel t)
    pure (.BR (.Test_branch { b5 := BitVec.ofNat 1 (bit / 32), op := b1 nz,
                              b40 := BitVec.ofNat 5 (bit % 32),
                              imm14 := ← sField "tbz offset" 14 off, Rt := ← rt.encZR }))
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
    let off ← env.rel t
    let imm ← sField "adr offset" 21 off
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
where
  /-- Data-processing (2 source) with `S = 0`. -/
  dp2 (sf : BitVec 1) (opcode : BitVec 6) (Rm Rn Rd : BitVec 5) : ArmInst :=
    .DPR (.Data_processing_two_source { sf, S := 0, Rm, opcode, Rn, Rd })

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

/-- AArch64 ELF relocation types used (ELF for the Arm 64-bit Architecture, §5.7). -/
inductive RelocType where
  | call26 | adrGotPage | ld64GotLo12Nc | adrPrelPgHi21 | addAbsLo12Nc
  deriving DecidableEq, Repr, Inhabited, BEq

/-- ELF `R_AARCH64_*` number. -/
def RelocType.elf : RelocType → Nat
  | .call26 => 283 | .adrGotPage => 311 | .ld64GotLo12Nc => 312 | .adrPrelPgHi21 => 275
  | .addAbsLo12Nc => 277

/-- ELF name (as `llvm-readelf` prints it). -/
def RelocType.elfName : RelocType → String
  | .call26 => "R_AARCH64_CALL26" | .adrGotPage => "R_AARCH64_ADR_GOT_PAGE"
  | .ld64GotLo12Nc => "R_AARCH64_LD64_GOT_LO12_NC" | .adrPrelPgHi21 => "R_AARCH64_ADR_PREL_PG_HI21"
  | .addAbsLo12Nc => "R_AARCH64_ADD_ABS_LO12_NC"

/-- Cranelift's `binemit::Reloc` name (the `relocs.json` schema of `docs/contracts/drivers.md`). -/
def RelocType.craneliftName : RelocType → String
  | .call26 => "Arm64Call" | .adrGotPage => "Aarch64AdrGotPage21"
  | .ld64GotLo12Nc => "Aarch64Ld64GotLo12Nc" | .adrPrelPgHi21 => "Aarch64AdrPrelPgHi21"
  | .addAbsLo12Nc => "Aarch64AddAbsLo12Nc"

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

/-- Byte offsets of the labels of a line list (every instruction and data word is 4 bytes). -/
def labelOffsets (lines : Array Line) : Std.HashMap Lbl Nat := Id.run do
  let mut m : Std.HashMap Lbl Nat := {}
  let mut off := 0
  for ln in lines do
    if let .label l := ln then m := m.insert l off
    off := off + ln.size
  return m

/-- Lay out a function: resolve labels, encode every instruction, collect relocations; the
jump-table words are `target - table` (signed 32-bit). -/
def FnAsm.layout (f : FnAsm) : Except String FnBin := do
  let lbls := labelOffsets f.lines
  let lbl (l : Lbl) : Option Nat := lbls[l]?
  let mut words : Array (BitVec 32) := #[]
  let mut relocs : Array Reloc := #[]
  let mut insns : Array (Nat × Insn) := #[]
  for ln in f.lines do
    let pc := 4 * words.size
    match ln with
    | .ins i _ =>
      let w ← (i.encode { pc, lbl }).mapError fun e => s!"{f.name}+{pc}: `{i.asm f.k}`: {e}"
      words := words.push w
      insns := insns.push (pc, i)
      if let some (type, sym, addend) := i.reloc? then
        relocs := relocs.push { offset := pc, type, sym, addend }
    | .word t b =>
      match lbl t, lbl b with
      | some t, some b =>
        words := words.push (← (sField "jump-table entry" 32 ((t : Int) - b)).mapError
          fun e => s!"{f.name}+{pc}: {e}")
      | _, _ => throw s!"{f.name}+{pc}: undefined label in jump table"
    | .label _ => pure ()
  if 4 * words.size != f.size then throw s!"{f.name}: size {4 * words.size} ≠ {f.size}"
  pure { name := f.name, words, relocs := relocs.toList, traps := f.traps, insns }

/-- Little-endian bytes of code words. -/
def wordsBytes (ws : Array (BitVec 32)) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * ws.size)
  for w in ws do
    let n := w.toNat
    b := b.push (UInt8.ofNat n) |>.push (UInt8.ofNat (n >>> 8)) |>.push (UInt8.ofNat (n >>> 16))
      |>.push (UInt8.ofNat (n >>> 24))
  return b

end Backend

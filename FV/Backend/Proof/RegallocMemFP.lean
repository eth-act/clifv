module

public import FV.Backend.Proof.RegallocMemOS

@[expose] public section

/-!
# Scalar SIMD&FP loads and stores on the Arm model (S11e1)

The float-register counterpart of `RegallocMem.lean`/`RegallocMemCorr.lean` for `fpuLoad`/
`fpuStore` (`ldr`/`ldur`/`str`/`stur` of an `s` or `d` register, Cranelift `FpuLoad32/64`,
`FpuStore32/64`):

* `exec_fpuLoad_line`/`exec_fpuStore_line`: the instruction with a final addressing mode
  (`FinalAM`) encodes, and the model executes it as the value-level access at `AMode.addr`: the
  `sz.bytes` bytes zero-extended into the 128-bit register (`ldV`, Arm's `write_sfp`), or the low
  bytes of the register written to memory; the pc advances by 4;
* `execMInst_fpuLoad`/`execMInst_fpuStore`: the allocated instruction with a `MemMode` mode
  (final forms, or a frame offset through `memFinalize`, `x16` holding large offsets) runs as
  `StepsOk` to that access;
* `fpuLoad_core`/`fpuStore_core` and the per-mode `Corr` lemmas `corr_fpuLoad*`/`corr_fpuStore*`;
* `os_fpuLoad_*`/`os_fpuStore_*`: `OperandsSound` for every addressing mode of `memOk`, with a
  float vreg data register and int vreg address registers.
-/

namespace Backend.Proof

open Backend

/-- The scalar sizes of `fpuLoad`/`fpuStore` (32 and 64 bits). -/
def FpSz (sz : ScalarSize) : Prop := sz = .size32 ∨ sz = .size64

theorem fpSz_of_beq {sz : ScalarSize} (h : (sz == .size32 || sz == .size64) = true) : FpSz sz := by
  cases sz <;> simp_all [FpSz]

/-- The `size` field of a 32/64-bit SIMD&FP load/store (C7.2 LDR/STR (SIMD&FP)). -/
def fpSizeF : ScalarSize → BitVec 2
  | .size64 => 3
  | _ => 2

/-- The 128-bit register value an `ldr st/dt` from `a` leaves: the bytes, zero-extended. -/
def ldV (sz : ScalarSize) (a : BitVec 64) (s : Arm.ArmState) : CV :=
  (Arm.read_mem_bytes sz.bytes a s).setWidth 128

/-- A SIMD&FP load/store without writeback. -/
def fpCls (size opc : BitVec 2) (Rn Rt : BitVec 5) (imm : Arm.LDST.Reg_offset) :
    Arm.LDST.Reg_imm_cls :=
  { size      := size,
    opc       := opc,
    Rn        := Rn,
    Rt        := Rt,
    SIMD?     := true,
    wback     := false,
    postindex := false,
    imm       := imm }

theorem fpSz_bytes {sz : ScalarSize} (h : FpSz sz) : sz.bytes = 4 ∨ sz.bytes = 8 := by
  rcases h with rfl | rfl <;> simp [ScalarSize.bytes]

theorem ldst_fpuLoad (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (str : String) (s : Arm.ArmState)
    (hsp : Rn = 31#5 → Arm.CheckSPAlignment s) :
    Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn Rt imm) str s =
    Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.w (.SFP Rt) (ldV sz (Arm.read_gpr 64 Rn s + imm.value (log2 sz.bytes) s) s) s) := by
  rcases hsz with rfl | rfl <;>
  · by_cases h31 : Rn = 31#5 ∧ ¬ Arm.CheckSPAlignment s
    · exact absurd (hsp h31.1) h31.2
    · simp (config := {decide := true}) [fpCls, fpSizeF, Arm.LDST.exec_reg_imm_common,
        Arm.LDST.reg_imm_operation, ScalarSize.bytes, Arm.LDST.supported_simd_reg_imm,
        Arm.LDST.reg_imm_constrain_unpredictable, Arm.write_sfp, Arm.write_pc, Arm.read_pc, h31,
        ldV, log2]
      rfl

theorem ldst_fpuStore (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (str : String) (s : Arm.ArmState)
    (hsp : Rn = 31#5 → Arm.CheckSPAlignment s) :
    Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn Rt imm) str s =
    Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.write_mem_bytes sz.bytes (Arm.read_gpr 64 Rn s + imm.value (log2 sz.bytes) s)
        ((Arm.r (.SFP Rt) s).setWidth (sz.bytes * 8)) s) := by
  rcases hsz with rfl | rfl <;>
  · by_cases h31 : Rn = 31#5 ∧ ¬ Arm.CheckSPAlignment s
    · exact absurd (hsp h31.1) h31.2
    · simp (config := {decide := true}) [fpCls, fpSizeF, Arm.LDST.exec_reg_imm_common,
        Arm.LDST.reg_imm_operation, ScalarSize.bytes, Arm.LDST.supported_simd_reg_imm,
        Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_sfp, Arm.write_pc,
        Arm.read_pc, h31, log2]
      rfl

theorem ldstur_fpuLoad (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5) (imm9 : BitVec 9)
    (s : Arm.ArmState) (hsp : Rn = 31#5 → Arm.CheckSPAlignment s) :
    Arm.LDST.exec_ldstur
      { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := imm9, Rn := Rn, Rt := Rt } s =
    Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.w (.SFP Rt) (ldV sz (Arm.read_gpr 64 Rn s + BitVec.signExtend 64 imm9) s) s) := by
  rcases hsz with rfl | rfl <;>
  · by_cases h31 : Rn = 31#5 ∧ ¬ Arm.CheckSPAlignment s
    · exact absurd (hsp h31.1) h31.2
    · simp (config := {decide := true}) [Arm.LDST.exec_ldstur, fpSizeF, ScalarSize.bytes,
        Arm.write_sfp, Arm.write_pc, Arm.read_pc, h31, ldV,
        Arm.r_of_w_different]
      rfl

theorem ldstur_fpuStore (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5) (imm9 : BitVec 9)
    (s : Arm.ArmState) (hsp : Rn = 31#5 → Arm.CheckSPAlignment s) :
    Arm.LDST.exec_ldstur
      { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := imm9, Rn := Rn, Rt := Rt } s =
    Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.write_mem_bytes sz.bytes (Arm.read_gpr 64 Rn s + BitVec.signExtend 64 imm9)
        ((Arm.r (.SFP Rt) s).setWidth (sz.bytes * 8)) s) := by
  rcases hsz with rfl | rfl <;>
  · by_cases h31 : Rn = 31#5 ∧ ¬ Arm.CheckSPAlignment s
    · exact absurd (hsp h31.1) h31.2
    · simp (config := {decide := true}) [Arm.LDST.exec_ldstur, fpSizeF, ScalarSize.bytes,
        Arm.read_sfp, Arm.write_pc, Arm.read_pc, h31, Arm.r_of_write_mem_bytes]
      rfl

/-- `LDR/STR St/Dt` (unsigned offset). -/
def fpUimmInst (size opc : BitVec 2) (imm12 : BitVec 12) (Rn Rt : BitVec 5) : Arm.ArmInst :=
  .LDST (.Reg_unsigned_imm { size := size, V := 1#1, opc := opc, imm12 := imm12, Rn := Rn, Rt := Rt })

/-- `LDUR/STUR St/Dt`. -/
def fpUnscInst (size opc : BitVec 2) (imm9 : BitVec 9) (Rn Rt : BitVec 5) : Arm.ArmInst :=
  .LDST (.Reg_unscaled_imm { size := size, VR := 1#1, opc := opc, imm9 := imm9, Rn := Rn, Rt := Rt })

/-- `LDR/STR St/Dt` (register offset). -/
def fpRegInst (size opc : BitVec 2) (Rm : BitVec 5) (option : BitVec 3) (S : BitVec 1)
    (Rn Rt : BitVec 5) : Arm.ArmInst :=
  .LDST (.Reg_reg_offset
    { size := size, V := 1#1, opc := opc, Rm := Rm, option := option, S := S, Rn := Rn, Rt := Rt })

theorem encV_v' {d : Nat} (hd : d < 32) : (Reg.v d).encV = .ok (BitVec.ofNat 5 d) := by
  simp [Reg.encV, show d ≤ 31 by omega]

theorem fp_log2 {sz : ScalarSize} (hsz : FpSz sz) : log2 sz.bytes < 64 := by
  rcases hsz with rfl | rfl <;> decide

/-- **An `ldr st/dt`/`ldur` with a final addressing mode** on the Arm model. -/
theorem exec_fpuLoad_line (env : Env) (ctx : FnCtx) (sz : ScalarSize) (hsz : FpSz sz) (d : Nat)
    (hd : d < 32) (m : AMode) (hm : FinalAM sz.bytes m) (s : Arm.ArmState)
    (hsp : m.base = .sp → Arm.CheckSPAlignment s) :
    ∃ ai, Insn.toArmInst env (.fpuLoad sz (.v d) m) = .ok ai ∧
      Arm.exec_inst ai s = Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.w (.SFP (BitVec.ofNat 5 d)) (ldV sz (m.addr ctx sz.bytes s) s) s) := by
  have hb48 := fpSz_bytes hsz
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨fpUimmInst (fpSizeF sz) 1 (BitVec.ofNat 12 (off / sz.bytes)) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpUimmInst (fpSizeF sz) 1 (BitVec.ofNat 12 (off / sz.bytes))
          Rn (BitVec.ofNat 5 d)) s = Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn
            (BitVec.ofNat 5 d) (.uimm12 (BitVec.ofNat 12 (off / sz.bytes)))) str s := ⟨_, rfl⟩
      rw [e, ldst_fpuLoad sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact uimm_value sz.bytes (by omega) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨fpUnscInst (fpSizeF sz) 1 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUnscInst] <;> rfl
    · have e : Arm.exec_inst (fpUnscInst (fpSizeF sz) 1 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_ldstur
            { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := BitVec.ofInt 9 off, Rn := Rn,
              Rt := BitVec.ofNat 5 d } s := rfl
      rw [e, ldstur_fpuLoad sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, hr]
      congr 1
      exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 1 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 1 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 0#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_fpuLoad sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
      apply BitVec.eq_of_toNat_eq
      simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
      exact (regX s rm).isLt
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 1 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 1 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 1#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_fpuLoad sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
      exact uxtx_shift _ _ (fp_log2 hsz)
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 1 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 1 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 1#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_fpuLoad sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 1 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 1 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 0#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_fpuLoad sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      rfl
  | _ => simp [FinalAM] at hm

/-- **An `str st/dt`/`stur` with a final addressing mode** on the Arm model. -/
theorem exec_fpuStore_line (env : Env) (ctx : FnCtx) (sz : ScalarSize) (hsz : FpSz sz) (d : Nat)
    (hd : d < 32) (m : AMode) (hm : FinalAM sz.bytes m) (s : Arm.ArmState)
    (hsp : m.base = .sp → Arm.CheckSPAlignment s) :
    ∃ ai, Insn.toArmInst env (.fpuStore sz (.v d) m) = .ok ai ∧
      Arm.exec_inst ai s = Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.write_mem_bytes sz.bytes (m.addr ctx sz.bytes s)
          ((Arm.r (.SFP (BitVec.ofNat 5 d)) s).setWidth (sz.bytes * 8)) s) := by
  have hb48 := fpSz_bytes hsz
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨fpUimmInst (fpSizeF sz) 0 (BitVec.ofNat 12 (off / sz.bytes)) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpUimmInst (fpSizeF sz) 0 (BitVec.ofNat 12 (off / sz.bytes))
          Rn (BitVec.ofNat 5 d)) s = Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn
            (BitVec.ofNat 5 d) (.uimm12 (BitVec.ofNat 12 (off / sz.bytes)))) str s := ⟨_, rfl⟩
      rw [e, ldst_fpuStore sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact uimm_value sz.bytes (by omega) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨fpUnscInst (fpSizeF sz) 0 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUnscInst] <;> rfl
    · have e : Arm.exec_inst (fpUnscInst (fpSizeF sz) 0 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_ldstur
            { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := BitVec.ofInt 9 off, Rn := Rn,
              Rt := BitVec.ofNat 5 d } s := rfl
      rw [e, ldstur_fpuStore sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, hr]
      congr 1
      exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 0 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 0 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 0#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_fpuStore sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
      apply BitVec.eq_of_toNat_eq
      simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
      exact (regX s rm).isLt
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 0 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 0 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 1#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_fpuStore sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
      exact uxtx_shift _ _ (fp_log2 hsz)
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 0 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 0 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 1#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_fpuStore sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨fpRegInst (fpSizeF sz) 0 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (fpRegInst (fpSizeF sz) 0 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 0#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [fpRegInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_fpuStore sz hsz Rn _ _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      rfl
  | _ => simp [FinalAM] at hm

theorem ldV_congr_mem {s t : Arm.ArmState} (h : t.mem = s.mem) (sz : ScalarSize) (a : BitVec 64) :
    ldV sz a t = ldV sz a s := by
  simp only [ldV]
  rw [read_mem_bytes_congr (s := t) (t := s) _ a (fun k _ => by rw [h])]

/-- **An `fpuLoad` on the Arm model** (into `v d`): its lines run without error from an
aligned state; `v d` gets the loaded value at `AMode.addr`, the pc advances past the lines, `x16`
may hold a scratch value (large slot offsets). -/
theorem execMInst_fpuLoad (ctx : FnCtx) (env : Env) (sz : ScalarSize) (hsz : FpSz sz) {d : Nat}
    (hd : d < 32) (m : AMode) (fl : Clif.MemFlags) (hm : MemMode sz.bytes m) (s : Arm.ArmState)
    (halign : Arm.CheckSPAlignment s) :
    ∃ ls o, MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} = .ok (ls, {}) ∧
      StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
        (Arm.w (.SFP (BitVec.ofNat 5 d)) (ldV sz (m.addr ctx sz.bytes s) s) (x16w o s))) := by
  have hbp : 0 < sz.bytes := by rcases fpSz_bytes hsz with h | h <;> omega
  have single : ∀ m' : AMode, FinalAM sz.bytes m' → (m'.base = .sp → Arm.CheckSPAlignment s) →
      m'.addr ctx sz.bytes s = m.addr ctx sz.bytes s →
      StepsOk env [.ins (.fpuLoad sz (.v d) m') fl.trapCode] s
        (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * 1))
          (Arm.w (.SFP (BitVec.ofNat 5 d)) (ldV sz (m.addr ctx sz.bytes s) s) (x16w none s))) := by
    intro m' hf hs ha
    obtain ⟨ai, hai, he⟩ := exec_fpuLoad_line env ctx sz hsz d hd m' hf s hs
    refine ⟨ai, hai, ?_, ?_, ?_, ?_⟩
    · rw [he, Arm.r_of_w_same]
    · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    · rw [he, Arm.w_program, Arm.w_program]
    · simp only [StepsOk, he, ha, x16w]
  -- the large offset in `x16`: `loadConst64` then the load through `[B, x16, sxtx]`
  have big : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      m.addr ctx sz.bytes s = regX s B + BitVec.ofInt 64 o →
      MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} =
        .ok (loadConst64 (.x 16) (u64 o) ++
          [.ins (.fpuLoad sz (.v d) (.regExtended B (.x 16) .sxtx)) fl.trapCode], {}) →
      ∃ ls o, MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} = .ok (ls, {}) ∧
        StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
          (Arm.w (.SFP (BitVec.ofNat 5 d)) (ldV sz (m.addr ctx sz.bytes s) s) (x16w o s))) := by
    intro B o hB ha hl
    have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
    refine ⟨_, some (BitVec.ofNat 64 (u64 o)), hl, ?_⟩
    have hA := steps_loadConst64 env (n := 16) (by omega) (u64 o) s
    let L := (loadConst64 (.x 16) (u64 o)).length
    let S1 := pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * L)) (BitVec.ofNat 64 (u64 o))
    have hS1 : S1.mem = s.mem ∧ spOf S1 = spOf s ∧ Arm.r .PC S1 = Arm.r .PC s + BitVec.ofNat 64 (4 * L) ∧
        Arm.r (.GPR 16#5) S1 = BitVec.ofNat 64 (u64 o) ∧ Arm.r .ERR S1 = Arm.r .ERR s ∧ S1.program = s.program := by
      simp [S1, pcx, Arm.ArmState.mem_w_eq_mem, spOf, Arm.r_of_w_different, Arm.r_of_w_same, Arm.w_program]
    have hal1 : Arm.CheckSPAlignment S1 := by
      have e : Arm.r (.GPR 31#5) S1 = Arm.r (.GPR 31#5) s := hS1.2.1
      simpa [Arm.CheckSPAlignment, Arm.read_gpr, e] using halign
    have hBS : regX S1 B = regX s B := by
      rcases hB with rfl | rfl
      · exact hS1.2.1
      · simp [S1, pcx, regX, rnum, Arm.r_of_w_different]
    obtain ⟨ai, hai, he⟩ := exec_fpuLoad_line { env with pc := env.pc + 4 * L } ctx sz hsz d hd
      (.regExtended B (.x 16) .sxtx) ⟨hBok, by simp [IdxOk], by simp⟩ S1 (fun _ => hal1)
    have haddr : AMode.addr ctx (.regExtended B (.x 16) .sxtx) sz.bytes S1 = m.addr ctx sz.bytes s := by
      rw [show AMode.addr ctx (.regExtended B (.x 16) .sxtx) sz.bytes S1 = regX S1 B +
          Arm.extend_reg (regX S1 (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl]
      rw [hBS, ha, show regX S1 (.x 16) = BitVec.ofNat 64 (u64 o) from hS1.2.2.2.1,
        show ExtendOp.sxtx.bits = 7#3 from rfl, sxtx_id, ofNat_u64]
    have hld : ldV sz (m.addr ctx sz.bytes s) S1 = ldV sz (m.addr ctx sz.bytes s) s :=
      ldV_congr_mem hS1.1 sz _
    refine StepsOk.append hA ⟨ai, hai, ?_, ?_, ?_, ?_⟩
    · rw [he, Arm.r_of_w_same]
    · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    · rw [he, Arm.w_program, Arm.w_program]
    · simp only [StepsOk]
      rw [he, haddr, hld, hS1.2.2.1]
      simp only [S1, pcx, x16w, List.length_append, List.length_cons, List.length_nil]
      rw [Arm.w_of_w_commute (fld1 := .SFP _) (fld2 := .PC) (by simp), Arm.w_of_w_shadow,
        BitVec.add_assoc]
      congr 2
      apply BitVec.eq_of_toNat_eq; simp [L]; omega
  -- `memFinalize`'s `fin B o` (base `sp` or `fp`, any offset)
  have base : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      m.addr ctx sz.bytes s = regX s B + BitVec.ofInt 64 o →
      (∀ k, simm9? o = some k → MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} =
        .ok ([.ins (.fpuLoad sz (.v d) (.unscaled B k)) fl.trapCode], {})) →
      (simm9? o = none → ∀ k, uimm12Scaled? o sz.bytes = some k →
        MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} =
          .ok ([.ins (.fpuLoad sz (.v d) (.unsignedOffset B k)) fl.trapCode], {})) →
      (simm9? o = none → uimm12Scaled? o sz.bytes = none →
        MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} =
          .ok (loadConst64 (.x 16) (u64 o) ++
            [.ins (.fpuLoad sz (.v d) (.regExtended B (.x 16) .sxtx)) fl.trapCode], {})) →
      ∃ ls o, MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} = .ok (ls, {}) ∧
        StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
          (Arm.w (.SFP (BitVec.ofNat 5 d)) (ldV sz (m.addr ctx sz.bytes s) s) (x16w o s))) := by
    intro B o hB ha h1 h2 h3
    have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
    cases h9 : simm9? o with
    | some k =>
      have hk : k = o ∧ -256 ≤ k ∧ k ≤ 255 := by
        simp only [simm9?] at h9; split at h9 <;> simp_all
      refine ⟨_, none, h1 k h9, single (.unscaled B k) ⟨hBok, hk.2.1, by omega⟩ (fun _ => halign) ?_⟩
      rw [ha]; simp [AMode.addr, hk.1]
    | none =>
      cases hu : uimm12Scaled? o sz.bytes with
      | some k =>
        have hk : (k : Int) = o ∧ k % sz.bytes = 0 ∧ k ≤ 4095 * sz.bytes := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
          · cases hu
        refine ⟨_, none, h2 h9 k hu, single (.unsignedOffset B k) ⟨hBok, hk.2.1,
          by have := Nat.div_le_div_right (c := sz.bytes) hk.2.2; rw [Nat.mul_div_cancel _ hbp] at this; omega⟩
          (fun _ => halign) ?_⟩
        rw [ha]
        simp only [AMode.addr]
        congr 1
        rw [← hk.1]; rfl
      | none => exact big B o hB ha (h3 h9 hu)
  cases m with
  | slotOffset off =>
    exact base .sp (off + ctx.slotBase) (.inl rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, h9, hu])
  | spOffset off =>
    exact base .sp off (.inl rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, h9, hu])
  | fpOffset off =>
    exact base (.x 29) off (.inr rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, Reg.fp, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
  | _ =>
    simp only [MemMode] at hm <;>
    exact ⟨_, none, by simp [MInst.lines, memFinalize_final ctx _ hm], single _ hm (fun _ => halign) rfl⟩


/-- **An `fpuStore` on the Arm model** (of `v d`): the low `sz.bytes` bytes of `v d` are written
at `AMode.addr`, the pc advances past the lines, `x16` may hold a scratch value. -/
theorem execMInst_fpuStore (ctx : FnCtx) (env : Env) (sz : ScalarSize) (hsz : FpSz sz) {d : Nat}
    (hd : d < 32) (m : AMode) (fl : Clif.MemFlags) (hm : MemMode sz.bytes m) (s : Arm.ArmState)
    (halign : Arm.CheckSPAlignment s) :
    ∃ ls o, MInst.lines ctx (.fpuStore sz (.v d) m fl) {} = .ok (ls, {}) ∧
      StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
        (Arm.write_mem_bytes sz.bytes (m.addr ctx sz.bytes s)
          ((Arm.r (.SFP (BitVec.ofNat 5 d)) s).setWidth (sz.bytes * 8)) (x16w o s))) := by
  have hbp : 0 < sz.bytes := by rcases fpSz_bytes hsz with h | h <;> omega
  have single : ∀ m' : AMode, FinalAM sz.bytes m' → (m'.base = .sp → Arm.CheckSPAlignment s) →
      m'.addr ctx sz.bytes s = m.addr ctx sz.bytes s →
      StepsOk env [.ins (.fpuStore sz (.v d) m') fl.trapCode] s
        (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * 1))
          (Arm.write_mem_bytes sz.bytes (m.addr ctx sz.bytes s)
            ((Arm.r (.SFP (BitVec.ofNat 5 d)) s).setWidth (sz.bytes * 8)) (x16w none s))) := by
    intro m' hf hs ha
    obtain ⟨ai, hai, he⟩ := exec_fpuStore_line env ctx sz hsz d hd m' hf s hs
    refine ⟨ai, hai, ?_, ?_, ?_, ?_⟩
    · rw [he, Arm.r_of_w_same]
    · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]
    · rw [he, Arm.w_program, Arm.write_mem_bytes_program]
    · simp only [StepsOk, he, ha, x16w]
  have big : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      m.addr ctx sz.bytes s = regX s B + BitVec.ofInt 64 o →
      MInst.lines ctx (.fpuStore sz (.v d) m fl) {} =
        .ok (loadConst64 (.x 16) (u64 o) ++
          [.ins (.fpuStore sz (.v d) (.regExtended B (.x 16) .sxtx)) fl.trapCode], {}) →
      ∃ ls o, MInst.lines ctx (.fpuStore sz (.v d) m fl) {} = .ok (ls, {}) ∧
        StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
          (Arm.write_mem_bytes sz.bytes (m.addr ctx sz.bytes s)
            ((Arm.r (.SFP (BitVec.ofNat 5 d)) s).setWidth (sz.bytes * 8)) (x16w o s))) := by
    intro B o hB ha hl
    have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
    refine ⟨_, some (BitVec.ofNat 64 (u64 o)), hl, ?_⟩
    have hA := steps_loadConst64 env (n := 16) (by omega) (u64 o) s
    let L := (loadConst64 (.x 16) (u64 o)).length
    let S1 := pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * L)) (BitVec.ofNat 64 (u64 o))
    have hS1 : S1.mem = s.mem ∧ spOf S1 = spOf s ∧ Arm.r .PC S1 = Arm.r .PC s + BitVec.ofNat 64 (4 * L) ∧
        Arm.r (.GPR 16#5) S1 = BitVec.ofNat 64 (u64 o) ∧ Arm.r .ERR S1 = Arm.r .ERR s ∧ S1.program = s.program := by
      simp [S1, pcx, Arm.ArmState.mem_w_eq_mem, spOf, Arm.r_of_w_different, Arm.r_of_w_same, Arm.w_program]
    have hal1 : Arm.CheckSPAlignment S1 := by
      have e : Arm.r (.GPR 31#5) S1 = Arm.r (.GPR 31#5) s := hS1.2.1
      simpa [Arm.CheckSPAlignment, Arm.read_gpr, e] using halign
    have hBS : regX S1 B = regX s B := by
      rcases hB with rfl | rfl
      · exact hS1.2.1
      · simp [S1, pcx, regX, rnum, Arm.r_of_w_different]
    obtain ⟨ai, hai, he⟩ := exec_fpuStore_line { env with pc := env.pc + 4 * L } ctx sz hsz d hd
      (.regExtended B (.x 16) .sxtx) ⟨hBok, by simp [IdxOk], by simp⟩ S1 (fun _ => hal1)
    have haddr : AMode.addr ctx (.regExtended B (.x 16) .sxtx) sz.bytes S1 = m.addr ctx sz.bytes s := by
      rw [show AMode.addr ctx (.regExtended B (.x 16) .sxtx) sz.bytes S1 = regX S1 B +
          Arm.extend_reg (regX S1 (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl]
      rw [hBS, ha, show regX S1 (.x 16) = BitVec.ofNat 64 (u64 o) from hS1.2.2.2.1,
        show ExtendOp.sxtx.bits = 7#3 from rfl, sxtx_id, ofNat_u64]
    have hld : Arm.r (.SFP (BitVec.ofNat 5 d)) S1 = Arm.r (.SFP (BitVec.ofNat 5 d)) s := by
      simp [S1, pcx, Arm.r_of_w_different]
    refine StepsOk.append hA ⟨ai, hai, ?_, ?_, ?_, ?_⟩
    · rw [he, Arm.r_of_w_same]
    · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]
    · rw [he, Arm.w_program, Arm.write_mem_bytes_program]
    · simp only [StepsOk]
      rw [he, haddr, hld, hS1.2.2.1]
      simp only [S1, pcx, x16w, List.length_append, List.length_cons, List.length_nil]
      rw [write_mem_bytes_w (f := .PC), Arm.w_of_w_shadow, BitVec.add_assoc]
      congr 2
      apply BitVec.eq_of_toNat_eq; simp [L]; omega
  have base : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      m.addr ctx sz.bytes s = regX s B + BitVec.ofInt 64 o →
      (∀ k, simm9? o = some k → MInst.lines ctx (.fpuStore sz (.v d) m fl) {} =
        .ok ([.ins (.fpuStore sz (.v d) (.unscaled B k)) fl.trapCode], {})) →
      (simm9? o = none → ∀ k, uimm12Scaled? o sz.bytes = some k →
        MInst.lines ctx (.fpuStore sz (.v d) m fl) {} =
          .ok ([.ins (.fpuStore sz (.v d) (.unsignedOffset B k)) fl.trapCode], {})) →
      (simm9? o = none → uimm12Scaled? o sz.bytes = none →
        MInst.lines ctx (.fpuStore sz (.v d) m fl) {} =
          .ok (loadConst64 (.x 16) (u64 o) ++
            [.ins (.fpuStore sz (.v d) (.regExtended B (.x 16) .sxtx)) fl.trapCode], {})) →
      ∃ ls o, MInst.lines ctx (.fpuStore sz (.v d) m fl) {} = .ok (ls, {}) ∧
        StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
          (Arm.write_mem_bytes sz.bytes (m.addr ctx sz.bytes s)
            ((Arm.r (.SFP (BitVec.ofNat 5 d)) s).setWidth (sz.bytes * 8)) (x16w o s))) := by
    intro B o hB ha h1 h2 h3
    have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
    cases h9 : simm9? o with
    | some k =>
      have hk : k = o ∧ -256 ≤ k ∧ k ≤ 255 := by
        simp only [simm9?] at h9; split at h9 <;> simp_all
      refine ⟨_, none, h1 k h9, single (.unscaled B k) ⟨hBok, hk.2.1, by omega⟩ (fun _ => halign) ?_⟩
      rw [ha]; simp [AMode.addr, hk.1]
    | none =>
      cases hu : uimm12Scaled? o sz.bytes with
      | some k =>
        have hk : (k : Int) = o ∧ k % sz.bytes = 0 ∧ k ≤ 4095 * sz.bytes := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
          · cases hu
        refine ⟨_, none, h2 h9 k hu, single (.unsignedOffset B k) ⟨hBok, hk.2.1,
          by have := Nat.div_le_div_right (c := sz.bytes) hk.2.2; rw [Nat.mul_div_cancel _ hbp] at this; omega⟩
          (fun _ => halign) ?_⟩
        rw [ha]
        simp only [AMode.addr]
        congr 1
        rw [← hk.1]; rfl
      | none => exact big B o hB ha (h3 h9 hu)
  cases m with
  | slotOffset off =>
    exact base .sp (off + ctx.slotBase) (.inl rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, h9, hu])
  | spOffset off =>
    exact base .sp off (.inl rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, h9, hu])
  | fpOffset off =>
    exact base (.x 29) off (.inr rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, Reg.fp, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
  | _ =>
    simp only [MemMode] at hm <;>
    exact ⟨_, none, by simp [MInst.lines, memFinalize_final ctx _ hm], single _ hm (fun _ => halign) rfl⟩

/-! ## The allocated/canonical correspondence -/

theorem ldV_congr {F : BitVec 64 → Prop} {s t : Arm.ArmState} (sz : ScalarSize) {a : BitVec 64}
    (h : ∀ x, ¬ F x → s.mem x = t.mem x) (hav : Avoids F sz.bytes a) : ldV sz a s = ldV sz a t := by
  simp only [ldV]
  rw [read_mem_bytes_congr _ a (fun k hk => h _ (hav k hk))]

/-- The post-state of a float load into `v a`. -/
def fldPost (s : Arm.ArmState) (P : BitVec 64) (a : Nat) (V : CV) (o : Option (BitVec 64)) :
    Arm.ArmState :=
  Arm.w .PC P (Arm.w (.SFP (BitVec.ofNat 5 a)) V (x16w o s))

theorem fldPost_sw {F : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorld F s t)
    {P P' : BitVec 64} (a b : Nat) (V V' : CV) (o o' : Option (BitVec 64)) :
    SameWorld F (fldPost s P a V o) (fldPost t P' b V' o') :=
  SameWorld.w_right (by simp [Masked]) (SameWorld.w_left (by simp [Masked])
    (SameWorld.w_right (by simp [Masked]) (SameWorld.w_left (by simp [Masked])
      (sameWorld_x16w o o' h))))

theorem fldPost_facts (s : Arm.ArmState) (P : BitVec 64) {a : Nat} (ha : a < 32) (V : CV)
    (o : Option (BitVec 64)) :
    spOf (fldPost s P a V o) = spOf s ∧ (fldPost s P a V o).mem = s.mem ∧
      regVal (fldPost s P a V o) (.v a) = V ∧
      ∀ r, r.allocatable = true → r ≠ .v a → regVal (fldPost s P a V o) r = regVal s r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [fldPost, spOf]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    exact (x16w_facts o s).2.2.2.2
  · simp only [fldPost, Arm.ArmState.mem_w_eq_mem]; exact (x16w_facts o s).2.2.2.1
  · simp [fldPost, regVal, rnum, Arm.r_of_w_different, Arm.r_of_w_same]
  · intro r hr hne
    rcases allocatable_cases hr with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · have e2 : BitVec.ofNat 5 k ≠ 16#5 := rnum_ne (a := k) (b := 16) (by omega) (by omega) (by omega)
      cases o <;> simp [fldPost, regVal, rnum, x16w, Arm.r_of_w_different, e2]
    · have hka : k ≠ a := fun e => hne (by rw [e])
      have e1 : BitVec.ofNat 5 k ≠ BitVec.ofNat 5 a := rnum_ne (by omega) (by omega) hka
      cases o <;> simp [fldPost, regVal, rnum, x16w, Arm.r_of_w_different, e1]

/-- The allocated/canonical correspondence of one float load (the part of `Corr` independent
of the operand list). -/
theorem fpuLoad_core {F : BitVec 64 → Prop} (ctx : FnCtx) (env : Env) (sz : ScalarSize) (hsz : FpSz sz)
    (fl : Clif.MemFlags) {n0 : Nat} (hn0 : n0 < 32) {m mC : AMode}
    (hm : MemMode sz.bytes m) (hmC : MemMode sz.bytes mC) {s t t' : Arm.ArmState}
    (hal : Arm.CheckSPAlignment s) (hwt : SameWorld F s t)
    (hsp_t : Arm.r (.GPR 31#5) t = Arm.r (.GPR 31#5) s) (hmem : ∀ x, ¬ F x → t.mem x = s.mem x)
    (hacc : AccessOk F ctx (.fpuLoad sz (.v 0) mC fl) t)
    (hex : execMInst ctx env0 (.fpuLoad sz (.v 0) mC fl) t = some t')
    (haddr : mC.addr ctx sz.bytes t = m.addr ctx sz.bytes s) :
    ∃ S, execMInst ctx env (.fpuLoad sz (.v n0) m fl) s = some S ∧ SameWorld F S t' ∧
      FrameKeep F s S ∧ regVal S (.v n0) = regVal t' (.v 0) ∧
      ∀ r, r.allocatable = true → r ≠ .v n0 → regVal S r = regVal s r := by
  obtain ⟨ls, o, hl, hS⟩ := execMInst_fpuLoad ctx env sz hsz (d := n0) hn0 m fl hm s hal
  obtain ⟨lsC, oC, hlC, hT⟩ := execMInst_fpuLoad ctx env0 sz hsz (d := 0) (by omega) mC fl hmC t
    (align_of_spEq hsp_t hal)
  simp only [execMInst, hlC, hT.exec, Option.some.injEq] at hex
  subst hex
  have hav : Avoids F sz.bytes (m.addr ctx sz.bytes s) := by
    have := hacc (mC.addr ctx sz.bytes t, sz.bytes) (by simp [MInst.accesses])
    rw [← haddr]; exact this
  have hld : ldV sz (mC.addr ctx sz.bytes t) t = ldV sz (m.addr ctx sz.bytes s) s := by
    rw [haddr]; exact ldV_congr sz hmem hav
  obtain ⟨f1, f2, f3, f4⟩ := fldPost_facts s (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length)) hn0
    (ldV sz (m.addr ctx sz.bytes s) s) o
  obtain ⟨-, -, g3, -⟩ := fldPost_facts t (Arm.r .PC t + BitVec.ofNat 64 (4 * lsC.length))
    (a := 0) (by omega) (ldV sz (mC.addr ctx sz.bytes t) t) oC
  refine ⟨fldPost s (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length)) n0
      (ldV sz (m.addr ctx sz.bytes s) s) o,
    by simp only [execMInst, hl]; exact hS.exec, fldPost_sw hwt _ _ _ _ _ _,
    ⟨f1, fun a _ => by rw [f2]⟩, ?_, f4⟩
  rw [f3, ← hld]; exact g3.symm

/-- The allocated/canonical correspondence of one float store. -/
theorem fpuStore_core {F : BitVec 64 → Prop} (ctx : FnCtx) (env : Env) (sz : ScalarSize) (hsz : FpSz sz)
    (fl : Clif.MemFlags) {n0 : Nat} (hn0 : n0 < 32) {m mC : AMode}
    (hm : MemMode sz.bytes m) (hmC : MemMode sz.bytes mC) {s t t' : Arm.ArmState}
    (hal : Arm.CheckSPAlignment s) (hwt : SameWorld F s t)
    (hsp_t : Arm.r (.GPR 31#5) t = Arm.r (.GPR 31#5) s)
    (hv_t : Arm.r (.SFP (BitVec.ofNat 5 0)) t = Arm.r (.SFP (BitVec.ofNat 5 n0)) s)
    (hacc : AccessOk F ctx (.fpuStore sz (.v 0) mC fl) t)
    (hex : execMInst ctx env0 (.fpuStore sz (.v 0) mC fl) t = some t')
    (haddr : mC.addr ctx sz.bytes t = m.addr ctx sz.bytes s) :
    ∃ S, execMInst ctx env (.fpuStore sz (.v n0) m fl) s = some S ∧ SameWorld F S t' ∧
      FrameKeep F s S ∧ ∀ r, r.allocatable = true → regVal S r = regVal s r := by
  obtain ⟨ls, o, hl, hS⟩ := execMInst_fpuStore ctx env sz hsz (d := n0) hn0 m fl hm s hal
  obtain ⟨lsC, oC, hlC, hT⟩ := execMInst_fpuStore ctx env0 sz hsz (d := 0) (by omega) mC fl hmC t
    (align_of_spEq hsp_t hal)
  simp only [execMInst, hlC, hT.exec, Option.some.injEq] at hex
  subst hex
  have hav : Avoids F sz.bytes (m.addr ctx sz.bytes s) := by
    have := hacc (mC.addr ctx sz.bytes t, sz.bytes) (by simp [MInst.accesses])
    rw [← haddr]; exact this
  refine ⟨_, by simp only [execMInst, hl]; exact hS.exec, ?_, ⟨?_, fun a ha => ?_⟩, fun r hr => ?_⟩
  · refine SameWorld.w_right (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) ?_)
    refine SameWorld.write_mem_bytes' haddr.symm (by rw [hv_t]) (sameWorld_x16w o oC hwt)
  · simp only [spOf]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]
    exact (x16w_facts o s).2.2.2.2
  · rw [Arm.ArmState.mem_w_eq_mem, mem_write_mem_bytes_ne _ _ _ _ _ (fun k hk e => hav k hk (e ▸ ha)),
      (x16w_facts o s).2.2.2.1]
  · rcases allocatable_cases hr with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · have e2 : rnum k ≠ 16#5 := rnum_ne (a := k) (b := 16) (by omega) (by omega) (by omega)
      cases o <;> simp [regVal, x16w, Arm.r_of_w_different, Arm.r_of_write_mem_bytes, e2]
    · cases o <;> simp [regVal, x16w, Arm.r_of_w_different, Arm.r_of_write_mem_bytes]

/-! ## Generic `Corr` lemmas -/

/-- Close the `Corr` of a float load from `fpuLoad_core`'s result. -/
syntax "fload_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| fload_fin) => `(tactic| (
    obtain ⟨S, h1, h2, h3, h4, h5⟩ := hcore
    exact ⟨S, h1, h2, h3, by simp [defVals, Operand.isDef, h4], fun r hr hnd => h5 r hr
      (fun e => hnd ⟨⟨d, .float, .def, .late, .reg⟩, .v n0⟩ (by simp) rfl e.symm)⟩))

/-- Close the `Corr` of a float store from `fpuStore_core`'s result. -/
syntax "fstore_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| fstore_fin) => `(tactic| (
    obtain ⟨S, h1, h2, h3, h5⟩ := hcore
    exact ⟨S, h1, h2, h3, by simp [defVals, Operand.isDef], fun r hr _ => h5 r hr⟩))

theorem corr_fpuLoad0g (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize)
    (hsz : FpSz sz) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (hmm : MemMode sz.bytes am)
    (hA : ∀ s w : Arm.ArmState, SameWorld F s w → am.addr ctx sz.bytes w = am.addr ctx sz.bytes s) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩] (fun r => .fpuLoad sz (r.getD 0 .xzr) am fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, rfl⟩ := regs1 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨n0, rfl, hn0⟩
  have hcanon : canonRegs #[⟨d, .float, .def, .late, .reg⟩] = #[.v 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .def, .late, .reg⟩] (canonRegs #[⟨d, .float, .def, .late, .reg⟩])
      (useVals #[⟨d, .float, .def, .late, .reg⟩] #[.v n0] s) w = w := by
    simp [placeUses, useVals, hcanon, Operand.isUse]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hsp : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s := sw_r_eq hw (by simp [Masked])
  have hcore := fpuLoad_core ctx env sz hsz fl hn0 (m := am) (mC := am)
    hmm hmm hal hw hsp (fun x hx => (hw.2.1 x hx).symm) hacc hex (hA s w hw)
  fload_fin

theorem corr_fpuLoad1 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize)
    (hsz : FpSz sz) (d n : Nat) (fl : Clif.MemFlags) (A : Reg → AMode) (g : BitVec 64 → BitVec 64)
    (hA : ∀ a : Nat, a < 29 → MemMode sz.bytes (A (.x a)))
    (hg : ∀ (a : Nat) s, (A (.x a)).addr ctx sz.bytes s = g (Arm.r (.GPR (rnum a)) s)) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .fpuLoad sz (r.getD 0 .xzr) (A (r.getD 1 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] =
      #[.v 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.v n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := fpuLoad_core ctx env sz hsz fl hn0 (m := A (.x n1)) (mC := A (.x 1))
    (hA _ hn1.1) (hA 1 (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) hw)
    (by rw [Arm.r_of_w_different (by simp)]; exact sw_r_eq hw (by simp [Masked]))
    (fun x hx => by rw [Arm.ArmState.mem_w_eq_mem]; exact (hw.2.1 x hx).symm) hacc hex
    (by rw [hg, hg]; simp [rnum])
  fload_fin

theorem corr_fpuLoad2 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize)
    (hsz : FpSz sz) (d n m : Nat) (fl : Clif.MemFlags) (A : Reg → Reg → AMode)
    (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hA : ∀ a b : Nat, a < 29 → b < 29 → MemMode sz.bytes (A (.x a) (.x b)))
    (hg : ∀ (a b : Nat) s, (A (.x a) (.x b)).addr ctx sz.bytes s =
      g (Arm.r (.GPR (rnum a)) s) (Arm.r (.GPR (rnum b)) s)) :
    Corr F ctx env #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .fpuLoad sz (r.getD 0 .xzr) (A (r.getD 1 .xzr) (r.getD 2 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩
  have hcanon : canonRegs #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩] = #[.v 0, .x 1, .x 2] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] #[.v n0, .x n1, .x n2] s) w =
      Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := fpuLoad_core ctx env sz hsz fl hn0 (m := A (.x n1) (.x n2)) (mC := A (.x 1) (.x 2))
    (hA _ _ hn1.1 hn2.1) (hA 1 2 (by decide) (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked]) hw))
    (by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
        exact sw_r_eq hw (by simp [Masked]))
    (fun x hx => by rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]; exact (hw.2.1 x hx).symm)
    hacc hex (by rw [hg, hg]; simp [rnum])
  fload_fin

theorem corr_fpuStore0g (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize)
    (hsz : FpSz sz) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (hmm : MemMode sz.bytes am)
    (hA : ∀ (s w : Arm.ArmState) (v : CV), SameWorld F s w →
      am.addr ctx sz.bytes (Arm.w (.SFP 0#5) v w) = am.addr ctx sz.bytes s) :
    Corr F ctx env #[⟨d, .float, .use, .early, .reg⟩] (fun r => .fpuStore sz (r.getD 0 .xzr) am fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, rfl⟩ := regs1 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨n0, rfl, hn0⟩
  have hcanon : canonRegs #[⟨d, .float, .use, .early, .reg⟩] = #[.v 0] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .use, .early, .reg⟩] (canonRegs #[⟨d, .float, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .use, .early, .reg⟩] #[.v n0] s) w =
      Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w := by
    simp [placeUses, useVals, hcanon, Operand.isUse, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hsp : Arm.r (.GPR 31#5) (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w) = Arm.r (.GPR 31#5) s := by
    rw [Arm.r_of_w_different (by simp)]; exact sw_r_eq hw (by simp [Masked])
  have hcore := fpuStore_core ctx env sz hsz fl hn0 (m := am) (mC := am)
    hmm hmm hal (SameWorld.w_right (by simp [Masked]) hw) hsp
    (by simp [rnum]) hacc hex (hA s w _ hw)
  fstore_fin

theorem corr_fpuStore1 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize)
    (hsz : FpSz sz) (d n : Nat) (fl : Clif.MemFlags) (A : Reg → AMode) (g : BitVec 64 → BitVec 64)
    (hA : ∀ a : Nat, a < 29 → MemMode sz.bytes (A (.x a)))
    (hg : ∀ (a : Nat) s, (A (.x a)).addr ctx sz.bytes s = g (Arm.r (.GPR (rnum a)) s)) :
    Corr F ctx env #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .fpuStore sz (r.getD 0 .xzr) (A (r.getD 1 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have hcanon : canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] =
      #[.v 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.v n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := fpuStore_core ctx env sz hsz fl hn0 (m := A (.x n1)) (mC := A (.x 1))
    (hA _ hn1.1) (hA 1 (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked]) hw))
    (by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
        exact sw_r_eq hw (by simp [Masked]))
    (by rw [Arm.r_of_w_different (by simp)]; simp [rnum]) hacc hex (by rw [hg, hg]; simp [rnum])
  fstore_fin

theorem corr_fpuStore2 (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (sz : ScalarSize)
    (hsz : FpSz sz) (d n m : Nat) (fl : Clif.MemFlags) (A : Reg → Reg → AMode)
    (g : BitVec 64 → BitVec 64 → BitVec 64)
    (hA : ∀ a b : Nat, a < 29 → b < 29 → MemMode sz.bytes (A (.x a) (.x b)))
    (hg : ∀ (a b : Nat) s, (A (.x a) (.x b)).addr ctx sz.bytes s =
      g (Arm.r (.GPR (rnum a)) s) (Arm.r (.GPR (rnum b)) s)) :
    Corr F ctx env #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .fpuStore sz (r.getD 0 .xzr) (A (r.getD 1 .xzr) (r.getD 2 .xzr)) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz' := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz'
  have hf := ha.fits
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz'
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩
  have hcanon : canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩] = #[.v 0, .x 1, .x 2] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  have ht : placeUses #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .float, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] #[.v n0, .x n1, .x n2] s) w =
      Arm.w (.GPR 2#5) (Arm.r (.GPR (rnum n2)) s) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s)
        (Arm.w (.SFP 0#5) (Arm.r (.SFP (rnum n0)) s) w)) := by
    simp [placeUses, useVals, hcanon, Operand.isUse, lo64, regVal, rnum]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hcore := fpuStore_core ctx env sz hsz fl hn0 (m := A (.x n1) (.x n2)) (mC := A (.x 1) (.x 2))
    (hA _ _ hn1.1 hn2.1) (hA 1 2 (by decide) (by decide)) hal
    (SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked])
      (SameWorld.w_right (by simp [Masked]) hw)))
    (by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp),
          Arm.r_of_w_different (by simp)]
        exact sw_r_eq hw (by simp [Masked]))
    (by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]; simp [rnum])
    hacc hex (by rw [hg, hg]; simp [rnum])
  fstore_fin


/-! ## `OperandsSound` per addressing mode -/

section
variable (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem)

theorem os_fpuLoad_slot (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.slotOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad0g F ctx env sz hsz d (.slotOffset off) fl trivial fun s w hw => by
      simp only [AMode.addr, spOf]; rw [sw_r_eq hw (by simp [Masked])])

theorem os_fpuLoad_sp (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.spOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad0g F ctx env sz hsz d (.spOffset off) fl trivial fun s w hw => by
      simp only [AMode.addr, spOf]; rw [sw_r_eq hw (by simp [Masked])])

theorem os_fpuLoad_fp (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.fpOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad0g F ctx env sz hsz d (.fpOffset off) fl trivial fun s w hw => by
      simp only [AMode.addr, regX]; rw [sw_r_eq hw (by simp [Masked, rnum])])

theorem os_fpuLoad_unscaled (sz : ScalarSize) (hsz : FpSz sz) (d n : Nat) (off : Int)
    (h1 : -256 ≤ off) (h2 : off < 256) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.unscaled (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad1 F ctx env sz hsz d n fl (fun r => .unscaled r off)
      (fun a => a + BitVec.ofInt 64 off) (mm_unscaled h1 h2) (fun _ _ => rfl))

theorem os_fpuLoad_uoff (sz : ScalarSize) (hsz : FpSz sz) (d n off : Nat)
    (h1 : off % sz.bytes = 0) (h2 : off / sz.bytes < 4096) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.unsignedOffset (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad1 F ctx env sz hsz d n fl (fun r => .unsignedOffset r off)
      (fun a => a + BitVec.ofNat 64 off) (mm_uoff h1 h2) (fun _ _ => rfl))

theorem os_fpuLoad_regReg (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.regReg (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad2 F ctx env sz hsz d n m fl .regReg (fun a b => a + b) mm_regReg (fun _ _ _ => rfl))

theorem os_fpuLoad_regScaled (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.regScaled (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad2 F ctx env sz hsz d n m fl .regScaled (fun a b => a + b <<< log2 sz.bytes)
      mm_regScaled (fun _ _ _ => rfl))

theorem os_fpuLoad_regScaledExtended (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.regScaledExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad2 F ctx env sz hsz d n m fl (fun a b => .regScaledExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) (log2 sz.bytes))
      (mm_regScaledExtended he) (fun _ _ _ => rfl))

theorem os_fpuLoad_regExtended (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad sz (.vreg d .float) (.regExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuLoad2 F ctx env sz hsz d n m fl (fun a b => .regExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) 0)
      (mm_regExtended he) (fun _ _ _ => rfl))

theorem os_fpuStore_slot (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.slotOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore0g F ctx env sz hsz d (.slotOffset off) fl trivial fun s w v hw => by
      simp only [AMode.addr, spOf]
      rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked])])

theorem os_fpuStore_sp (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.spOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore0g F ctx env sz hsz d (.spOffset off) fl trivial fun s w v hw => by
      simp only [AMode.addr, spOf]
      rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked])])

theorem os_fpuStore_fp (sz : ScalarSize) (hsz : FpSz sz) (d : Nat) (off : Int) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.fpOffset off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore0g F ctx env sz hsz d (.fpOffset off) fl trivial fun s w v hw => by
      simp only [AMode.addr, regX]
      rw [Arm.r_of_w_different (by simp), sw_r_eq hw (by simp [Masked, rnum])])

theorem os_fpuStore_unscaled (sz : ScalarSize) (hsz : FpSz sz) (d n : Nat) (off : Int)
    (h1 : -256 ≤ off) (h2 : off < 256) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.unscaled (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore1 F ctx env sz hsz d n fl (fun r => .unscaled r off)
      (fun a => a + BitVec.ofInt 64 off) (mm_unscaled h1 h2) (fun _ _ => rfl))

theorem os_fpuStore_uoff (sz : ScalarSize) (hsz : FpSz sz) (d n off : Nat)
    (h1 : off % sz.bytes = 0) (h2 : off / sz.bytes < 4096) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.unsignedOffset (.vreg n .int) off) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore1 F ctx env sz hsz d n fl (fun r => .unsignedOffset r off)
      (fun a => a + BitVec.ofNat 64 off) (mm_uoff h1 h2) (fun _ _ => rfl))

theorem os_fpuStore_regReg (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.regReg (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore2 F ctx env sz hsz d n m fl .regReg (fun a b => a + b) mm_regReg (fun _ _ _ => rfl))

theorem os_fpuStore_regScaled (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.regScaled (.vreg n .int) (.vreg m .int)) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore2 F ctx env sz hsz d n m fl .regScaled (fun a b => a + b <<< log2 sz.bytes)
      mm_regScaled (fun _ _ _ => rfl))

theorem os_fpuStore_regScaledExtended (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.regScaledExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore2 F ctx env sz hsz d n m fl (fun a b => .regScaledExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) (log2 sz.bytes))
      (mm_regScaledExtended he) (fun _ _ _ => rfl))

theorem os_fpuStore_regExtended (sz : ScalarSize) (hsz : FpSz sz) (d n m : Nat)
    (e : ExtendOp) (he : extOk e) (fl : Clif.MemFlags) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore sz (.vreg d .float) (.regExtended (.vreg n .int) (.vreg m .int) e) fl) :=
  os_of_corr rfl _ (by assign_tac) (by rcases hsz with rfl | rfl <;> fo_tac) rfl rfl
    (corr_fpuStore2 F ctx env sz hsz d n m fl (fun a b => .regExtended a b e)
      (fun a b => a + Arm.extend_reg b (Arm.decode_reg_extend e.bits) 0)
      (mm_regExtended he) (fun _ _ _ => rfl))

end

end Backend.Proof

import FV.Backend.Proof.RegallocLayout

/-!
# Executing slot stores and loads (M6 proof)

`slotStore`/`slotLoad` at `sp + off` for every offset of a frame below 32 KiB: the unscaled
encoding (`stur`/`ldur`, `off ≤ 255`) and the unsigned-offset encoding (`str`/`ldr`,
`256 ≤ off`), for 8-byte int and 16-byte float slots.
-/

namespace Backend.Proof
open Backend

theorem spAligned {s : Arm.ArmState} (h : Arm.CheckSPAlignment s) :
    Arm.Aligned (Arm.r (.GPR 31#5) s) 4 := by
  simpa only [Arm.CheckSPAlignment, Arm.read_gpr, BitVec.setWidth_eq] using h

theorem signExtend_small {off : Nat} (h : off < 256) :
    BitVec.signExtend 64 (BitVec.ofNat 9 off) = BitVec.ofNat 64 off := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq; simp; omega
  · simp [BitVec.msb_eq_decide]; omega

theorem ldst_offset16 (off : Nat) (h : off % 16 = 0) (h' : off / 16 < 4096) :
    BitVec.setWidth 64 (BitVec.ofNat 12 (off / 16)) <<< 4 = BitVec.ofNat 64 off := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt h']
  omega

/-- The machine state after storing `n` bytes `v` at `sp + off`. -/
def stSt (s : Arm.ArmState) (off n : Nat) (v : BitVec (n * 8)) : Arm.ArmState :=
  Arm.w .PC (Arm.r .PC s + 4#64) (Arm.write_mem_bytes n (spOf s + BitVec.ofNat 64 off) v s)

/-- The machine state after loading 8 bytes at `sp + off` into `x n`. -/
def ldIntSt (s : Arm.ArmState) (off n : Nat) : Arm.ArmState :=
  Arm.w (.GPR (rnum n)) (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) s)
    (Arm.w .PC (Arm.r .PC s + 4#64) s)

theorem exec_store_int (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 29) (h8 : off % 8 = 0)
    (hoff : off < 32768) {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    execMInst ctx env (slotStore .int (.x n) off) s = some (stSt s off 8 (Arm.r (.GPR (rnum n)) s)) := by
  have halign' := spAligned halign
  by_cases h255 : off ≤ 255
  · have hl : MInst.lines ctx (slotStore .int (.x n) off) {} =
        .ok ([.ins (.store .store64 (.x n) (.unscaled .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotStore, memFinalize, simm9?, show (off : Int) ≤ 255 by omega]; rfl
    have ha' : Insn.toArmInst env (.store .store64 (.x n) (.unscaled .sp off)) =
        .ok (.LDST (.Reg_unscaled_imm { size := 3#2, VR := 0#1, opc := 0#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
        Reg.encZR, Reg.encSP, show n ≤ 30 by omega, rnum, sField, show (off : Int) < 256 by omega]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unscaled_imm { size := 3#2, VR := 0#1, opc := 0#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) s =
        stSt s off 8 (Arm.r (.GPR (rnum n)) s) := by
      simp [stSt, Arm.exec_inst, Arm.LDST.exec_reg_unscaled_imm, Arm.LDST.exec_reg_unscaled_imm_gpr,
        Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
        signExtend_small (show off < 256 by omega),
        Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
        rnum_ne31 hn, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, halign', spOf]
      rfl
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, stSt, Arm.r_of_w_same]), he]
  · have hl : MInst.lines ctx (slotStore .int (.x n) off) {} =
        .ok ([.ins (.store .store64 (.x n) (.unsignedOffset .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotStore, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
        h8, StoreOp.bytes, show (off : Int) ≤ 32760 by omega]
      rfl
    have ha' : Insn.toArmInst env (.store .store64 (.x n) (.unsignedOffset .sp off)) =
        .ok (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 0#2, imm12 := BitVec.ofNat 12 (off / 8), Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
        Reg.encZR, Reg.encSP, show n ≤ 30 by omega, rnum, uField, h8, show off / 8 < 4096 by omega,
        StoreOp.bytes]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 0#2, imm12 := BitVec.ofNat 12 (off / 8), Rn := 31#5, Rt := rnum n })) s =
        stSt s off 8 (Arm.r (.GPR (rnum n)) s) := by
      rw [stSt, ← ldst_offset off h8 (by omega)]
      simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
        Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
        Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
        rnum_ne31 hn, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, halign', spOf]
      rfl
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, stSt, Arm.r_of_w_same]), he]

theorem exec_load_int (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 29) (h8 : off % 8 = 0)
    (hoff : off < 32768) {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    execMInst ctx env (slotLoad .int (.x n) off) s = some (ldIntSt s off n) := by
  have halign' := spAligned halign
  by_cases h255 : off ≤ 255
  · have hl : MInst.lines ctx (slotLoad .int (.x n) off) {} =
        .ok ([.ins (.load .uload64 (.x n) (.unscaled .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotLoad, memFinalize, simm9?, show (off : Int) ≤ 255 by omega]; rfl
    have ha' : Insn.toArmInst env (.load .uload64 (.x n) (.unscaled .sp off)) =
        .ok (.LDST (.Reg_unscaled_imm { size := 3#2, VR := 0#1, opc := 1#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
        Reg.encZR, Reg.encSP, show n ≤ 30 by omega, rnum, sField, show (off : Int) < 256 by omega]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unscaled_imm { size := 3#2, VR := 0#1, opc := 1#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) s =
        ldIntSt s off n := by
      rw [ldIntSt, Arm.w_of_w_commute (by simp)]
      simp [Arm.exec_inst, Arm.LDST.exec_reg_unscaled_imm, Arm.LDST.exec_reg_unscaled_imm_gpr,
        Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
        signExtend_small (show off < 256 by omega),
        Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr,
        rnum_ne31 hn, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, halign', spOf]
      rfl
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, ldIntSt, Arm.r_of_w_different (by simp), Arm.r_of_w_same]), he]
  · have hl : MInst.lines ctx (slotLoad .int (.x n) off) {} =
        .ok ([.ins (.load .uload64 (.x n) (.unsignedOffset .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotLoad, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
        h8, LoadOp.bytes, show (off : Int) ≤ 32760 by omega]
      rfl
    have ha' : Insn.toArmInst env (.load .uload64 (.x n) (.unsignedOffset .sp off)) =
        .ok (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 1#2, imm12 := BitVec.ofNat 12 (off / 8), Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
        Reg.encZR, Reg.encSP, show n ≤ 30 by omega, rnum, uField, h8, show off / 8 < 4096 by omega,
        LoadOp.bytes]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 3#2, V := 0#1, opc := 1#2, imm12 := BitVec.ofNat 12 (off / 8), Rn := 31#5, Rt := rnum n })) s =
        ldIntSt s off n := by
      rw [ldIntSt, ← ldst_offset off h8 (by omega), Arm.w_of_w_commute (by simp)]
      simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
        Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
        Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr,
        rnum_ne31 hn, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, halign', spOf]
      rfl
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, ldIntSt, Arm.r_of_w_different (by simp), Arm.r_of_w_same]), he]


theorem wsfp_cast {k : Nat} (h : 8 <<< k = 8 <<< k / 8 * 8) (hk : k = 4) (a : BitVec 64) (r : BitVec 5)
    (s : Arm.ArmState) :
    Arm.write_mem_bytes (8 <<< k / 8) a (BitVec.cast h (Arm.read_sfp (8 <<< k) r s)) s =
      Arm.write_mem_bytes 16 a (Arm.read_sfp 128 r s) s := by
  subst hk; rfl

theorem rsfp_cast {k : Nat} (h : 8 <<< k / 8 * 8 = 8 <<< k) (hk : k = 4) (a : BitVec 64) (r : BitVec 5)
    (s : Arm.ArmState) :
    Arm.write_sfp (8 <<< k) r (BitVec.cast h (Arm.read_mem_bytes (8 <<< k / 8) a s)) s =
      Arm.write_sfp 128 r (Arm.read_mem_bytes 16 a s) s := by
  subst hk; rfl

/-- The machine state after loading 16 bytes at `sp + off` into `v n`. -/
def ldFSt (s : Arm.ArmState) (off n : Nat) : Arm.ArmState :=
  Arm.w (.SFP (rnum n)) (Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 off) s)
    (Arm.w .PC (Arm.r .PC s + 4#64) s)

theorem exec_store_float (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 32) (h8 : off % 16 = 0)
    (hoff : off < 32768) {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    execMInst ctx env (slotStore .float (.v n) off) s = some (stSt s off 16 (Arm.r (.SFP (rnum n)) s)) := by
  have halign' := spAligned halign
  by_cases h255 : off ≤ 255
  · have hl : MInst.lines ctx (slotStore .float (.v n) off) {} =
        .ok ([.ins (.store .fpuStore128 (.v n) (.unscaled .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotStore, memFinalize, simm9?, show (off : Int) ≤ 255 by omega]; rfl
    have ha' : Insn.toArmInst env (.store .fpuStore128 (.v n) (.unscaled .sp off)) =
        .ok (.LDST (.Reg_unscaled_imm { size := 0#2, VR := 1#1, opc := 2#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
        Reg.encV, Reg.encSP, show n ≤ 31 by omega, rnum, sField, show (off : Int) < 256 by omega]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unscaled_imm { size := 0#2, VR := 1#1, opc := 2#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) s =
        stSt s off 16 (Arm.r (.SFP (rnum n)) s) := by
      simp only [Arm.exec_inst]
      simp only [Arm.LDST.exec_reg_unscaled_imm, Arm.LDST.exec_ldstur]
      have hsc : (BitVec.extractLsb' 1 1 2#2 ++ 0#2).toNat = 4 := by decide
      have hg : (2#2).getLsbD 0 = false := by decide
      simp only [hsc, hg, ite_true, Bool.false_eq_true, ite_false, halign, not_true, and_false,
        show ¬ (4 > 4) by decide, signExtend_small (show off < 256 by omega)]
      rw [wsfp_cast _ hsc]
      simp [stSt, Arm.read_sfp, Arm.read_gpr, Arm.read_pc, Arm.write_pc, spOf, Arm.r_of_write_mem_bytes]
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, stSt, Arm.r_of_w_same]), he]
  · have hl : MInst.lines ctx (slotStore .float (.v n) off) {} =
        .ok ([.ins (.store .fpuStore128 (.v n) (.unsignedOffset .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotStore, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
        h8, StoreOp.bytes, show (off : Int) ≤ 65520 by omega]
      rfl
    have ha' : Insn.toArmInst env (.store .fpuStore128 (.v n) (.unsignedOffset .sp off)) =
        .ok (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 2#2, imm12 := BitVec.ofNat 12 (off / 16), Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
        Reg.encV, Reg.encSP, show n ≤ 31 by omega, rnum, uField, h8, show off / 16 < 4096 by omega,
        StoreOp.bytes]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 2#2, imm12 := BitVec.ofNat 12 (off / 16), Rn := 31#5, Rt := rnum n })) s =
        stSt s off 16 (Arm.r (.SFP (rnum n)) s) := by
      rw [stSt, spOf, ← ldst_offset16 off h8 (by omega)]
      simp only [Arm.exec_inst]
      have hsc : (Arm.BitVec.lsb (2#2) 1 ++ 0#2).toNat = 4 := by decide
      simp only [Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common, hsc,
        decide_true, ite_true, show Arm.LDST.supported_simd_reg_imm 0#2 2#2 = true by decide,
        show Arm.BitVec.lsb (2#2) 1 = 1#1 by decide, show Arm.BitVec.lsb (2#2) 0 = 0#1 by decide,
        show Arm.LDST.reg_imm_constrain_unpredictable false true (31#5) (rnum n) = false by
          simp [Arm.LDST.reg_imm_constrain_unpredictable]]
      simp [Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value, halign, Arm.ldst_read,
        Arm.read_gpr, Arm.read_pc, Arm.write_pc, spOf]
      rfl
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, stSt, Arm.r_of_w_same]), he]

theorem exec_load_float (ctx : FnCtx) (env : Env) {n off : Nat} (hn : n < 32) (h8 : off % 16 = 0)
    (hoff : off < 32768) {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    execMInst ctx env (slotLoad .float (.v n) off) s = some (ldFSt s off n) := by
  have halign' := spAligned halign
  by_cases h255 : off ≤ 255
  · have hl : MInst.lines ctx (slotLoad .float (.v n) off) {} =
        .ok ([.ins (.load .fpuLoad128 (.v n) (.unscaled .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotLoad, memFinalize, simm9?, show (off : Int) ≤ 255 by omega]; rfl
    have ha' : Insn.toArmInst env (.load .fpuLoad128 (.v n) (.unscaled .sp off)) =
        .ok (.LDST (.Reg_unscaled_imm { size := 0#2, VR := 1#1, opc := 3#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
        Reg.encV, Reg.encSP, show n ≤ 31 by omega, rnum, sField, show (off : Int) < 256 by omega]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unscaled_imm { size := 0#2, VR := 1#1, opc := 3#2, imm9 := BitVec.ofNat 9 off, Rn := 31#5, Rt := rnum n })) s =
        ldFSt s off n := by
      simp only [Arm.exec_inst]
      simp only [Arm.LDST.exec_reg_unscaled_imm, Arm.LDST.exec_ldstur]
      have hsc : (BitVec.extractLsb' 1 1 3#2 ++ 0#2).toNat = 4 := by decide
      have hg : (3#2).getLsbD 0 = true := by decide
      simp only [hsc, hg, ite_true, Bool.false_eq_true, ite_false, halign, not_true, and_false,
        show ¬ (4 > 4) by decide, signExtend_small (show off < 256 by omega), reduceCtorEq]
      rw [rsfp_cast _ hsc, ldFSt, Arm.w_of_w_commute (by simp)]
      simp only [Arm.write_sfp, Arm.read_gpr, Arm.read_pc, Arm.write_pc, spOf, BitVec.setWidth_eq]
      rw [Arm.r_of_w_different (by simp)]
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, ldFSt, Arm.r_of_w_different (by simp), Arm.r_of_w_same]), he]
  · have hl : MInst.lines ctx (slotLoad .float (.v n) off) {} =
        .ok ([.ins (.load .fpuLoad128 (.v n) (.unsignedOffset .sp off)) trustedFlags.trapCode], {}) := by
      simp [MInst.lines, slotLoad, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
        h8, LoadOp.bytes, show (off : Int) ≤ 65520 by omega]
      rfl
    have ha' : Insn.toArmInst env (.load .fpuLoad128 (.v n) (.unsignedOffset .sp off)) =
        .ok (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 3#2, imm12 := BitVec.ofNat 12 (off / 16), Rn := 31#5, Rt := rnum n })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
        Reg.encV, Reg.encSP, show n ≤ 31 by omega, rnum, uField, h8, show off / 16 < 4096 by omega,
        LoadOp.bytes]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 3#2, imm12 := BitVec.ofNat 12 (off / 16), Rn := 31#5, Rt := rnum n })) s =
        ldFSt s off n := by
      rw [ldFSt, spOf, ← ldst_offset16 off h8 (by omega), Arm.w_of_w_commute (by simp)]
      simp only [Arm.exec_inst]
      have hsc : (Arm.BitVec.lsb (3#2) 1 ++ 0#2).toNat = 4 := by decide
      simp only [Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common, hsc,
        decide_true, ite_true, show Arm.LDST.supported_simd_reg_imm 0#2 3#2 = true by decide,
        show Arm.BitVec.lsb (3#2) 1 = 1#1 by decide, show Arm.BitVec.lsb (3#2) 0 = 1#1 by decide,
        show Arm.LDST.reg_imm_constrain_unpredictable false true (31#5) (rnum n) = false by
          simp [Arm.LDST.reg_imm_constrain_unpredictable]]
      simp [Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value, halign, Arm.ldst_write,
        Arm.write_sfp, Arm.read_gpr, Arm.read_pc, Arm.write_pc, spOf]
    simp only [execMInst, hl]
    rw [execLines_one ha' (by rw [he, ldFSt, Arm.r_of_w_different (by simp), Arm.r_of_w_same]), he]


/-! ## Effects on the location store -/

theorem stSt_mem_pc_sp {s : Arm.ArmState} {o n : Nat} {v : BitVec (n * 8)} :
    spOf (stSt s o n v) = spOf s := spOf_write _ _ _ _ _

/-- A slot store keeps the world and `sp`, and every other live location. -/
theorem store_effect {fr : RAFrame} {D : Loc → Prop} {T : Prop} {sp0 : BitVec 64}
    {F : BitVec 64 → Prop} (hfr : FrameOk fr D T sp0 F) {s w : Arm.ArmState} (hw : SameWorld F s w)
    (hsp : spOf s = sp0) {dst : Loc} {o n : Nat} (hD : D dst) (hoff : fr.offset dst = .ok o)
    (hn : slotBytes dst = n) (v : BitVec (n * 8)) :
    SameWorld F (stSt s o n v) w ∧ spOf (stSt s o n v) = sp0 ∧
      ∀ l, D l → l ≠ dst → locVal fr (stSt s o n v) l = locVal fr s l := by
  subst hn
  refine ⟨SameWorld.w_left (by simp [Masked]) (SameWorld.write_mem_bytes_inF hw _ _ _
      (fun j hj => by rw [hsp]; exact hfr.inF _ o hD hoff j hj)), by rw [stSt, spOf_write, hsp], ?_⟩
  intro l hDl e
  cases l with
  | reg r =>
    simp only [locVal, stSt]
    rw [regVal_w (by cases r <;> simp [Reg.field]), regVal_write_mem_bytes]
  | stack k c =>
    exact locVal_frame_write (fun r h => Loc.noConfusion h) (fun o' ho => by
      rw [hsp]; exact hfr.sep _ _ o' o hDl hD e ho hoff)
  | save r =>
    exact locVal_frame_write (fun r h => Loc.noConfusion h) (fun o' ho => by
      rw [hsp]; exact hfr.sep _ _ o' o hDl hD e ho hoff)

theorem locVal_frame_eq {fr : RAFrame} {s : Arm.ArmState} {l : Loc} {o : Nat}
    (hoff : fr.offset l = .ok o) :
    locVal fr s l = if slotBytes l = 8 then ofX (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 o) s)
      else Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 o) s := by
  cases l with
  | reg r => simp [RAFrame.offset] at hoff
  | stack k c => simp only [locVal, hoff]
  | save r => simp only [locVal, hoff]

/-- The stored slot holds the stored value (8-byte slots: zero-extended). -/
theorem store_dst8 {fr : RAFrame} {s : Arm.ArmState} {dst : Loc} {o : Nat}
    (hoff : fr.offset dst = .ok o) (h8 : slotBytes dst = 8) (v : BitVec 64) :
    locVal fr (stSt s o 8 v) dst = ofX v := by
  rw [locVal_frame_eq hoff, if_pos h8, stSt, spOf_write, Arm.read_mem_bytes_of_w,
    Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)]

theorem store_dst16 {fr : RAFrame} {s : Arm.ArmState} {dst : Loc} {o : Nat}
    (hoff : fr.offset dst = .ok o) (h16 : slotBytes dst = 16) (v : BitVec 128) :
    locVal fr (stSt s o 16 v) dst = v := by
  rw [locVal_frame_eq hoff, if_neg (by omega), stSt, spOf_write, Arm.read_mem_bytes_of_w,
    Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)]

/-- An int reload keeps the world, `sp` and every location but its destination register,
which gets the slot's value. -/
theorem loadInt_effect {fr : RAFrame} {F : BitVec 64 → Prop} {s w : Arm.ArmState}
    (hw : SameWorld F s w) {n : Nat} (hn : (Reg.x n).allocatable = true) {src : Loc} {o : Nat}
    (hoff : fr.offset src = .ok o) (h8 : slotBytes src = 8) :
    SameWorld F (ldIntSt s o n) w ∧ spOf (ldIntSt s o n) = spOf s ∧
      ∀ l, ValidLoc l → locVal fr (ldIntSt s o n) l =
        upd (locVal fr s) (.reg (.x n)) (locVal fr s src) l := by
  rcases allocatable_cases hn with ⟨n', en, hhn⟩ | ⟨_, en, _⟩ <;> cases en
  obtain ⟨hW, hDv, hO⟩ := gpr_write_sound hhn hw
    (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 o) s) (Arm.r .PC s + 4#64)
  have hsp : spOf (ldIntSt s o n) = spOf s := by
    simp only [spOf, ldIntSt]
    rw [Arm.r_of_w_different (by simpa using (rnum_ne31 hhn.1).symm),
      Arm.r_of_w_different (by simp)]
  have hm : (ldIntSt s o n).mem = s.mem := by
    simp only [ldIntSt]; rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]
  refine ⟨hW, hsp, fun l hl => ?_⟩
  by_cases e : l = .reg (.x n)
  · subst e
    simp only [upd, if_true]
    rw [locVal_frame_eq hoff, if_pos h8]
    exact hDv
  · simp only [upd, e, if_false]
    cases l with
    | reg r => exact hO r (hl r rfl) (fun h => e (by rw [h]))
    | stack k c => exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm
    | save r => exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm

/-- A float reload, likewise. -/
theorem loadFloat_effect {fr : RAFrame} {F : BitVec 64 → Prop} {s w : Arm.ArmState}
    (hw : SameWorld F s w) {n : Nat} (hn : n < 32) {src : Loc} {o : Nat}
    (hoff : fr.offset src = .ok o) (h16 : slotBytes src = 16) :
    SameWorld F (ldFSt s o n) w ∧ spOf (ldFSt s o n) = spOf s ∧
      ∀ l, ValidLoc l → locVal fr (ldFSt s o n) l =
        upd (locVal fr s) (.reg (.v n)) (locVal fr s src) l := by
  have hsp : spOf (ldFSt s o n) = spOf s := by
    simp only [spOf, ldFSt]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
  have hm : (ldFSt s o n).mem = s.mem := by
    simp only [ldFSt]; rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]
  refine ⟨SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) hw), hsp,
    fun l hl => ?_⟩
  by_cases e : l = .reg (.v n)
  · subst e
    simp only [upd, if_true]
    rw [locVal_frame_eq hoff, if_neg (by omega)]
    simp only [locVal, ldFSt, regVal, Arm.r_of_w_same]
  · simp only [upd, e, if_false]
    cases l with
    | reg r =>
      simp only [locVal, ldFSt]
      rw [regVal_w, regVal_w (by cases r <;> simp [Reg.field])]
      rcases allocatable_cases (hl r rfl) with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
      · simp [Reg.field]
      · simp only [Reg.field, ne_eq, Option.some.injEq, Arm.StateField.SFP.injEq]
        exact rnum_ne hk hn (fun h => e (by rw [h]))
    | stack k c => exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm
    | save r => exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm

end Backend.Proof

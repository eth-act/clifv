import FV.Concurrency.ArmAllocMem
import FV.Concurrency.VCodeAddr
import FV.Backend.Proof.RegallocMem
import FV.Backend.Proof.RegallocMemFP

/-!
# Layer 4b for the plain load/store items of the atomics scope (T2h, #311)

The facts about the **plain load/store** instructions (GPR `load`/`store`, SIMD&FP
`fpuLoad`/`fpuStore` of 32/64 bits) that the per-item obligation `ArmAllocThread.ItemSim` at their
items needs (the scope itself: `ArmAllocLS`):

* `ctlIndep_*`: the pc, error and program after each encoded plain load/store do not depend on
  the memory (`CtlIndep`), alignment faults included;
* `preMem`, `straightSem_pre`: an event-free prefix of lines (`memFinalize`'s `loadConst64`)
  commutes with `setMem`, and the source step of a form with such a prefix is the if-expression on
  the access's execution (**receptiveness**);
* `immEvs_load_eq`, `immEvs_store_eq`: two GPR accesses of the same shape have the same events
  when their base and offset values (and, for a store, the data) agree.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
open Code VCodeEvents VCodeAddr

/-! ## The pc, error and program after a plain load/store -/

theorem sameCtl_pcp {p q : BitVec 64} {X Y : ArmState} (hp : p = q) (h : SameCtl X Y) :
    SameCtl (Arm.w .PC p X) (Arm.w .PC q Y) := by
  refine ⟨?_, ?_, ?_⟩
  · show Arm.r .PC (Arm.w .PC p X) = Arm.r .PC (Arm.w .PC q Y)
    rw [hp]
    simp
  · rw [Arm.r_of_w_different (show Arm.StateField.ERR ≠ Arm.StateField.PC by simp),
      Arm.r_of_w_different (show Arm.StateField.ERR ≠ Arm.StateField.PC by simp)]
    exact h.2.1
  · rw [Arm.w_program, Arm.w_program]
    exact h.2.2

theorem sameCtl_w_ne {f : Arm.StateField} (v : Arm.state_value f) (s : ArmState)
    (hpc : Arm.StateField.PC ≠ f) (herr : Arm.StateField.ERR ≠ f) :
    SameCtl (Arm.w f v s) s := by
  refine ⟨Arm.r_of_w_different hpc, Arm.r_of_w_different herr, ?_⟩
  exact w_program

theorem sameCtl_setMem_both {M M' : Memory} {X Y : ArmState} (h : SameCtl X Y) :
    SameCtl (setMem M X) (setMem M' Y) :=
  (sameCtl_setMem M X).trans (h.trans (sameCtl_setMem M' Y).symm)

theorem sameCtl_wSFP (n : Nat) (i : BitVec 5) (v : BitVec n) (y : ArmState) :
    SameCtl (write_sfp n i v y) y := by
  show SameCtl (Arm.w (Arm.StateField.SFP i) (BitVec.setWidth 128 v) y) y
  exact sameCtl_w_ne _ y (show Arm.StateField.PC ≠ Arm.StateField.SFP i by simp)
    (show Arm.StateField.ERR ≠ Arm.StateField.SFP i by simp)

theorem chk_setMem {Rn : BitVec 5} {y : ArmState} {M : Memory}
    (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y)) (h : Rn = 31#5) :
    CheckSPAlignment (setMem M y) := by
  rw [check_sp_sm']
  by_cases ha : CheckSPAlignment y
  · exact ha
  · exact absurd ⟨h, ha⟩ h31

theorem chk_y {Rn : BitVec 5} {y : ArmState} (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y))
    (h : Rn = 31#5) : CheckSPAlignment y := by
  by_cases ha : CheckSPAlignment y
  · exact ha
  · exact absurd ⟨h, ha⟩ h31

/-- **The pc, error and program after a plain GPR load do not depend on the memory** (the
access is not at an unaligned `sp`). -/
theorem pc_setMem_y (M : Memory) (y : ArmState) :
    read_pc (setMem M y) + 4#64 = read_pc y + 4#64 := by
  simp [read_pc, r_setMem]

theorem sameCtl_gpr_load {op : LoadOp} (hop : op ≠ .fpuLoad128) {Rn Rt : BitVec 5} (hRt : Rt ≠ 31#5)
    (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y)) :
    SameCtl (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str
      (setMem M y))
      (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str y) := by
  rw [ldst_load op hop Rn Rt hRt imm str (setMem M y)
      (fun h => chk_setMem h31 h),
    ldst_load op hop Rn Rt hRt imm str y
      (fun h => chk_y h31 h)]
  simp only [read_gpr_sm, offset_value_sm]
  refine sameCtl_pcp (show Arm.r .PC (setMem M y) + 4#64 = Arm.r .PC y + 4#64 from by
    simp [read_pc, r_setMem]) ?_
  exact (sameCtl_w_ne (ldX op (Arm.read_gpr 64 Rn y + imm.value (log2 op.bytes) y) (setMem M y))
    (setMem M y) (show Arm.StateField.PC ≠ Arm.StateField.GPR Rt by simp)
    (show Arm.StateField.ERR ≠ Arm.StateField.GPR Rt by simp)).trans
    ((sameCtl_setMem _ _).trans (sameCtl_w_ne (ldX op (Arm.read_gpr 64 Rn y + imm.value (log2 op.bytes) y) y) y
      (show Arm.StateField.PC ≠ Arm.StateField.GPR Rt by simp)
      (show Arm.StateField.ERR ≠ Arm.StateField.GPR Rt by simp)).symm)

/-- **... at an unaligned `sp`** (both steps write the alignment fault). -/
theorem sameCtl_gpr_load_err {op : LoadOp} (hop : op ≠ .fpuLoad128) {Rn Rt : BitVec 5}
    (hRt : Rt ≠ 31#5) (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y) :
    SameCtl (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str
      (setMem M y))
      (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str y) := by
  cases op <;> simp at hop <;>
  · simp (config := {decide := true}) [Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation,
      gprCls, LoadOp.fields, LoadOp.bytes, Arm.LDST.reg_imm_constrain_unpredictable, h31,
      check_sp_sm', read_gpr_sm, log2]
    first
      | (refine sameCtl_pcp (by simp [read_pc, r_setMem])
          (by simp only [write_err_sm, sameCtl_setMem]))
      | (rw [write_err_sm]; exact sameCtl_setMem _ _)

theorem sameCtl_gpr_store {op : StoreOp} (hop : op ≠ .fpuStore128) {Rn Rt : BitVec 5}
    (hRt : Rt ≠ 31#5) (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y)) :
    SameCtl (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str
      (setMem M y))
      (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str y) := by
  rw [ldst_store op hop Rn Rt hRt imm str (setMem M y)
      (fun h => chk_setMem h31 h),
    ldst_store op hop Rn Rt hRt imm str y
      (fun h => chk_y h31 h)]
  refine sameCtl_pcp (show Arm.r .PC (setMem M y) + 4#64 = Arm.r .PC y + 4#64 from by
    simp [read_pc, r_setMem]) ?_
  exact ((sameCtl_wmb _ _ _ _).trans (sameCtl_setMem _ _)).trans (sameCtl_wmb _ _ _ _).symm

theorem sameCtl_gpr_store_err {op : StoreOp} (hop : op ≠ .fpuStore128) {Rn Rt : BitVec 5}
    (hRt : Rt ≠ 31#5) (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y) :
    SameCtl (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str
      (setMem M y))
      (Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str y) := by
  cases op <;> simp at hop <;>
  · simp (config := {decide := true}) [Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation,
      gprCls, StoreOp.fields, StoreOp.bytes, Arm.LDST.reg_imm_constrain_unpredictable, h31,
      check_sp_sm', read_gpr_sm, log2]
    first
      | (refine sameCtl_pcp (by simp [read_pc, r_setMem])
          (by simp only [write_err_sm, sameCtl_setMem]))
      | (rw [write_err_sm]; exact sameCtl_setMem _ _)

theorem sameCtl_fp_load {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5}
    (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y)) :
    SameCtl (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn Rt imm) str (setMem M y))
      (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn Rt imm) str y) := by
  rw [ldst_fpuLoad sz hsz Rn Rt imm str (setMem M y)
      (fun h => chk_setMem h31 h),
    ldst_fpuLoad sz hsz Rn Rt imm str y
      (fun h => chk_y h31 h)]
  simp only [read_gpr_sm, offset_value_sm]
  refine sameCtl_pcp (show Arm.r .PC (setMem M y) + 4#64 = Arm.r .PC y + 4#64 from by
    simp [read_pc, r_setMem]) ?_
  exact (sameCtl_w_ne (ldV sz (Arm.read_gpr 64 Rn y + imm.value (log2 sz.bytes) y) (setMem M y))
    (setMem M y) (show Arm.StateField.PC ≠ Arm.StateField.SFP Rt by simp)
    (show Arm.StateField.ERR ≠ Arm.StateField.SFP Rt by simp)).trans
    ((sameCtl_setMem _ _).trans (sameCtl_w_ne (ldV sz (Arm.read_gpr 64 Rn y + imm.value (log2 sz.bytes) y) y) y
      (show Arm.StateField.PC ≠ Arm.StateField.SFP Rt by simp)
      (show Arm.StateField.ERR ≠ Arm.StateField.SFP Rt by simp)).symm)

theorem sameCtl_fp_load_err {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5}
    (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y) :
    SameCtl (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn Rt imm) str (setMem M y))
      (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 1 Rn Rt imm) str y) := by
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) [Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation,
      fpCls, fpSizeF, ScalarSize.bytes, Arm.LDST.supported_simd_reg_imm,
      Arm.LDST.reg_imm_constrain_unpredictable, h31, check_sp_sm', read_gpr_sm, log2]
    first
      | (refine sameCtl_pcp (by simp [read_pc, r_setMem])
          (by simp only [write_err_sm, sameCtl_setMem]))
      | (rw [write_err_sm]; exact sameCtl_setMem _ _)

theorem sameCtl_fp_store {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5}
    (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y)) :
    SameCtl (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn Rt imm) str (setMem M y))
      (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn Rt imm) str y) := by
  rw [ldst_fpuStore sz hsz Rn Rt imm str (setMem M y)
      (fun h => chk_setMem h31 h),
    ldst_fpuStore sz hsz Rn Rt imm str y
      (fun h => chk_y h31 h)]
  refine sameCtl_pcp (show Arm.r .PC (setMem M y) + 4#64 = Arm.r .PC y + 4#64 from by
    simp [read_pc, r_setMem]) ?_
  exact ((sameCtl_wmb _ _ _ _).trans (sameCtl_setMem _ _)).trans (sameCtl_wmb _ _ _ _).symm

theorem sameCtl_fp_store_err {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5}
    (imm : Arm.LDST.Reg_offset) (str : String) (M : Memory) (y : ArmState)
    (h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y) :
    SameCtl (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn Rt imm) str (setMem M y))
      (Arm.LDST.exec_reg_imm_common (fpCls (fpSizeF sz) 0 Rn Rt imm) str y) := by
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) [Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation,
      fpCls, fpSizeF, ScalarSize.bytes, Arm.LDST.supported_simd_reg_imm,
      Arm.LDST.reg_imm_constrain_unpredictable, h31, check_sp_sm', read_gpr_sm, log2]
    first
      | (refine sameCtl_pcp (by simp [read_pc, r_setMem])
          (by simp only [write_err_sm, sameCtl_setMem]))
      | (rw [write_err_sm]; exact sameCtl_setMem _ _)

theorem sameCtl_ldstur_load {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5} (imm9 : BitVec 9)
    (M : Memory) (y : ArmState) (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y)) :
    SameCtl ((Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := imm9, Rn := Rn, Rt := Rt }) (setMem M y))
      ((Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := imm9, Rn := Rn, Rt := Rt }) y) := by
  rw [ldstur_fpuLoad sz hsz Rn Rt imm9 (setMem M y)
      (fun h => chk_setMem h31 h),
    ldstur_fpuLoad sz hsz Rn Rt imm9 y
      (fun h => chk_y h31 h)]
  simp only [read_gpr_sm]
  refine sameCtl_pcp (show Arm.r .PC (setMem M y) + 4#64 = Arm.r .PC y + 4#64 from by
    simp [read_pc, r_setMem]) ?_
  exact (sameCtl_w_ne (ldV sz (Arm.read_gpr 64 Rn y + BitVec.signExtend 64 imm9) (setMem M y))
    (setMem M y) (show Arm.StateField.PC ≠ Arm.StateField.SFP Rt by simp)
    (show Arm.StateField.ERR ≠ Arm.StateField.SFP Rt by simp)).trans
    ((sameCtl_setMem _ _).trans (sameCtl_w_ne (ldV sz (Arm.read_gpr 64 Rn y + BitVec.signExtend 64 imm9) y) y
      (show Arm.StateField.PC ≠ Arm.StateField.SFP Rt by simp)
      (show Arm.StateField.ERR ≠ Arm.StateField.SFP Rt by simp)).symm)

theorem sameCtl_ldstur_load_err {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5}
    (imm9 : BitVec 9) (M : Memory) (y : ArmState) (h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y) :
    SameCtl ((Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := imm9, Rn := Rn, Rt := Rt }) (setMem M y))
      ((Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := imm9, Rn := Rn, Rt := Rt }) y) := by
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) [Arm.LDST.exec_ldstur, fpSizeF, ScalarSize.bytes, h31,
      check_sp_sm', read_gpr_sm]
    first
      | (refine sameCtl_pcp (by simp [read_pc, r_setMem])
          (by simp only [write_err_sm, sameCtl_setMem]))
      | (rw [write_err_sm]; exact sameCtl_setMem _ _)

theorem sameCtl_ldstur_store {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5} (imm9 : BitVec 9)
    (M : Memory) (y : ArmState) (h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment y)) :
    SameCtl (Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := imm9, Rn := Rn, Rt := Rt } (setMem M y))
      (Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := imm9, Rn := Rn, Rt := Rt } y) := by
  rw [ldstur_fpuStore sz hsz Rn Rt imm9 (setMem M y)
      (fun h => chk_setMem h31 h),
    ldstur_fpuStore sz hsz Rn Rt imm9 y
      (fun h => chk_y h31 h)]
  refine sameCtl_pcp (show Arm.r .PC (setMem M y) + 4#64 = Arm.r .PC y + 4#64 from by
    simp [read_pc, r_setMem]) ?_
  exact ((sameCtl_wmb _ _ _ _).trans (sameCtl_setMem _ _)).trans (sameCtl_wmb _ _ _ _).symm

theorem sameCtl_ldstur_store_err {sz : ScalarSize} (hsz : FpSz sz) {Rn Rt : BitVec 5}
    (imm9 : BitVec 9) (M : Memory) (y : ArmState) (h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y) :
    SameCtl (Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := imm9, Rn := Rn, Rt := Rt } (setMem M y))
      (Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := imm9, Rn := Rn, Rt := Rt } y) := by
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) [Arm.LDST.exec_ldstur, fpSizeF, ScalarSize.bytes, h31,
      check_sp_sm', read_gpr_sm]
    first
      | (refine sameCtl_pcp (by simp [read_pc, r_setMem])
          (by simp only [write_err_sm, sameCtl_setMem]))
      | (rw [write_err_sm]; exact sameCtl_setMem _ _)

/-- The reductions of the encoded plain load/store forms to `exec_reg_imm_common` (the
emitter's string is quantified). -/
theorem exec_uimm_ex {size opc : BitVec 2} {imm12 : BitVec 12} {Rn Rt : BitVec 5} :
    ∃ str, ∀ s : ArmState, Arm.exec_inst (uimmInst size opc imm12 Rn Rt) s =
      Arm.LDST.exec_reg_imm_common (gprCls size opc Rn Rt (LDST.Reg_offset.uimm12 imm12)) str s :=
  ⟨_, fun s => rfl⟩

theorem exec_unsc_ex {size opc : BitVec 2} {imm9 : BitVec 9} {Rn Rt : BitVec 5} :
    ∃ str, ∀ s : ArmState, Arm.exec_inst (unscInst size opc imm9 Rn Rt) s =
      Arm.LDST.exec_reg_imm_common (gprCls size opc Rn Rt (LDST.Reg_offset.simm9 imm9)) str s :=
  ⟨_, fun s => rfl⟩

theorem exec_regI_ex {size opc : BitVec 2} {Rm : BitVec 5} {option : BitVec 3} {S : BitVec 1}
    {Rn Rt : BitVec 5} (ho : Arm.BitVec.lsb option 1 = 1#1) :
    ∃ str, ∀ s : ArmState, Arm.exec_inst (regInst size opc Rm option S Rn Rt) s =
      Arm.LDST.exec_reg_imm_common (gprCls size opc Rn Rt (LDST.Reg_offset.reg Rm option S)) str s := by
  refine ⟨s!"{Arm.Reg_reg_offset_cls.mk size 0b111#3 0#1 0b00#2 opc 0b1#1 Rm option S 0b10#2 Rn Rt}",
    fun s => ?_⟩
  rw [show Arm.exec_inst (regInst size opc Rm option S Rn Rt) s =
      Arm.LDST.exec_reg_reg_offset
        { size := size, V := 0#1, opc := opc, Rm := Rm, option := option, S := S, Rn := Rn,
          Rt := Rt } s from rfl]
  simp only [Arm.LDST.exec_reg_reg_offset,
    if_neg (show ¬ (Arm.BitVec.lsb option 1 = 0#1) from by simp [ho])]
  rfl

theorem exec_fpUimm_ex {size opc : BitVec 2} {imm12 : BitVec 12} {Rn Rt : BitVec 5} :
    ∃ str, ∀ s : ArmState, Arm.exec_inst (fpUimmInst size opc imm12 Rn Rt) s =
      Arm.LDST.exec_reg_imm_common (fpCls size opc Rn Rt (LDST.Reg_offset.uimm12 imm12)) str s :=
  ⟨_, fun s => rfl⟩

theorem exec_fpReg_ex {size opc : BitVec 2} {Rm : BitVec 5} {option : BitVec 3} {S : BitVec 1}
    {Rn Rt : BitVec 5} (ho : Arm.BitVec.lsb option 1 = 1#1) :
    ∃ str, ∀ s : ArmState, Arm.exec_inst (fpRegInst size opc Rm option S Rn Rt) s =
      Arm.LDST.exec_reg_imm_common (fpCls size opc Rn Rt (LDST.Reg_offset.reg Rm option S)) str s := by
  refine ⟨s!"{Arm.Reg_reg_offset_cls.mk size 0b111#3 1#1 0b00#2 opc 0b1#1 Rm option S 0b10#2 Rn Rt}",
    fun s => ?_⟩
  rw [show Arm.exec_inst (fpRegInst size opc Rm option S Rn Rt) s =
      Arm.LDST.exec_reg_reg_offset
        { size := size, V := 1#1, opc := opc, Rm := Rm, option := option, S := S, Rn := Rn,
          Rt := Rt } s from rfl]
  simp only [Arm.LDST.exec_reg_reg_offset,
    if_neg (show ¬ (Arm.BitVec.lsb option 1 = 0#1) from by simp [ho])]
  rfl

theorem ctlIndep_uimm_load (op : LoadOp) (hop : op ≠ .fpuLoad128) (imm12 : BitVec 12)
    (Rn Rt : BitVec 5) (hRt : Rt ≠ 31#5) :
    CtlIndep (uimmInst op.fields.1 op.fields.2.2 imm12 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_uimm_ex (size := op.fields.1) (opc := op.fields.2.2) (imm12 := imm12)
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_gpr_load_err (op := op) hop hRt (LDST.Reg_offset.uimm12 imm12) str M y h31
  · exact sameCtl_gpr_load (op := op) hop hRt (LDST.Reg_offset.uimm12 imm12) str M y h31

theorem ctlIndep_uimm_store (op : StoreOp) (hop : op ≠ .fpuStore128) (imm12 : BitVec 12)
    (Rn Rt : BitVec 5) (hRt : Rt ≠ 31#5) :
    CtlIndep (uimmInst op.fields.1 op.fields.2.2 imm12 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_uimm_ex (size := op.fields.1) (opc := op.fields.2.2) (imm12 := imm12)
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_gpr_store_err (op := op) hop hRt (LDST.Reg_offset.uimm12 imm12) str M y h31
  · exact sameCtl_gpr_store (op := op) hop hRt (LDST.Reg_offset.uimm12 imm12) str M y h31

theorem ctlIndep_unsc_load (op : LoadOp) (hop : op ≠ .fpuLoad128) (imm9 : BitVec 9)
    (Rn Rt : BitVec 5) (hRt : Rt ≠ 31#5) :
    CtlIndep (unscInst op.fields.1 op.fields.2.2 imm9 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_unsc_ex (size := op.fields.1) (opc := op.fields.2.2) (imm9 := imm9)
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_gpr_load_err (op := op) hop hRt (LDST.Reg_offset.simm9 imm9) str M y h31
  · exact sameCtl_gpr_load (op := op) hop hRt (LDST.Reg_offset.simm9 imm9) str M y h31

theorem ctlIndep_unsc_store (op : StoreOp) (hop : op ≠ .fpuStore128) (imm9 : BitVec 9)
    (Rn Rt : BitVec 5) (hRt : Rt ≠ 31#5) :
    CtlIndep (unscInst op.fields.1 op.fields.2.2 imm9 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_unsc_ex (size := op.fields.1) (opc := op.fields.2.2) (imm9 := imm9)
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_gpr_store_err (op := op) hop hRt (LDST.Reg_offset.simm9 imm9) str M y h31
  · exact sameCtl_gpr_store (op := op) hop hRt (LDST.Reg_offset.simm9 imm9) str M y h31

theorem ctlIndep_reg_load (op : LoadOp) (hop : op ≠ .fpuLoad128) (Rm : BitVec 5) (option : BitVec 3)
    (S : BitVec 1) (Rn Rt : BitVec 5) (ho : Arm.BitVec.lsb option 1 = 1#1) (hRt : Rt ≠ 31#5) :
    CtlIndep (regInst op.fields.1 op.fields.2.2 Rm option S Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_regI_ex (size := op.fields.1) (opc := op.fields.2.2) (Rm := Rm) (option := option) (S := S) ho
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_gpr_load_err (op := op) hop hRt (LDST.Reg_offset.reg Rm option S) str M y h31
  · exact sameCtl_gpr_load (op := op) hop hRt (LDST.Reg_offset.reg Rm option S) str M y h31

theorem ctlIndep_reg_store (op : StoreOp) (hop : op ≠ .fpuStore128) (Rm : BitVec 5)
    (option : BitVec 3) (S : BitVec 1) (Rn Rt : BitVec 5)
    (ho : Arm.BitVec.lsb option 1 = 1#1) (hRt : Rt ≠ 31#5) :
    CtlIndep (regInst op.fields.1 op.fields.2.2 Rm option S Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_regI_ex (size := op.fields.1) (opc := op.fields.2.2) (Rm := Rm) (option := option) (S := S) ho
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_gpr_store_err (op := op) hop hRt (LDST.Reg_offset.reg Rm option S) str M y h31
  · exact sameCtl_gpr_store (op := op) hop hRt (LDST.Reg_offset.reg Rm option S) str M y h31

theorem ctlIndep_fpUimm_load (sz : ScalarSize) (hsz : FpSz sz) (imm12 : BitVec 12)
    (Rn Rt : BitVec 5) :
    CtlIndep (fpUimmInst (fpSizeF sz) 1 imm12 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_fpUimm_ex (size := fpSizeF sz) (opc := 1)
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_fp_load_err hsz (LDST.Reg_offset.uimm12 imm12) str M y h31
  · exact sameCtl_fp_load hsz (LDST.Reg_offset.uimm12 imm12) str M y h31

theorem ctlIndep_fpUimm_store (sz : ScalarSize) (hsz : FpSz sz) (imm12 : BitVec 12)
    (Rn Rt : BitVec 5) :
    CtlIndep (fpUimmInst (fpSizeF sz) 0 imm12 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_fpUimm_ex (size := fpSizeF sz) (opc := 0)
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_fp_store_err hsz (LDST.Reg_offset.uimm12 imm12) str M y h31
  · exact sameCtl_fp_store hsz (LDST.Reg_offset.uimm12 imm12) str M y h31

theorem ctlIndep_fpReg_load (sz : ScalarSize) (hsz : FpSz sz) (Rm : BitVec 5) (option : BitVec 3)
    (S : BitVec 1) (Rn Rt : BitVec 5) (ho : Arm.BitVec.lsb option 1 = 1#1) :
    CtlIndep (fpRegInst (fpSizeF sz) 1 Rm option S Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_fpReg_ex (size := fpSizeF sz) (opc := 1) (Rm := Rm) (option := option) (S := S) ho
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_fp_load_err hsz (LDST.Reg_offset.reg Rm option S) str M y h31
  · exact sameCtl_fp_load hsz (LDST.Reg_offset.reg Rm option S) str M y h31

theorem ctlIndep_fpReg_store (sz : ScalarSize) (hsz : FpSz sz) (Rm : BitVec 5) (option : BitVec 3)
    (S : BitVec 1) (Rn Rt : BitVec 5) (ho : Arm.BitVec.lsb option 1 = 1#1) :
    CtlIndep (fpRegInst (fpSizeF sz) 0 Rm option S Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  obtain ⟨str, hex⟩ := exec_fpReg_ex (size := fpSizeF sz) (opc := 0) (Rm := Rm) (option := option) (S := S) ho
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_fp_store_err hsz (LDST.Reg_offset.reg Rm option S) str M y h31
  · exact sameCtl_fp_store hsz (LDST.Reg_offset.reg Rm option S) str M y h31

theorem ctlIndep_fpUnsc_load (sz : ScalarSize) (hsz : FpSz sz) (imm9 : BitVec 9)
    (Rn Rt : BitVec 5) :
    CtlIndep (fpUnscInst (fpSizeF sz) 1 imm9 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  have hex : ∀ s : ArmState, Arm.exec_inst (fpUnscInst (fpSizeF sz) 1 imm9 Rn Rt) s =
      Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := imm9, Rn := Rn, Rt := Rt } s := fun s => rfl
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_ldstur_load_err hsz imm9 M y h31
  · exact sameCtl_ldstur_load hsz imm9 M y h31

theorem ctlIndep_fpUnsc_store (sz : ScalarSize) (hsz : FpSz sz) (imm9 : BitVec 9)
    (Rn Rt : BitVec 5) :
    CtlIndep (fpUnscInst (fpSizeF sz) 0 imm9 Rn Rt) := by
  refine ctlIndep_of fun M y => ?_
  have hex : ∀ s : ArmState, Arm.exec_inst (fpUnscInst (fpSizeF sz) 0 imm9 Rn Rt) s =
      Arm.LDST.exec_ldstur { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := imm9, Rn := Rn, Rt := Rt } s := fun s => rfl
  rw [hex (setMem M y), hex y]
  by_cases h31 : Rn = 31#5 ∧ ¬ CheckSPAlignment y
  · exact sameCtl_ldstur_store_err hsz imm9 M y h31
  · exact sameCtl_ldstur_store hsz imm9 M y h31

/-! ## Event-free prefixes of lines -/

/-- The events of a line list whose lines' instructions have no memory kind are empty. -/
theorem linesEvs_insKind_none : ∀ {env : Env} {pre : List Line} (s : ArmState),
    (∀ ln ∈ pre, ∃ x t', ln = .ins x t' ∧ insnKind x = none) → linesEvs env pre s = []
  | env, [], _, _ => rfl
  | env, .ins i t :: pre, s, h => by
    obtain ⟨x, u, e, hk⟩ := h _ List.mem_cons_self
    cases e
    simp only [linesEvs]
    cases ha : i.toArmInst env with
    | error _ => rfl
    | ok ai =>
      simp only [ha]
      split
      · simp only [instEvs_none ha hk, List.nil_append]
        exact linesEvs_insKind_none _ (fun ln hl => h ln (List.mem_cons_of_mem _ hl))
      · simp only [instEvs_none ha hk]
  | env, .label _ :: _, _, h => by obtain ⟨x, t', e, -⟩ := h _ List.mem_cons_self; cases e
  | env, .word _ _ :: _, _, h => by obtain ⟨x, t', e, -⟩ := h _ List.mem_cons_self; cases e
  | env, .data _ :: _, _, h => by obtain ⟨x, t', e, -⟩ := h _ List.mem_cons_self; cases e

/-- **An event-free prefix of lines does not touch the memory**: running it over `setMem M s` is
`setMem M` of running it over `s` (its events are empty, so its footprint is memory-free). -/
theorem preMem {env : Env} {pre : List Line}
    (hk : ∀ ln ∈ pre, ∃ x t', ln = .ins x t' ∧ insnKind x = none) (M : Memory) (s : ArmState) :
    execLines env pre (setMem M s) = (execLines env pre s).map (setMem M) := by
  have h := ofoot_execLines env pre s
  rw [linesEvs_insKind_none s hk] at h
  simpa only [applyW] using h.2 M trivial

open Classical in
/-- **Receptiveness of a straight-line form with an event-free prefix** (`straightSem_pre`): the
memory-independent shape of the step (`straightSem_one` with the prefix's `preMem`): the prefix's
end state `y1` does not depend on the memory, and the step's value at any memory is the
if-expression on the access's execution at that memory. -/
theorem straightSem_pre {F : BitVec 64 → Prop} {ctx : FnCtx} {i ic : MInst} {uses : List CV}
    {w : ArmState} {ops : Array Operand} {pre : List Line} {x : Insn}
    {t : Option Clif.TrapCode} {a : ArmInst}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hl : ic.lines ctx {} = .ok (pre ++ [.ins x t], {}))
    (hk : ∀ ln ∈ pre, ∃ x' t', ln = .ins x' t' ∧ insnKind x' = none)
    (ha : x.toArmInst env0 = .ok a)
    (ha' : x.toArmInst { env0 with pc := env0.pc + 4 * pre.length } = .ok a)
    (hc : CtlIndep a) (y1 : ArmState)
    (hy1 : execLines env0 pre (placeUses ops (canonRegs ops) uses w) = some y1) (M : Memory) :
    straightSem F ctx i uses (setMem M w) =
      if AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w) ∧
          Arm.r .PC (exec_inst a (setMem M y1)) = Arm.r .PC (setMem M y1) + 4#64 ∧
          Arm.r .ERR (exec_inst a (setMem M y1)) = .None ∧
          (exec_inst a (setMem M y1)).program = w.program then
        some (defVals ops (canonRegs ops) (exec_inst a (setMem M y1)),
          exec_inst a (setMem M y1), Ctl.next)
      else none := by
  unfold straightSem
  simp only [hops, hic, placeUses_setMem, accessOk_setMem, execMInst, hl]
  rw [execLines_append env0 pre [.ins x t] (setMem M (placeUses ops (canonRegs ops) uses w)),
    preMem hk M (placeUses ops (canonRegs ops) uses w), hy1]
  simp only [Option.map_some, Option.bind_some]
  have e1 : execLines { env0 with pc := env0.pc + 4 * pre.length } [.ins x t] (setMem M y1) =
      if Arm.r .PC (exec_inst a (setMem M y1)) = Arm.r .PC (setMem M y1) + 4#64 then
        some (exec_inst a (setMem M y1)) else none := by
    simp only [execLines, ha']
  rw [e1]
  by_cases hA : AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w)
  · rw [if_pos hA]
    by_cases hP : Arm.r .PC (exec_inst a (setMem M y1)) = Arm.r .PC (setMem M y1) + 4#64
    · rw [if_pos hP]
      show (if Arm.r .ERR (exec_inst a (setMem M y1)) = .None ∧
          (exec_inst a (setMem M y1)).program = (setMem M w).program then
        some (defVals ops (canonRegs ops) (exec_inst a (setMem M y1)),
          exec_inst a (setMem M y1), Ctl.next) else none) = _
      by_cases hC1 : Arm.r .ERR (exec_inst a (setMem M y1)) = .None ∧
          (exec_inst a (setMem M y1)).program = (setMem M w).program
      · rw [if_pos hC1, if_pos ⟨hA, hP, hC1.1, hC1.2.trans (setMem_program M w)⟩]
      · rw [if_neg hC1, if_neg (fun h => hC1 ⟨h.2.2.1, h.2.2.2.trans (setMem_program M w)⟩)]
    · rw [if_neg hP, if_neg (fun h => hP h.2.1)]
  · rw [if_neg hA, if_neg (fun h => hA h.1)]

/-! ## The events of the plain load/store instructions on any memory -/

/-- **The events of a plain GPR load on any memory** are the single read event at the base
register's value plus the offset's value, of the access size, reading the memory — so they only
depend on the base and offset values (and the `sp`-alignment branch). -/
theorem immEvs_load_eq (op : LoadOp) (hop : op ≠ .fpuLoad128) (Rn Rt Rn' Rt' : BitVec 5)
    (imm imm' : Arm.LDST.Reg_offset) (M : Memory) (s y : ArmState)
    (ha : read_gpr 64 Rn s = read_gpr 64 Rn' y)
    (hi : imm.value op.fields.1.toNat s = imm'.value op.fields.1.toNat y)
    (hRn : (Rn = 31#5) ↔ (Rn' = 31#5))
    (h31s : Rn = 31#5 → CheckSPAlignment s) (h31y : Rn' = 31#5 → CheckSPAlignment y) :
    immEvs (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) (setMem M s) =
      immEvs (gprCls op.fields.1 op.fields.2.2 Rn' Rt' imm') (setMem M y) := by
  cases op <;> simp at hop <;> simp only [LoadOp.fields] at hi <;>
  · simp (config := {decide := true}) only [immEvs, gprCls, LoadOp.fields, log2,
      Arm.LDST.reg_imm_constrain_unpredictable, check_sp_sm', hRn, Bool.false_eq_true,
      not_false_eq_true, and_true, and_false, false_and, decide_eq_true_eq, if_false, ite_true]
    by_cases hA1 : Rn' = 31#5 ∧ ¬ CheckSPAlignment s
    · exact absurd hA1 (fun h => h.2 (h31s (hRn.mpr h.1)))
    · by_cases hA2 : Rn' = 31#5 ∧ ¬ CheckSPAlignment y
      · exact absurd hA2 (fun h => h.2 (h31y h.1))
      · rw [if_neg hA1, if_neg hA2]
        simp only [read_gpr_sm, offset_value_sm, setMem_mem]
        rw [ha, hi]
        rfl

/-- **… of a plain GPR store**: a write of the data register's bytes. -/
theorem immEvs_store_eq (op : StoreOp) (hop : op ≠ .fpuStore128) (Rn Rt Rn' Rt' : BitVec 5)
    (imm imm' : Arm.LDST.Reg_offset) (M : Memory) (s y : ArmState)
    (ha : read_gpr 64 Rn s = read_gpr 64 Rn' y)
    (hd : Arm.r (Arm.StateField.GPR Rt) s = Arm.r (Arm.StateField.GPR Rt') y)
    (hi : imm.value op.fields.1.toNat s = imm'.value op.fields.1.toNat y)
    (hRt : Rt ≠ 31#5 ∧ Rt' ≠ 31#5)
    (hRn : (Rn = 31#5) ↔ (Rn' = 31#5))
    (h31s : Rn = 31#5 → CheckSPAlignment s) (h31y : Rn' = 31#5 → CheckSPAlignment y) :
    immEvs (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) (setMem M s) =
      immEvs (gprCls op.fields.1 op.fields.2.2 Rn' Rt' imm') (setMem M y) := by
  cases op <;> simp at hop <;> simp only [StoreOp.fields] at hi <;>
  · simp (config := {decide := true}) only [immEvs, gprCls, StoreOp.fields, log2,
      Arm.LDST.reg_imm_constrain_unpredictable, check_sp_sm', hRn, Bool.false_eq_true,
      not_false_eq_true, and_true, and_false, false_and, decide_eq_true_eq, if_false, ite_true]
    by_cases hA1 : Rn' = 31#5 ∧ ¬ CheckSPAlignment s
    · exact absurd hA1 (fun h => h.2 (h31s (hRn.mpr h.1)))
    · by_cases hA2 : Rn' = 31#5 ∧ ¬ CheckSPAlignment y
      · exact absurd hA2 (fun h => h.2 (h31y h.1))
      · rw [if_neg hA1, if_neg hA2]
        simp (config := {decide := true}) [gprCls, ldst_read, read_gpr_zr_sm, read_gpr,
          read_gpr_sm, offset_value_sm, setMem_mem, ha, hi, hd, if_pos hRt.1, if_pos hRt.2]
        refine ⟨?_, ?_⟩
        · have ha' : r (StateField.GPR Rn) s = r (StateField.GPR Rn') y := by
            simpa [read_gpr] using ha
          simp only [r_setMem, ha']
          congr 1
          try simpa using hi
        · have hz : ∀ n, read_gpr_zr n Rt s = read_gpr_zr n Rt' y := fun n => by
            simp only [read_gpr_zr, read_gpr, hd]; rw [if_pos hRt.1, if_pos hRt.2]
          first
            | rw [if_pos hRt.1, if_pos hRt.2]
            | (congr 1; exact hz _)

end Concurrency.ArmAllocThread

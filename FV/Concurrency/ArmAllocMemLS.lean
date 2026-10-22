import FV.Concurrency.ArmAllocMem
import FV.Concurrency.VCodeAddr
import FV.Backend.Proof.RegallocMem
import FV.Backend.Proof.RegallocMemFP

/-!
# Layer 4b for the plain load/store items of the atomics scope (T2h, #311)

The per-item obligation `ArmAllocThread.ItemSim` at the items whose instruction is a **plain
load/store** (GPR `load`/`store`, SIMD&FP `fpuLoad`/`fpuStore` of 32/64 bits), and the run level
for functions whose items are event-free, `fence`, a covered `ldar`/`stlr`, or such a plain
load/store:

* `oneEvPre`: **a straight-line form with an event-free prefix of lines and one access line**
(`OneEvPreForm`), generalising `OneEvForm`/`oneEv_op` to the forms whose offset `memFinalize`
computes through `x16` (`loadConst64`); the prefix's steps are event-free and do not read the
memory, the access's events on any memory are the canonical run's (the **event equality**
`OneEvPreForm.ev`), and the source step exists for every read value (**receptiveness**,
`straightSem_pre`);
* the one-line forms (`unscaled`, `unsignedOffset`, `regReg`, `regScaled`, `regScaledExtended`,
`regExtended`) are `oneEvPre` with the empty prefix; the event equality per addressing mode:
for every mode the allocated and the canonical runs access the same address (the base and index
registers' values agree, `useVals`/`placeUses`; stack offsets go through `sp`, which `SameWorld`
keeps);
* `MemScopeLS`: every instruction is event-free (`NoEvForm`), `fence`, a covered `ldar`/`stlr`,
or a covered plain load/store (`LSForm`); **`arm_alloc_refines_ls`**: such a function's precise
Arm runs from `Q`-related states realize runs of the allocated code with `Refines` up to `Done`
(`arm_alloc_refines_mem`'s conclusion);
* witnesses per addressing mode (`ArmAllocMemLSWitness`).
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

end Concurrency.ArmAllocThread

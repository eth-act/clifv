import FV.E2E.LinkArmTwinCE
import FV.E2E.LinkArmTwinCRun
import FV.E2E.LinkArmTwinCLockLslWitness
import FV.E2E.LinkArmStage2ZWitness
import FV.E2E.LinkArmIniOfWitness
import FV.E2E.LinkArmThmPRBG

/-!
# Witnesses: twins relating the errors, `DetPRBR` (SEM1 #537, #716, #719)

On the slotted system `Lsl` (`f` calls `h` then `r`), at the calling function `f`, on two distinct
returned entries (they differ in `x1`):

* `twinBaseCE_Lsl`: `twinBaseCE_of_lock` (shared return index `0`); `twinCE_Lsl`: `TwinCE` at every
  depth; `twinCE_symm_Lsl`, `twinCE_trans_Lsl` (`TwinCE.symm`, `TwinCE.trans`);
* `tableOfE_twinCE_Lsl`: the machine's own prefix-closed table (`tableOfE_iniOf_Lsl`) of one entry
  is the other's (`tableOfE_twinCE`);
* `callTwinCE_zero_Lsl`, `detTabPRBE_zero_Lsl`, `detTabPRBr_zero_Lsl`: `CallTwinCE` at depth `0`
  (no callee run returns at depth `0`) and the table transfers from it (`detTabPRBE_ofCE`,
  `detTabPRBr_ofCE`);
* `thmPRBRLE_allCR_Lsl`, `thmPRBG_allCR_Lsl`: the `DetPRBR` forms at every depth (`Ok`, budget,
  `BaseRetOk`, `RetCount` discharged; the determinism premises remain), and
  `thmPRBRLE_allCR_of_det_Lsl` (from `DetPRB` through `DetPRB.toR`);
* `twinNC_base_of_twoRun_Lsl`: the first `TwinNC` clause from the backend lock form
  (`twinNC_base_of_twoRun`, `actRL_step_mach`) for `r` on two distinct states (they differ in
  `x30`), one step.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof

/-- A returned entry of `f`: pc at `x30`, no error, `f`'s code. -/
noncomputable def sRetF : Arm.ArmState :=
  let b := Arm.w .ERR .None (Arm.set_program uImg ((Lsl.A fF).fb.program (Lsl.A fF).base))
  Arm.w .PC (Arm.r (.GPR 30#5) b) b

/-- `sRetF` with a different `x1`. -/
noncomputable def sRetF₁ : Arm.ArmState :=
  Arm.w (.GPR 1#5) (Arm.r (.GPR 1#5) sRetF + 1) sRetF

theorem sRetF_ne : sRetF ≠ sRetF₁ := by
  intro e
  have := congrArg (Arm.r (.GPR 1#5)) e
  simp only [sRetF₁, Arm.r_of_w_same] at this
  exact absurd this (by bv_omega)

theorem retAt_sRetF : Lsl.RetAt fF sRetF sRetF := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [sRetF, xreg, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program]

theorem retAt_sRetF₁ : Lsl.RetAt fF sRetF₁ sRetF₁ := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [sRetF₁, sRetF, xreg, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program]

/-- **`twinBaseCE_of_lock` at the calling function `f`, on two distinct entries.** -/
theorem twinBaseCE_Lsl (M : Nat) : Lsl.TwinBaseCE M fF sRetF sRetF₁ :=
  Lsl.twinBaseCE_of_lock Lsl_ok fF_mem (List.all_eq_true.mp lsl_blrLow fF fF_mem) (K := Lsl.D)
    (c := BitVec.ofNat 64 Lsl.D) (by simp [Nat.mod_eq_of_lt lsl_D_lt])
    (fun h hc => Lsl_ok.depth h (Lsl.callee_mem hc)) (T := 0)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    ⟨retAt_sRetF, retAt_sRetF₁⟩

/-- **`TwinCE` at every depth at `f`, on two distinct entries** (the nested clause: no call
before the return at index `0`). -/
theorem twinCE_Lsl : ∀ M, Lsl.TwinCE M fF sRetF sRetF₁
  | 0 => twinBaseCE_Lsl 0
  | M + 1 => ⟨twinBaseCE_Lsl (M + 1), fun _ hi => absurd retAt_sRetF (hi 0 (Nat.succ_pos _))⟩

theorem twinCE_symm_Lsl (M : Nat) : Lsl.TwinCE M fF sRetF₁ sRetF :=
  LinkSys.TwinCE.symm Lsl (twinCE_Lsl M)

theorem twinCE_trans_Lsl (M : Nat) : Lsl.TwinCE M fF sRetF sRetF :=
  LinkSys.TwinCE.trans Lsl (twinCE_Lsl M) (twinCE_symm_Lsl M)

/-- **The prefix-closed table carries over between the two entries.** -/
theorem tableOfE_twinCE_Lsl (M : Nat) :
    Lsl.TableOfE M fF sRetF₁ (Lsl.iniOf M fF sRetF) :=
  Lsl.tableOfE_twinCE (twinCE_Lsl M)
    (tableOfE_iniOf_Lsl M fF_mem (by simp [sRetF, Arm.w_program, program_set_program]))

/-- `CallTwinCE` at depth `0`: no callee run returns at depth `0`. -/
theorem callTwinCE_zero_Lsl : Lsl.CallTwinCE (fun M _ => Lsl.K M) 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ cs rvals cm' _ _ _ _ _ _ _ hrun =>
    absurd hrun ((inferInstance : Lsl.CrunOk).zero cs rvals cm')

theorem detTabPRBE_zero_Lsl : Lsl.DetTabPRBE (fun M _ => Lsl.K M) 0 :=
  Lsl.detTabPRBE_ofCE callTwinCE_zero_Lsl

theorem detTabPRBr_zero_Lsl : Lsl.DetTabPRBr (fun M _ => Lsl.K M) 0 :=
  Lsl.detTabPRBr_ofCE callTwinCE_zero_Lsl

/-- **`ThmPRBRLE` at every depth on the slotted system from `DetPRBR`, `DetTabPRBE`.** -/
theorem thmPRBRLE_allCR_Lsl (hdet : ∀ M, Lsl.DetPRBR (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRLE_allCR Lsl_ok (Lsl.budget_K Lsl_ok) needSlots baseRetOk_Lsl retCount_Lsl hdet hdt M

/-- The same from `DetPRB` (`DetPRB.toR`). -/
theorem thmPRBRLE_allCR_of_det_Lsl (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M :=
  thmPRBRLE_allCR_Lsl (fun M => LinkSys.DetPRB.toR Lsl (hdet M)) hdt M

/-- **`ThmPRBG` at every depth on the slotted system from `DetPRBR`, `DetTabPRBE`,
`DetTabPRBr`.** -/
theorem thmPRBG_allCR_Lsl (hdet : ∀ M, Lsl.DetPRBR (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M)
    (hdtr : ∀ M, Lsl.DetTabPRBr (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBG (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBG_allCR Lsl_ok (Lsl.budget_K Lsl_ok) needSlots baseRetOk_Lsl retCount_Lsl hdet hdt
    hdtr M

/-- A state of `r`'s image with the stack pointer at `0x100000`. -/
noncomputable def sW : Arm.ArmState := Arm.w (.GPR 31#5) (BitVec.ofNat 64 0x100000) uImg

/-- `sW` with a different `x30`. -/
noncomputable def sW₁ : Arm.ArmState := Arm.w (.GPR 30#5) (Arm.r (.GPR 30#5) sW + 1) sW

theorem sW_ne : sW₁ ≠ sW := by
  intro e
  have := congrArg (Arm.r (.GPR 30#5)) e
  simp only [sW₁, Arm.r_of_w_same] at this
  exact absurd this (by bv_omega)

theorem spv_sW : spv sW = BitVec.ofNat 64 0x100000 := by
  simp [spv, sW, Arm.r_of_w_same]

theorem room_sW :
    Lsl.D ≤ (BitVec.ofNat 64 0x100000 - BitVec.ofNat 64 (frameDrop (Lsl.A fR).af)).toNat := by
  native_decide

theorem mem_sW₁ (a : BitVec 64) : sW₁.mem a = uImg.mem a := by
  simp only [sW₁, sW, Arm.ArmState.mem_w_eq_mem]

theorem img_uImg (a : BitVec 64) (ha : Lsl.Img a) : uImg.mem a = Lsl.imgMem a := by
  rw [uImg, mem_withImg]; simp [ha]

/-- **The first `TwinNC` clause from the backend's lock form, on two distinct states** of `r`
(one step; the lock at index `0` is `StEqOutX` of states differing in `x30` only). -/
theorem twinNC_base_of_twoRun_Lsl (M : Nat) {lm : Std.HashMap Backend.Lbl Nat}
    {base : BitVec 64} {psF : PState} {G G' : BitVec 64 → Prop} {gv : Nat → String → Prop} :
    ∀ i < 1, Arm.r .PC (runX (Lsl.mach M fR) i sW₁) = Arm.r .PC (runX (Lsl.mach M fR) i sW) ∧
      spv (runX (Lsl.mach M fR) i sW₁) = spv (runX (Lsl.mach M fR) i sW) ∧
      (∀ h, Lsl.CallsTo fR (runX (Lsl.mach M fR) i sW₁) h ↔
        Lsl.CallsTo fR (runX (Lsl.mach M fR) i sW) h) ∧
      ∀ h, Lsl.CallsTo fR (runX (Lsl.mach M fR) i sW₁) h → ∀ a,
        Lsl.SlotByte h (spv (runX (Lsl.mach M fR) i sW₁)) a →
        (runX (Lsl.mach M fR) i sW₁).mem (BitVec.ofNat 64 a) =
          (runX (Lsl.mach M fR) i sW).mem (BitVec.ofNat 64 a) := by
  have hlk0 : StEqOutX (fun _ => False) sW₁ sW :=
    ⟨fun f hf => Arm.r_of_w_different hf, Arm.w_program, fun a _ => by
      simp only [sW₁, Arm.ArmState.mem_w_eq_mem]⟩
  refine Lsl.twinNC_base_of_twoRun Lsl_ok fR_mem (List.all_eq_true.mp lsl_blrLow fR fR_mem)
    (lm := lm) (base := base) (s := sW) (t0 := sW₁) (XI := ExtSemI.const Lsl.Xb) rfl
    (psF := psF) (K := Lsl.D) (G := G) (G' := G') (gv := gv)
    (by rw [spv_sW]; exact room_sW) (fun h hc => Lsl_ok.depth h (Lsl.callee_mem hc))
    (fun i hi => ?_) (fun i hi a ha => ?_) (fun i hi a ha => ?_)
    (fun i _ h hc => absurd hc (Lsl.not_callsTo_of_noHook fR_noHookLines _ h))
    (fun i _ h hc => absurd hc (Lsl.not_callsTo_of_noHook fR_noHookLines _ h))
  · obtain rfl : i = 0 := by omega
    exact ⟨.halt sW, .halt sW, hlk0.1, hlk0.2.1, fun a _ => hlk0.2.2 a id⟩
  · obtain rfl : i = 0 := by omega
    exact (mem_sW₁ a).trans (img_uImg a ha)
  · obtain rfl : i = 0 := by omega
    show sW.mem a = _
    simp only [sW, Arm.ArmState.mem_w_eq_mem]
    exact img_uImg a ha

end E2E.LinkSlotSysWitness

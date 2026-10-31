import FV.E2E.LinkArmDetInduction
import FV.E2E.LinkArmLockRetWitness
import FV.E2E.LinkArmIniOfWitness
import FV.E2E.LinkArmThmPRBRZeroWitness

/-!
# Witnesses: the determinism induction on the slotted system (SEM1 #537, #713, #732)

`Lsl = L0.std` (`LinkSlotSysWitness`): `f` calls `h`, then `r`, which reads the slot bytes `h`
left behind. Every premise of the determinism induction (`LinkArmDetInduction.lean`) holds on it,
none vacuously (`NeedSlots`, `NeedNI`):

* the checks on the compiled code: `x30Free_Lsl`, `retsLow_Lsl`, `blrLow_Lsl` (`native_decide`
  on `detChecksB`);
* `needNI_Lsl`: `h`'s frame has a slot region (`fH_frame`; `NeedNI` holds, so `BaseNIX` and the
  two-run route are not vacuous);
* `hookNIX_L0`, `hookNIX_Lsl`, `baseNIX_L0`: the closed base's hooks (`pc + 4`, identity TLS) do
  not observe the exterior; `baseNIX_Lsl` by `BaseNIX.std` (`Lsl = L0.std`);
  `hooks_lock_base_LslK`, `hooks_lock_tls_LslK`: the hook locks on two distinct states without
  the `HookNIX` premise;
* **`detInduction_Lsl`**, **`thmPRBRLE_allK_Lsl`**, `thmPRBRL_allK_Lsl`,
  **`detRunPRBCRU_allK_Lsl`**, **`detPRBRU_allK_Lsl`**, **`callTwinCET_allK_Lsl`**,
  **`detTabPRBE_allK_Lsl`**, **`detTabPRBr_allK_Lsl`**: the induction's conclusions at every
  depth, unconditional;
* the chain's steps with every premise discharged: `lockRet_Lsl`, `callLock_Lsl`,
  `stage2PRBZSE_Lsl`, `lockRet_of_Lsl`, `detTabPRBE_of_Lsl`, `thmPRBRLE_allCRU_Lsl` (the U chain),
  `progXBT_rel_LslK`, `xnifXPBTGY_LslK`, `canonCallTwin_LslK`, `hcallLockXP_LslK`,
  `detTabPRBr_ofCT_Lsl`, `detPRBRU_ofC_Lsl`.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- The checks of every compiled function, as one decision. -/
def detChecksB : Bool :=
  Lsl.P.funcs.all fun g =>
    (match labelOffsets (Lsl.A g).fa.lines with
      | .ok lm => (Lsl.A g).fa.x30Free lm
      | .error _ => true) && (Lsl.A g).vc.retsLow && (Lsl.A g).fa.blrLow

theorem detChecksB_true : detChecksB = true := by native_decide

theorem x30Free_Lsl : ∀ g ∈ Lsl.P.funcs, ∀ lm, labelOffsets (Lsl.A g).fa.lines = .ok lm →
    (Lsl.A g).fa.x30Free lm = true := by
  intro g hg lm hlm
  have h := List.all_eq_true.mp detChecksB_true g hg
  simp only [hlm, Bool.and_eq_true] at h
  exact h.1.1

theorem retsLow_Lsl : ∀ g ∈ Lsl.P.funcs, (Lsl.A g).vc.retsLow = true := by
  intro g hg
  have h := List.all_eq_true.mp detChecksB_true g hg
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem blrLow_Lsl : ∀ g ∈ Lsl.P.funcs, (Lsl.A g).fa.blrLow = true := by
  intro g hg
  have h := List.all_eq_true.mp detChecksB_true g hg
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- `h`'s frame body is not just its spill area: its slot region (`NeedNI`'s second disjunct). -/
theorem fH_frame : (RAFrame.compute (Lsl.A fH).vcp (Lsl.A fH).rf).size ≠
    (Lsl.A fH).af.frameSize - clobberBytes (Lsl.A fH).af.saves := by
  native_decide

/-- **The slotted system needs non-interference** (`f` calls `h`, whose frame has a slot). -/
theorem needNI_Lsl : Lsl.NeedNI := by
  have h := funcsB_true; simp only [funcsB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, he'⟩ := List.any_eq_true.mp h.2
  exact ⟨fF, by rw [funcs_eq]; simp, fH, .inr (.inl ⟨e, he, by simpa using he'⟩), .inr fH_frame⟩

/-- **The closed base's hooks do not observe the exterior** (the call hook advances the pc, TLS
keeps the state). -/
theorem hookNIX_L0 (F : BitVec 64 → Prop) : HookNIX L0.Hb L0.BaseDest F := by
  refine ⟨fun d _ Z s t h _ => ?_, fun _ _ _ _ _ h _ => h⟩
  show StEqOutX Z (Arm.w .PC (Arm.r .PC s + 4) s) (Arm.w .PC (Arm.r .PC t + 4) t)
  have hpc : Arm.r .PC s = Arm.r .PC t := h.1 _ (by simp)
  refine ⟨fun f hf => ?_, by rw [Arm.w_program, Arm.w_program]; exact h.2.1, fun a ha => ?_⟩
  · by_cases e : f = .PC
    · subst e; rw [Arm.r_of_w_same, Arm.r_of_w_same, hpc]
    · rw [Arm.r_of_w_different e, Arm.r_of_w_different e]; exact h.1 f hf
  · rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]; exact h.2.2 a ha

theorem hookNIX_Lsl (F : BitVec 64 → Prop) : HookNIX Lsl.Hb Lsl.BaseDest F := hookNIX_L0 F

/-- **`hooks_lock_base` without its `HookNIX` premise** (two distinct states: they differ in
`x30`). -/
theorem hooks_lock_base_LslK (F : BitVec 64 → Prop) (M : Nat) {nm : String}
    (hpf : Lsl.P.func? nm = none) (u : Arm.ArmState) (v : BitVec 64) :
    StEqOutX (fun _ => False) ((Lsl.hooks M).call (some nm) u)
      ((Lsl.hooks M).call (some nm) (Arm.w (.GPR 30#5) v u)) :=
  hooks_lock_base_Lsl (hookNIX_Lsl F) M hpf u v

/-- **`hooks_lock_tls` without its `HookNIX` premise.** -/
theorem hooks_lock_tls_LslK (F : BitVec 64 → Prop) (M : Nat) (m : String) (r : Reg)
    (u : Arm.ArmState) (v : BitVec 64) :
    StEqOutX (fun _ => False) ((Lsl.hooks M).tls m r u)
      ((Lsl.hooks M).tls m r (Arm.w (.GPR 30#5) v u)) :=
  hooks_lock_tls_Lsl (hookNIX_Lsl F) M m r u v

theorem baseNIX_L0 : L0.BaseNIX := fun _ _ _ _ F _ _ _ _ _ => hookNIX_L0 F

/-- **`BaseNIX.std` applies**: `Lsl = L0.std`, under `NeedNI` (`needNI_Lsl`). -/
theorem baseNIX_Lsl : Lsl.BaseNIX := baseNIX_L0.std

/-- **The determinism induction on the slotted system**: `ThmPRBRLE` and `LockRet` at every
depth, no premise left. -/
theorem detInduction_Lsl (M : Nat) :
    Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M ∧ Lsl.LockRet (fun M _ => Lsl.K M) M :=
  Lsl.detInduction Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needSlots needNI_Lsl baseNIX_Lsl
    baseRetOk_Lsl retCount_Lsl x30Free_Lsl retsLow_Lsl blrLow_Lsl M

theorem thmPRBRLE_allK_Lsl (M : Nat) : Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRLE_allK Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needSlots needNI_Lsl baseNIX_Lsl
    baseRetOk_Lsl retCount_Lsl x30Free_Lsl retsLow_Lsl blrLow_Lsl M

theorem detRunPRBCRU_allK_Lsl (M : Nat) : Lsl.DetRunPRBCRU (fun M _ => Lsl.K M) M :=
  Lsl.detRunPRBCRU_allK Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needSlots needNI_Lsl
    baseNIX_Lsl baseRetOk_Lsl retCount_Lsl x30Free_Lsl retsLow_Lsl blrLow_Lsl M

/-- **`DetPRBRU` at every depth on the slotted system** (#732). -/
theorem detPRBRU_allK_Lsl (M : Nat) : Lsl.DetPRBRU (fun M _ => Lsl.K M) M :=
  Lsl.detPRBRU_allK Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needSlots needNI_Lsl baseNIX_Lsl
    baseRetOk_Lsl retCount_Lsl x30Free_Lsl retsLow_Lsl blrLow_Lsl M

theorem callTwinCET_allK_Lsl (M : Nat) : Lsl.CallTwinCET (fun M _ => Lsl.K M) M :=
  Lsl.callTwinCET_allK Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needSlots needNI_Lsl
    baseNIX_Lsl baseRetOk_Lsl retCount_Lsl x30Free_Lsl retsLow_Lsl blrLow_Lsl M

/-- **`DetTabPRBE` at every depth on the slotted system** (#716). -/
theorem detTabPRBE_allK_Lsl (M : Nat) : Lsl.DetTabPRBE (fun M _ => Lsl.K M) M :=
  Lsl.detTabPRBE_allK Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needSlots needNI_Lsl
    baseNIX_Lsl baseRetOk_Lsl retCount_Lsl x30Free_Lsl retsLow_Lsl blrLow_Lsl M

/-- **`DetTabPRBr` at every depth on the slotted system.** -/
theorem detTabPRBr_allK_Lsl (M : Nat) : Lsl.DetTabPRBr (fun M _ => Lsl.K M) M :=
  Lsl.detTabPRBr_allK Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needSlots needNI_Lsl
    baseNIX_Lsl baseRetOk_Lsl retCount_Lsl x30Free_Lsl retsLow_Lsl blrLow_Lsl M

/-- **`LockRet` at every depth on the slotted system.** -/
theorem lockRet_Lsl (M : Nat) : Lsl.LockRet (fun M _ => Lsl.K M) M := (detInduction_Lsl M).2

/-- **`CallLock` at every depth on the slotted system** (`callLock_zero`, `callLock_of`). -/
theorem callLock_Lsl : ∀ M, Lsl.CallLock (fun M _ => Lsl.K M) M
  | 0 => Lsl.callLock_zero
  | M + 1 => callLock_of_Lsl (Nat.succ_pos M) (thmPRBRLE_allK_Lsl M) (lockRet_Lsl M)

/-- **The stage-2 contracts at every depth on the slotted system** (`stage2PRBZSE_zero`,
`stage2PRBZS_ofERU` on the induction's facts). -/
theorem stage2PRBZSE_Lsl : ∀ M, Lsl.Stage2PRBZSE (fun M _ => Lsl.K M) M
  | 0 => Lsl.stage2PRBZSE_zero Lsl_ok
  | M + 1 => Lsl.stage2PRBZS_ofERU Lsl_ok (Lsl.budget_K Lsl_ok) needSlots (thmPRBRLE_allK_Lsl M)
      (detPRBRU_allK_Lsl M) (detTabPRBE_allK_Lsl (M + 1)) (retOkPRB_Lsl (M + 1))

theorem thmPRBRL_allK_Lsl (M : Nat) : Lsl.ThmPRBRL (fun M _ => Lsl.K M) M :=
  LinkSys.ThmPRBRLE.toThmPRBRL Lsl (thmPRBRLE_allK_Lsl M)

/-- **`lockRet_of` with every premise discharged** (its depth-`M - 1` hypotheses from the
induction). -/
theorem lockRet_of_Lsl (M : Nat) : Lsl.LockRet (fun M _ => Lsl.K M) M :=
  Lsl.lockRet_of Lsl_ok (Lsl.budget_K Lsl_ok) hooksKeep_Lsl needNI_Lsl baseNIX_Lsl x30Free_Lsl
    retsLow_Lsl blrLow_Lsl (fun _ => thmPRBRL_allK_Lsl (M - 1))
    (fun _ => detPRBRU_allK_Lsl (M - 1)) (fun _ => callTwinCET_allK_Lsl M) (callLock_Lsl M)
    (retOkPRB_Lsl M) (stage2PRBZSE_Lsl M)

/-- **`detTabPRBE_of` with every premise discharged.** -/
theorem detTabPRBE_of_Lsl (M : Nat) : Lsl.DetTabPRBE (fun M _ => Lsl.K M) (M + 1) :=
  Lsl.detTabPRBE_of Lsl_ok (Lsl.budget_K Lsl_ok) (Nat.succ_pos M)
    (by rw [Nat.add_sub_cancel]; exact thmPRBRLE_allK_Lsl M)
    (by rw [Nat.add_sub_cancel]; exact lockRet_Lsl M)

/-- **`thmPRBRLE_allCRU` (the U chain) with every premise discharged.** -/
theorem thmPRBRLE_allCRU_Lsl (M : Nat) : Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRLE_allCRU Lsl_ok (Lsl.budget_K Lsl_ok) needSlots baseRetOk_Lsl retCount_Lsl
    detPRBRU_allK_Lsl detTabPRBE_allK_Lsl M

/-- **`progXBT_rel` with the induction hypotheses discharged.** -/
theorem progXBT_rel_LslK (M : Nat) :
    type_of% (@progXBT_rel_Lsl M (fun _ => thmPRBRL_allK_Lsl (M - 1))
      (fun _ => detPRBRU_allK_Lsl (M - 1)) (fun _ => callTwinCET_allK_Lsl M)) :=
  @progXBT_rel_Lsl M (fun _ => thmPRBRL_allK_Lsl (M - 1))
    (fun _ => detPRBRU_allK_Lsl (M - 1)) (fun _ => callTwinCET_allK_Lsl M)

/-- **`xnifXPBTGY` with `NeedNI` and the induction hypotheses discharged.** -/
theorem xnifXPBTGY_LslK (M : Nat) :
    type_of% (@xnifXPBTGY_Lsl needNI_Lsl M (fun _ => thmPRBRL_allK_Lsl (M - 1))
      (fun _ => detPRBRU_allK_Lsl (M - 1)) (fun _ => callTwinCET_allK_Lsl M)) :=
  @xnifXPBTGY_Lsl needNI_Lsl M (fun _ => thmPRBRL_allK_Lsl (M - 1))
    (fun _ => detPRBRU_allK_Lsl (M - 1)) (fun _ => callTwinCET_allK_Lsl M)

/-- **`canonCallTwin` with the induction hypotheses discharged.** -/
theorem canonCallTwin_LslK (M : Nat) :
    type_of% (@LinkSys.canonCallTwin Lsl (fun M _ => Lsl.K M) Lsl_ok _ (Lsl.budget_K Lsl_ok) M
      (fun _ => thmPRBRL_allK_Lsl (M - 1)) (fun _ => detPRBRU_allK_Lsl (M - 1)) (retOkPRB_Lsl M)
      (stage2PRBZSE_Lsl M) (fun _ => callTwinCET_allK_Lsl M)) :=
  @LinkSys.canonCallTwin Lsl (fun M _ => Lsl.K M) Lsl_ok _ (Lsl.budget_K Lsl_ok) M
    (fun _ => thmPRBRL_allK_Lsl (M - 1)) (fun _ => detPRBRU_allK_Lsl (M - 1)) (retOkPRB_Lsl M)
    (stage2PRBZSE_Lsl M) (fun _ => callTwinCET_allK_Lsl M)

/-- **`hcallLockXP` with the call lock and `HookNIX` discharged.** -/
theorem hcallLockXP_LslK (M : Nat) :
    type_of% (@LinkSys.hcallLockXP Lsl (fun M _ => Lsl.K M) Lsl_ok (Lsl.budget_K Lsl_ok) M
      (callLock_Lsl M)) :=
  @LinkSys.hcallLockXP Lsl (fun M _ => Lsl.K M) Lsl_ok (Lsl.budget_K Lsl_ok) M (callLock_Lsl M)

theorem detTabPRBr_ofCT_Lsl (M : Nat) : Lsl.DetTabPRBr (fun M _ => Lsl.K M) M :=
  LinkSys.detTabPRBr_ofCT Lsl (LinkSys.CallLock.callTwinCET Lsl (callLock_Lsl M))

theorem detPRBRU_ofC_Lsl (M : Nat) : Lsl.DetPRBRU (fun M _ => Lsl.K M) M :=
  LinkSys.detPRBRU_ofC Lsl (LinkSys.detRunPRBCRU_of_lockRet Lsl Lsl_ok (lockRet_of_Lsl M))

end E2E.LinkSlotSysWitness

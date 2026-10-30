import FV.E2E.LinkArmProgramInitE
import FV.E2E.LinkArmThmPRBRZeroWitness

/-!
# Witnesses: the machine's own slot table (SEM1 #537, #700)

On the slotted system `Lsl = L0.std` (`LinkSlotSysWitness`: `f` calls `h`, `r` reads its slot):

* `hooksKeep_L0`, `hooksKeep_Lsl`: the closed base's hooks (`pc + 4`, identity TLS) keep an error
  state and the program;
* `tableOfE_iniOf_Lsl`, `tableOfE_iniOf_some`: the machine's own table is the run's
  (`TableOfE`), at every depth and entry with the function's program, and for a concrete entry;
* `thmPRBRLE_allC_Lsl`: `ThmPRBRLE` at every depth from `DetPRB`, `DetTabPRBE`;
* `backend_correct_program_core_initE_Lsl`, `backend_correct_program_initE_L0`: the top-level
  statements with `Ok`, the budget, `BaseRetOk`, `RetCount` and `HooksKeep` discharged (`DetPRB`,
  `DetTabPRBE` and the entry remain).
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

theorem hooksKeep_L0 : L0.HooksKeep :=
  ⟨fun _ s h => by
      show Arm.r .ERR (Arm.w .PC (Arm.r .PC s + 4) s) ≠ .None
      rw [Arm.r_of_w_different (by simp)]; exact h,
    fun _ _ _ h => h, fun _ s => Arm.w_program, fun _ _ _ => rfl⟩

theorem hooksKeep_Lsl : Lsl.HooksKeep :=
  ⟨hooksKeep_L0.err, hooksKeep_L0.tlsErr, hooksKeep_L0.prog, hooksKeep_L0.tlsProg⟩

/-- **The machine's own table on the slotted system.** -/
theorem tableOfE_iniOf_Lsl (M : Nat) {g : Clif.Function} (hg : g ∈ Lsl.P.funcs)
    {s : Arm.ArmState} (hprog : s.program = (Lsl.A g).fb.program (Lsl.A g).base) :
    Lsl.TableOfE M g s (Lsl.iniOf M g s) :=
  Lsl.tableOfE_iniOf Lsl_ok hooksKeep_Lsl hg hprog

theorem funcs_ne : Lsl.P.funcs ≠ [] := by native_decide

/-- A concrete entry: a function of `Lsl` with its program loaded. -/
theorem tableOfE_iniOf_some : ∃ g ∈ Lsl.P.funcs, ∀ M,
    Lsl.TableOfE M g (Arm.set_program Arm.ArmState.default ((Lsl.A g).fb.program (Lsl.A g).base))
      (Lsl.iniOf M g
        (Arm.set_program Arm.ArmState.default ((Lsl.A g).fb.program (Lsl.A g).base))) := by
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ funcs_ne
  exact ⟨g, hg, fun M => tableOfE_iniOf_Lsl M hg (program_set_program _ _)⟩

/-- **`ThmPRBRLE` at every depth on the slotted system** from `DetPRB` and `DetTabPRBE`. -/
theorem thmPRBRLE_allC_Lsl (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRLE_allC Lsl_ok (Lsl.budget_K Lsl_ok) needSlots baseRetOk_Lsl retCount_Lsl hdet hdt M

/-- **`backend_correct_program_core_initE` on the slotted system** (`Ok`, budget, `BaseRetOk`,
`RetCount`, `HooksKeep` discharged; `DetPRB`, `DetTabPRBE` and the entry remain). -/
theorem backend_correct_program_core_initE_Lsl
    (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M) :
    type_of% (@backend_correct_program_core_initE Lsl Lsl_ok _ (fun M _ => Lsl.K M)
      (Lsl.budget_K Lsl_ok) baseRetOk_Lsl retCount_Lsl hdet hdt hooksKeep_Lsl) :=
  @backend_correct_program_core_initE Lsl Lsl_ok _ (fun M _ => Lsl.K M) (Lsl.budget_K Lsl_ok)
    baseRetOk_Lsl retCount_Lsl hdet hdt hooksKeep_Lsl

/-- **`backend_correct_program_initE` on the slotted system's base `L0`** (`Lsl = L0.std`). -/
theorem backend_correct_program_initE_L0
    (hdet : ∀ M, L0.std.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, L0.std.DetTabPRBE (fun M _ => Lsl.K M) M) :
    type_of% (@backend_correct_program_initE L0 L0_ok (fun M _ => Lsl.K M)
      (L0.budget_K L0_ok) baseRetOk_Lsl retCount_Lsl hdet hdt hooksKeep_L0) :=
  @backend_correct_program_initE L0 L0_ok (fun M _ => Lsl.K M) (L0.budget_K L0_ok)
    baseRetOk_Lsl retCount_Lsl hdet hdt hooksKeep_L0

/-- `stage2PRBZS_ofE` and `countPRB_succE` on the slotted system (one level up). -/
theorem stage2PRBZS_ofE_Lsl {M' : Nat} (ih : Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M')
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) M')
    (hdt : Lsl.DetTabPRBE (fun M _ => Lsl.K M) (M' + 1)) :
    Lsl.Stage2PRBZSE (fun M _ => Lsl.K M) (M' + 1) :=
  Lsl.stage2PRBZS_ofE Lsl_ok (Lsl.budget_K Lsl_ok) needSlots ih hdet hdt (retOkPRB_Lsl (M' + 1))

theorem countPRB_succE_Lsl {M' : Nat} (ih : Lsl.ThmPRBRLE (fun M _ => Lsl.K M) M')
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) M')
    (hdt : Lsl.DetTabPRBE (fun M _ => Lsl.K M) (M' + 1)) :
    Lsl.CountPRBE (fun M _ => Lsl.K M) (M' + 1) :=
  Lsl.countPRB_succE Lsl_ok (Lsl.budget_K Lsl_ok) needSlots ih hdet hdt (retOkPRB_Lsl (M' + 1))

/-- `ThmPRBRLE` at depth `0` on the slotted system (no premise left). -/
theorem thmPRBRLE_zero_Lsl : Lsl.ThmPRBRLE (fun M _ => Lsl.K M) 0 :=
  Lsl.thmPRBRL_ofZSE Lsl_ok (Lsl.budget_K Lsl_ok) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun h => absurd h (Nat.lt_irrefl 0)) (retOkPRB_Lsl 0) (Lsl.stage2PRBZSE_zero Lsl_ok)
    (Lsl.countPRBE_zero Lsl_ok)

/-- The empty prefix: a table and a prefix-closed table have the same count. -/
theorem tabUpTo_count_E_zero (g : Clif.Function) (s : Arm.ArmState) (b : Nat → Nat → BitVec 8) :
    (0 : Nat) = 0 :=
  Lsl.tabUpTo_count_E (Lsl.tabUpTo_zero 1 g s b 0) (Lsl.tabUpToE_zero 1 g s b 0)

end E2E.LinkSlotSysWitness

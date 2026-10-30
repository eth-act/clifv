import FV.E2E.LinkArmTwinCE
import FV.E2E.LinkArmIniOfWitness
import FV.E2E.LinkArmTrapE

/-!
# Witnesses: traps under the slot-byte oracle (SEM1 #537)

On the slotted system `Lsl` (`f` calls `h` then `r`):

* `runEnds_Lsl_trapped`, `runEnds_Lsl_returned`: `RunEnds` of a trap and of a return;
* `stage2PRBZSEnds_zero_Lsl`, **`thmPRBTE_zero_Lsl`**: stage 2 for ending runs and the trapping
  linking statement at depth `0`, with no premise left (`Ok`, budget, `BaseRetOk`, `RetCount`
  discharged; no callee runs at depth `0`);
* **`thmPRBTE_allCR_Lsl`**: `ThmPRBTE` at every depth from `DetPRBR`, `DetTabPRBE`
  (`thmPRBTE_allCR`), and `thmPRBTE_one_Lsl` at depth `1` with `DetTabPRBE` at depth `1` from
  `CallTwinCE`.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof

theorem runEnds_Lsl_trapped (c : Clif.TrapCode) : RunEnds (.trapped c) := runEnds_trapped rfl

theorem runEnds_Lsl_returned (v : List Clif.Val) (m : Clif.Mem) : RunEnds (.returned v m) :=
  runEnds_returned rfl

theorem stage2PRBZSEnds_zero_Lsl : Lsl.Stage2PRBZSEnds (fun M _ => Lsl.K M) 0 :=
  Lsl.stage2PRBZSEnds_zero Lsl_ok

/-- **The trapping linking statement at depth `0` on the slotted system**, no premise left. -/
theorem thmPRBTE_zero_Lsl : Lsl.ThmPRBTE (fun M _ => Lsl.K M) 0 :=
  Lsl.thmPRBTE_ofR Lsl_ok (Lsl.budget_K Lsl_ok) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun h => absurd h (Nat.lt_irrefl 0)) (Lsl.retOkPRB_zero baseRetOk_Lsl retCount_Lsl)
    stage2PRBZSEnds_zero_Lsl

/-- **`ThmPRBTE` at every depth on the slotted system from `DetPRBR`, `DetTabPRBE`.** -/
theorem thmPRBTE_allCR_Lsl (hdet : ∀ M, Lsl.DetPRBR (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRBE (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBTE (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBTE_allCR Lsl_ok (Lsl.budget_K Lsl_ok) needSlots baseRetOk_Lsl retCount_Lsl hdet hdt M

/-- `ThmPRBTE` at depth `1` from `DetPRBR` at depth `0` and `CallTwinCE` at depth `1`
(`stage2PRBZS_ofE_endsR` on `ThmPRBRLE` at depth `0`). -/
theorem thmPRBTE_one_Lsl (hdet : Lsl.DetPRBR (fun M _ => Lsl.K M) 0)
    (htw : Lsl.CallTwinCE (fun M _ => Lsl.K M) 1) :
    Lsl.ThmPRBTE (fun M _ => Lsl.K M) 1 :=
  Lsl.thmPRBTE_ofR Lsl_ok (Lsl.budget_K Lsl_ok)
    (fun _ => LinkSys.ThmPRBRLE.toThmPRBRL Lsl thmPRBRLE_zero_Lsl) (fun _ => hdet)
    (Lsl.retOkPRB_of (κ := fun M _ => Lsl.K M) Lsl_ok needSlots baseRetOk_Lsl retCount_Lsl 1)
    (Lsl.stage2PRBZS_ofE_endsR Lsl_ok (Lsl.budget_K Lsl_ok) needSlots thmPRBRLE_zero_Lsl hdet
      (Lsl.detTabPRBE_ofCE htw)
      (Lsl.retOkPRB_of (κ := fun M _ => Lsl.K M) Lsl_ok needSlots baseRetOk_Lsl retCount_Lsl 1))

end E2E.LinkSlotSysWitness

import FV.E2E.LinkArmStage2PRBZSOf
import FV.E2E.LinkArmRetOkPRB

/-!
# `ThmPRBRL` at every depth (SEM1 #537, #680 (3), stage 2 glue (4))

* **`thmPRBRL_succS`**: `ThmPRBRL κ (M' + 1)` from `ThmPRBRL κ M'` (`thmPRBRL_ofZS` with
  stage 2 by `stage2PRBZS_of`), given `DetPRB κ M'`, `DetTabPRB κ (M' + 1)`,
  `RetOkPRB κ (M' + 1)` and `CountPRB κ (M' + 1)`, under `NeedSlots`;
* **`thmPRBRL_all`**: `ThmPRBRL κ M` for every `M`, from the scope conditions `BaseRetOk` and
  `RetCount` (depth `0`: `thmPRBRL_zero_of`; `RetOkPRB`: `retOkPRB_of`), `DetPRB`, `DetTabPRB`
  and `CountPRB` at every depth; without program callees with slots by `thmPRBRL_of_thm`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The induction step of `ThmPRBRL` with stage 2 discharged** (module doc). -/
theorem thmPRBRL_succS (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hN : L.NeedSlots)
    {M' : Nat} (ih : L.ThmPRBRL κ M') (hdet : L.DetPRB κ M') (hdt : L.DetTabPRB κ (M' + 1))
    (hret : L.RetOkPRB κ (M' + 1)) (hcnt : L.CountPRB κ (M' + 1)) : L.ThmPRBRL κ (M' + 1) :=
  L.thmPRBRL_ofZS hL hκ (fun _ => by rw [Nat.add_sub_cancel]; exact ih)
    (fun _ => by rw [Nat.add_sub_cancel]; exact hdet) hret
    (L.stage2PRBZS_of hL hκ hN ih hdet hdt hret) hcnt

/-- **`ThmPRBRL` at every depth** (module doc). -/
theorem thmPRBRL_all (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hB : L.BaseRetOk)
    (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRB κ M)
    (hdt : ∀ M, L.DetTabPRB κ M) (hcnt : ∀ M, L.CountPRB κ M) (M : Nat) : L.ThmPRBRL κ M := by
  by_cases hN : L.NeedSlots
  · induction M with
    | zero => exact L.thmPRBRL_zero_of hL hκ hB hC
    | succ M ih =>
      exact L.thmPRBRL_succS hL hκ hN ih (hdet M) (hdt (M + 1)) (L.retOkPRB_of hL hN hB hC (M + 1))
        (hcnt (M + 1))
  · exact L.thmPRBRL_of_thm hL hN (L.thm hL hκ M)

end LinkSys

end E2E

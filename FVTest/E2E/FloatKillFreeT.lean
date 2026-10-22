import FVTest.E2E.FloatTotalT
import FV.E2E.SpillKillFreeT

/-!
Non-vacuity of `E2E.spillKillFreeT` / `LinkCheck.killFreeB_of_scopeT` (S11 slice 8, totality
half): on `FloatFinalT`'s `fW` (float `load`, `f64const`, `select`, `store`, `bitcast`; outside
subset E) the premises hold and `killFreeB` of its prepared lowering follows from the theorem
(not from a run of `killFreeB`). Input conditions decided by `native_decide` (witness only).
`lake build FVTest.E2E.FloatKillFreeT`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatKillFreeT

open FloatDriverT FloatFinalT FloatLinkT FloatTotalT

/-- **Witness**: `fW`'s premises of `spillKillFreeT` hold. -/
theorem abiSigsOk_w : Spill.AbiSigsOk fW :=
  abiSigsOk_of_checks (by native_decide) (by native_decide) (by native_decide)

/-- **Witness**: `killFreeB` of `fW`'s prepared lowering, by the theorem. -/
theorem spillKillFreeT_w : Spill.killFreeB (vcpOf fW) = true :=
  spillKillFreeT dominated_w lowerScopeT_w abiSigsOk_w arity_w tryArg_w lowerFunction_w prepare_w

/-- **Witness**: the same from the decided conjuncts of the typed input scope. -/
theorem killFreeB_of_scopeT_w : Spill.killFreeB (vcpOf fW) = true :=
  killFreeB_of_scopeT (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) lowerFunction_w prepare_w

end FloatKillFreeT

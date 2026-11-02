import FV.E2E.LinkScopeInputT2
import FV.E2E.LinkScopeIntT
import FV.Backend.Proof.FormsCoverCompleteT
import FV.Backend.Proof.SpillResClassT

/-! # Run-time checks proven on the strengthened typed scope `fnScopeInTB2`

Two of the four run-time checks of `fnScopeInTB`'s non-E branch hold on every function of
`fnScopeInTB2` (`fnScopeInTB` with the entry-class and float-`select` typing conditions):

* `resClassOkB_of_T2`: `Spill.resClassOkB` (a statement's results are vregs of their classes);
* `formsCoveredB_of_T2`: `formsCoveredB` of `prepare (lowerFunction g)` (every instruction is a
  control form or a covered straight-line form).

Both come from the typed coverage analysis (`Backend.Proof.CovT`, `IselCovT*`):
`Spill.resClassOk_of_lowerScopeT`, `Driver.formsCovered_completeT`. `ctlSpillB` and `ctlInstsB`
stay run-time checks.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- The conjuncts of `fnScopeInTB2` the typed coverage analysis needs. -/
theorem covParts_of_T2 {g : Clif.Function} (h : fnScopeInTB2 g = true) :
    dominatedB g = true ∧ LowerScopeT g ∧ Compile.storeTypedB g = true ∧
      Compile.selectTypedB g = true := by
  obtain ⟨hT, -, hsel⟩ := fnScopeInT2_parts h
  have p := fnScopeInT_parts hT
  exact ⟨p.2.2.2.2.2.2.2.2.2.2.1, lowerScopeT_of p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.1, hsel⟩

/-- **`resClassOkB` holds on `fnScopeInTB2`.** -/
theorem resClassOkB_of_T2 {g : Clif.Function} (h : fnScopeInTB2 g = true) :
    Spill.resClassOkB g = true :=
  let ⟨hdom, hs, hst, hsel⟩ := covParts_of_T2 h
  resClassOkB_of (Spill.resClassOk_of_lowerScopeT hdom hs hst hsel)

/-- **`formsCoveredB` holds on `fnScopeInTB2`**: of `prepare`'s output of `lowerFunction`'s
VCode, in every context. -/
theorem formsCoveredB_of_T2 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB2 g = true)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) (cx : FnCtx) :
    formsCoveredB cx vcp = true :=
  let ⟨hdom, hs, hst, hsel⟩ := covParts_of_T2 h
  Driver.formsCoveredB_completeT hdom hs hst hsel hl hp cx

end E2E.LinkCheck

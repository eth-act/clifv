import FV.E2E.TypedProductionChecks
import FV.E2E.SemanticStackBoundTSR

/-!
# `TypedProductionChecks` for `okRWithTSR` (#753, stage R4)

The typed Stock checker's crate proofs (`lake exe link-check --lean`, typed Stock candidate) at the
compiler's typed checks with the register-guarded calls `okRWithTSR` (suffix `R`): the per-slice
checks `fnsBProductionR` (`chksWithTSR`), `okRProductionR_of_checks`, and the crate statements
`CrateStmtProduction` (`crate_correct_productionR`, through `okRWithTSR_soundTR` and
`LinkSys.OkTR`'s `backend_correct_program_budgetTR`) and `StackStmtTS`
(`crate_correct_stackR`, through `crate_correct_stackNTSR`).
-/

namespace E2E.TypedProductionChecks
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.StackBound
set_option autoImplicit false
set_option Elab.async false
variable {lower : ProductionLowering}

/-- The per-function checks of `okRWithTSR` (`chksWithTSR`) of the functions `fs`, on the
results of the whole program. -/
def fnsBProductionR (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (fs : List FnInput) : Bool :=
  let R := I.resultsProductionWith lower cleanup
  fs.all fun fi => (chksWithTSR (productionStage cleanup) I (progOf R) (tabOf R) fi.func
    (I.pipeProductionWith lower cleanup fi)).all (·.2)

theorem fnsBProductionR_append (I : LinkInput) (cleanup : Bool) (a b : List FnInput) :
    fnsBProductionR lower I cleanup (a ++ b) =
      (fnsBProductionR lower I cleanup a && fnsBProductionR lower I cleanup b) := by
  simp only [fnsBProductionR,List.all_append]

theorem okRProductionR_of_checks {I : LinkInput} {cleanup : Bool}
    (hg : SemanticChecksWith.globalBProduction lower I cleanup = true)
    (hf : fnsBProductionR lower I cleanup I.funcs = true) :
    okRWithTSR (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true := by
  unfold okRWithTSR
  rw [Bool.and_eq_true]
  constructor
  · exact hg
  · simpa only [fnsBProductionR,LinkInput.resultsProductionWith,List.all_map,
      Function.comp_def] using hf

/-- **`crate_correct_production` under `okRWithTSR`**: the typed checks with the
register-guarded calls establish `LinkSys.OkTR` (`okRWithTSR_soundTR`), and
`backend_correct_program_budgetTR` at the budget `L.K` (`budget_KTR`) gives the crate statement. -/
theorem crate_correct_productionR (I : LinkInput) (cleanup : Bool)
    (hI : okRWithTSR (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true)
    (n : String) : CrateStmtProduction lower I cleanup n :=
  fun B F hB hF f hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    have hL := okRWithTSR_soundTR (productionStage cleanup) (productionStage_cases cleanup)
      (I.resultsProductionWith_prepared lower cleanup) hI hB hF
    backend_correct_program_budgetTR _ hL
      (κ := fun M _ => (ofRes I (I.resultsProductionWith lower cleanup) B F).K M)
      (LinkSys.budget_KTR _ hL) (Clif.Program.func?_some hf).1 M hent hres hFeq hgfree himg hbe
      hargs hcs hsav hrel hpl htr

/-- **`crate_correct_stack` under `okBTSR`** (`crate_correct_stackNTSR`). -/
theorem crate_correct_stackR {I : SemanticStackBound.CompilerInput}
    (hI : SemanticStackBound.okBTSR I = true) {S : Nat}
    (hS : SemanticStackBound.stackB I = some S) (n : String) :
    SemanticStackBound.StackStmtTS I n := by
  intro B F hB hFI f hf
  have hf' : (progOf I.results).func? n = some f := hf
  have hn : SemanticStackBound.goodN I n = true := by
    unfold SemanticStackBound.goodN
    rw [hf']
    exact (SemanticStackBound.stackB_some hS).1 f (Clif.Program.func?_some hf').1
  exact SemanticStackBound.crate_correct_stackNTSR hI hn B F hB hFI f hf

end E2E.TypedProductionChecks

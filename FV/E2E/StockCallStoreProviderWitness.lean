import FV.E2E.StockCallStoreCompiledWitness
import FV.Backend.Lowering.StockCallStoreWith
import FV.Backend.Lowering.StockLiveCallWith
import FV.Backend.Lowering.StockResultCallRoutes

namespace E2E.CallStoreProviderWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof CallStoreFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The complete landed call chain remains the supplied predecessor. -/
def previous := Stock.LiveCall.lowerWithPrevious Stock.ResultCall.lowerValidated

private def observed : Bool := previous caller |>.toOption.any (fun vc => !Stock.CallStore.check caller vc)
attribute [local irreducible] observed
-- witness: native_decide (the actual unchanged predecessor and original caller)
private theorem observed_true : observed = true := by native_decide

private theorem available {α : Type} {action : Except String α} {predicate : α → Bool}
    (positive : action.toOption.any predicate = true) : ∃ value,action = .ok value ∧ predicate value = true := by
  cases action with
  | error message => cases positive
  | ok value => exact ⟨value,rfl,positive⟩

/-- The new class selects its actual Stock code while its real predecessor also succeeds. -/
-- witness: native_decide (fixed original caller and complete previous chain)
theorem actual_provider (cleanup : Bool) :
    ∃ result old,Stock.lower caller = .ok result ∧ previous caller = .ok old ∧
      Stock.CallStore.lowerWithPrevious previous caller = .ok result.code ∧ result.code ≠ old ∧
      Stock.CallStore.ReturnStoreDomain caller result.code := by
  obtain ⟨result,lowered,checked⟩ := CallStoreCompiledWitness.checked_caller cleanup
  have chosen : Stock.CallStore.candidate caller = .ok result.code := by
    unfold Stock.CallStore.candidate Stock.CheckedWith.candidate
    rw [lowered]
    simp only [bind,Except.bind,checked,↓reduceIte,pure,Except.pure]
  have positive := observed_true
  unfold observed at positive
  obtain ⟨old,prior,rejected⟩ := available positive
  have rejects : Stock.CallStore.check caller old = false := by simpa using rejected
  refine ⟨result,old,lowered,prior,Stock.CallStore.lowerWithPrevious_selects chosen,?_,
    Stock.CallStore.check_return_store_domain checked⟩
  intro same
  rw [same,rejects] at checked
  cases checked

end E2E.CallStoreProviderWitness

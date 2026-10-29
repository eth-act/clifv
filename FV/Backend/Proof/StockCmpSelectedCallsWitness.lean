module

public import FV.Backend.Proof.StockCmpSelectedCalls
public import FV.Backend.Proof.StockCmpSourceMatchWitness

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 8000 in
/-- An actual named lower call from an accepted original sparse-ID function
inhabits canonical matching and every internally derived root helper call. -/
theorem stock_cmp_selected_calls_witness :
    ∃ f ctx st next out trace,∃ selected : LowerSelection ctx 0 st out next trace,
      MappedCtxInv f ctx ∧ selected.rule = rule_lower_2215 ∧ selected.env = cmpEnv .eq 7 31 ∧
      selected.matched = st ∧ selected.matchTrace = #[] ∧
      RootCalls program ctx .eq 7 31 st next #[] selected.rhsTrace out := by
  obtain ⟨out,next,trace,run,selected,id,inv,data,type⟩ := stock_cmp_original_selection_witness
  have actual := stock_cmp_selected_calls inv (cc := .eq) (ty := .i64) (i := 0) (x := 7) (y := 31)
    (by rfl) (by rfl) selected
  exact ⟨_,_,_,next,out,trace,selected,inv,actual.2⟩
end Backend.Stock.Proof.ScalarCmp

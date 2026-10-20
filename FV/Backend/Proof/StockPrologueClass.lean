import FV.Backend.Proof.StockPrologueCode

/-! Universal input-only selection facts for the SystemV i64 prologue class. -/
set_option autoImplicit false
namespace Backend.Stock.Prologue
open D0

theorem eligible_sound {f : Clif.Function} (h : eligible f = true) :
    ∃ name runs, f = source name .systemVI64 runs :=
  ⟨f.name, f.runs, of_decide_eq_true h⟩

theorem source_eligible (name : String) (runs : List Clif.RunCommand) :
    eligible (source name .systemVI64 runs) = true := by
  simp [eligible, source, D0.source]

theorem eligible_checked_output {f : Clif.Function} (h : eligible f = true) :
    (Stock.lower f).map (fun r => Backend.Proof.Driver.lowerCheck f (compact f.name r)) =
      .ok true := by
  obtain ⟨name, runs, rfl⟩ := eligible_sound h
  exact systemV_i64_checked_output name runs

theorem eligible_success_and_edges {f : Clif.Function} (h : eligible f = true) :
    (Stock.lower f).isOk = true ∧
    ((Stock.lower f).toOption.map
      (fun r => r.edgeArgs.all (fun row => row.all (·.isEmpty)))).getD false = true := by
  obtain ⟨name, runs, rfl⟩ := eligible_sound h
  have facts := systemV_i64_code_and_success name runs
  exact ⟨facts.1, facts.2.2⟩

end Backend.Stock.Prologue

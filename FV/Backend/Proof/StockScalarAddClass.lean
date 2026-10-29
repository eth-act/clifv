module

public import FV.Backend.Lowering.StockScalarProduction
public import FV.Backend.Proof.StockScalarAddChecked
public import FV.Backend.Proof.StockPrologueAllClass

@[expose] public section

set_option autoImplicit false
namespace Backend.Stock.ScalarAdd
open D0

theorem eligible_sound {f : Clif.Function} (h : eligible f = true) :
    ∃ c, c ∈ configurations ∧ f = source f.name c f.runs := by
  obtain ⟨c, hc, hf⟩ := List.any_eq_true.mp h
  exact ⟨c, hc, of_decide_eq_true hf⟩

theorem source_eligible (name : String) (runs : List Clif.RunCommand) (c : Configuration) :
    eligible (source name c runs) = true := by
  apply List.any_eq_true.mpr
  refine ⟨c, ?_, ?_⟩
  · cases c <;> simp [configurations]
  · simp [source, D0.source]

theorem eligible_success_and_edges {f : Clif.Function} (h : eligible f = true) :
    (Stock.lower f).isOk = true ∧
    ((Stock.lower f).toOption.map
      (fun r => r.edgeArgs.all (fun row => row.all (·.isEmpty)))).getD false = true := by
  obtain ⟨c, _, hf⟩ := eligible_sound h
  rw [hf]
  have facts := code_and_success f.name f.runs c
  exact ⟨facts.1, facts.2.2⟩

theorem eligible_output {f : Clif.Function} (h : eligible f = true) :
    lower f = (Stock.lower f).map (compact f.name) := by
  obtain ⟨success, edges⟩ := eligible_success_and_edges h
  cases run : Stock.lower f with
  | error e =>
    rw [run] at success
    change false = true at success
    cases success
  | ok r =>
    simp only [run, Except.toOption, Option.map, Option.getD] at edges
    simp [lower, lowerWith, h, run, edges, Except.map]

theorem eligible_checked_output {f : Clif.Function} (h : eligible f = true) :
    (lower f).map (Backend.Proof.Driver.lowerCheck f) = .ok true := by
  rw [eligible_output h]
  obtain ⟨c, _, hf⟩ := eligible_sound h
  have checked := checked_output f.name f.runs c
  rw [← hf] at checked
  cases run : Stock.lower f <;> simpa [run, Except.map] using checked

theorem outside_class (stock : Clif.Function → Except String Result) (f : Clif.Function)
    (h : eligible f = false) : lowerWith stock f = Prologue.AllConfigurations.lower f := by
  simp [lowerWith, h]

theorem failed_attempt (f : Clif.Function) (message : String) :
    lowerWith (fun _ => .error message) f = Prologue.AllConfigurations.lower f := by
  simp [lowerWith]

theorem d0_outside_class {f : Clif.Function} (h : D0.eligible f = true) :
    eligible f = false := by
  cases hp : eligible f with
  | false => rfl
  | true =>
    obtain ⟨c, _, hf⟩ := D0.eligible_sound h
    obtain ⟨c', _, hf'⟩ := eligible_sound hp
    have lengths := congrArg (fun g : Clif.Function => g.sig.params.length) (hf.symm.trans hf')
    simp [D0.source, source] at lengths

theorem preserves_d0 {f : Clif.Function} (h : D0.eligible f = true) :
    lower f = D0.defaultLower f := by
  rw [lower, outside_class _ _ (d0_outside_class h)]
  exact Prologue.AllConfigurations.preserves_d0 h

/-- Every previously enabled prologue remains on exactly its existing route. -/
theorem preserves_prologue {f : Clif.Function} (h : Prologue.AllConfigurations.eligible f = true) :
    lower f = Prologue.AllConfigurations.lower f := by
  have outside : eligible f = false := by
    cases hp : eligible f with
    | false => rfl
    | true =>
      obtain ⟨c,_,hf⟩ := eligible_sound hp
      obtain ⟨c',_,hf'⟩ := Prologue.AllConfigurations.eligible_sound h
      have lengths := congrArg (fun g : Clif.Function => g.sig.params.length) (hf.symm.trans hf')
      simp [source,Prologue.source,D0.source] at lengths
  exact outside_class _ _ outside

end Backend.Stock.ScalarAdd

module

public import FV.Backend.Lowering.StockProduction
public import FV.Backend.Proof.StockPrologueClass
public import FV.Backend.Proof.StockD0Code

@[expose] public section

set_option autoImplicit false
namespace Backend.Stock.Production

theorem outside_class (stock : Clif.Function → Except String Result) (f : Clif.Function)
    (h : Prologue.eligible f = false) : lowerWith stock f = D0.defaultLower f := by
  simp [lowerWith, h]

theorem failed_attempt (f : Clif.Function) (message : String) :
    lowerWith (fun _ => .error message) f = D0.defaultLower f := by
  simp [lowerWith]

theorem eligible_output {f : Clif.Function} (h : Prologue.eligible f = true) :
    lower f = (Stock.lower f).map (D0.compact f.name) := by
  obtain ⟨success, edges⟩ := Prologue.eligible_success_and_edges h
  cases run : Stock.lower f with
  | error e =>
    rw [run] at success
    change false = true at success
    cases success
  | ok r =>
    simp only [run, Except.toOption, Option.map, Option.getD] at edges
    simp [lower, lowerWith, h, run, edges, Except.map]

theorem eligible_checked_output {f : Clif.Function} (h : Prologue.eligible f = true) :
    (lower f).map (Backend.Proof.Driver.lowerCheck f) = .ok true := by
  rw [eligible_output h]
  have checked := Prologue.eligible_checked_output h
  cases run : Stock.lower f <;> simpa [run, Except.map] using checked

theorem d0_outside_class {f : Clif.Function} (h : D0.eligible f = true) :
    Prologue.eligible f = false := by
  cases hp : Prologue.eligible f with
  | false => rfl
  | true =>
    obtain ⟨c, _, hf⟩ := D0.eligible_sound h
    obtain ⟨name, runs, hf'⟩ := Prologue.eligible_sound hp
    have lengths := congrArg (fun g : Clif.Function => g.blocks.length) (hf.symm.trans hf')
    simp [D0.source, Prologue.source] at lengths

theorem preserves_d0 {f : Clif.Function} (h : D0.eligible f = true) :
    lower f = D0.defaultLower f := outside_class _ _ (d0_outside_class h)

end Backend.Stock.Production

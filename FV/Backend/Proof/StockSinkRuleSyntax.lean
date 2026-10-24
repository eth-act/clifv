import FV.Backend.Proof.StockTermIndex
import FV.Backend.Proof.StockRuleFrame
import FV.Backend.Proof.StockPatternSink

/-! Exhaustive syntax boundary for the actual generated program: four complete
matched-rule contracts cover every direct sink constructor call. -/
namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program

def blocked (term : Term) : Bool := term.id == TId.sink_inst

def Exceptional (rule : Rule) : Prop :=
  rule = rule_inst_3905 ∨ rule = rule_inst_4203 ∨
  rule = rule_lower_1300 ∨ rule = rule_lower_1359

private theorem lookup_id {t : TermId} {term : Term}
    (found : program.term? t = some term) : term.id = t := by
  have checked := congrArg (fun a : List Nat => a[t]?) stock_term_ids_checked
  change program.terms[t]? = some term at found
  simp only [List.getElem?_map, Array.getElem?_toList, found, Option.map_some, List.getElem?_range] at checked
  rw [List.getElem?_range (Array.getElem_of_getElem? found).1] at checked
  exact Option.some.inj checked

theorem term_guard (t : TermId) : termCtorFree program blocked t = (t != 236) := by
  cases found : program.term? t with
  | none =>
    have different : t ≠ 236 := by
      intro same
      subst t
      have installed := data_program.t236
      unfold termOf at installed
      rw [found] at installed
      cases installed
    simp [termCtorFree, found, different]
  | some term =>
    have id := lookup_id found
    simp only [termCtorFree, found, blocked, TId.sink_inst]
    rw [id]
    rfl

instance (rule : Rule) : Decidable (Exceptional rule) := by
  unfold Exceptional
  infer_instance

def safeRule (rule : Rule) : Bool :=
  rule.iflets.all (fun il => exprTermFree (fun t => t != 236) il.rhs) &&
    (exprTermFree (fun t => t != 236) rule.rhs || ((rule.id == 344 || rule.id == 385 || rule.id == 815 || rule.id == 824) &&
      decide (Exceptional rule)))

/-- Exhaustive kernel check of direct sink sites, using a separately checked
term-index map so the large generated term records are not reduced at each call. -/
theorem table_checked : program.ruleLists.toList.flatten.all safeRule = true := by
  decide +kernel

/-- Every actual selected rule has sink-free matching expressions and either a
sink-free RHS or one of the four explicitly identified full-rule contracts. -/
theorem rule_cases {t : TermId} {rule : Rule} (member : rule ∈ program.rulesOf t) :
    ifletsCtorFree program blocked rule.iflets = true ∧
      (exprCtorFree program blocked rule.rhs = true ∨ Exceptional rule) := by
  have present : rule ∈ program.ruleLists.toList.flatten := by
    unfold Program.rulesOf at member
    cases lookup : program.ruleLists[t]? with
    | none => simp [lookup] at member
    | some rules =>
      exact List.mem_flatten.mpr ⟨rules,
        Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup),by simpa [lookup] using member⟩
  have checked := (List.all_eq_true.mp table_checked) rule present
  have guards : termCtorFree program blocked = (fun t => t != 236) := funext term_guard
  simp only [safeRule, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at checked
  refine ⟨?_, ?_⟩
  · simpa only [ifletsCtorFree, exprCtorFree, guards] using checked.1
  · rcases checked.2 with free | special
    · exact Or.inl (by simpa only [exprCtorFree, guards] using free)
    · exact Or.inr special.2

end Backend.Stock.Proof.SinkRules

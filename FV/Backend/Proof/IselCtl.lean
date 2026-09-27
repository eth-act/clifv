import FV.Backend.Proof.IselCtlTerm
import FV.Backend.Proof.IselCtlUnmatch

/-!
# Family Ctl: the terminator/branch/call statements for the exported program

Assembly of the per-rule theorems into M4's statements: `lowerTermRulesCorrect`
(`LowerTermRulesCorrect program`), with `termUnmatchable`, `branchExcludedUnmatchable`
(`IselCtlUnmatch`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000

/-- In a list whose rule ids are distinct, a rule is determined by its id. -/
theorem eq_of_mem_of_id {r r0 : Rule} :
    ∀ {L : List Rule}, (L.map Rule.id).Nodup → r ∈ L → r0 ∈ L → r.id = r0.id → r = r0
  | [], _, hr, _, _ => by cases hr
  | a :: L, hnd, hr, hr0, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp hr with h1 | h1 <;> rcases List.mem_cons.mp hr0 with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd h.symm (fun e => hnd.1 r0 h2 e)
    · subst h2; exact absurd h (fun e => hnd.1 r h1 e)
    · exact eq_of_mem_of_id hnd.2 h1 h2 h

theorem lower_ids_nodup : ((program.rulesOf TId.lower).map Rule.id).Nodup := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

theorem lower_branch_ids_nodup : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  decide +kernel

theorem mem_lower_2237 : rule_lower_2237 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨305, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

theorem mem_lower_2574 : rule_lower_2574 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨346, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

/-- **`LowerTermRulesCorrect`**: the `trap` and `return` rules of `lower` are correct. -/
theorem lowerTermRulesCorrect : LowerTermRulesCorrect program := by
  intro F isem MR hR hMR r hr hroot
  simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  rcases hroot with h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [h]; rfl)]
    exact trap_ruleOk data_program hR
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [h]; rfl)]
    exact ret_ruleOk data_program hR hMR

end Backend.Proof

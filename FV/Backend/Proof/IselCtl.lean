import FV.Backend.Proof.IselCtlTerm
import FV.Backend.Proof.IselCtlUnmatch
import FV.Backend.Proof.IselCtlCallInd
import FV.Backend.Proof.IselCtlBranch
import FV.Backend.Proof.IselCtlBrif
import FV.Backend.Proof.IselCtlTbz
import FV.Backend.Proof.IselCtlBrTable

/-!
# Family Ctl: the terminator/branch/call statements for the exported program

Assembly of the per-rule theorems into M4's statements: `lowerTermRulesCorrect`
(`LowerTermRulesCorrect program`), with `termUnmatchable`, `branchExcludedUnmatchable`
(`IselCtlUnmatch`), `callRulesCorrect` (`CallRulesCorrect program`, `IselCtlCallRules`),
`branchRulesCorrect` (`BranchRulesCorrect program`: `brif` 1132, `tbnz` 1137, `tbz` 1138, `jump`
1139, `br_table` 1140).
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

theorem mem_lower_2508 : rule_lower_2508 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨161, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

theorem mem_lower_2518 : rule_lower_2518 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨344, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

/-- **`CallRulesCorrect`**: under the callee contract, the `call` rules of `lower` (`bl`, rule id
1031; GOT + `blr`, rule id 1032) are correct. -/
theorem callRulesCorrect : CallRulesCorrect program := by
  intro F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot
  simp only [callRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  rcases hroot with h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [h]; rfl)]
    exact call_bl_ruleOk data_program hR hMR hMem hout hCR
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [h]; rfl)]
    exact call_got_ruleOk data_program hR hMR hMem hout hCR

theorem mem_lower_2529 : rule_lower_2529 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨345, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

/-- **`IndRulesCorrect`**: under the indirect-call contract, the `call_indirect` rule of `lower`
(`blr` of the callee value, rule id 1033) is correct. -/
theorem indRulesCorrect : IndRulesCorrect program := by
  intro F isem MR env cp sigs hR hMR hCR r hr hroot
  simp only [indRootRule, beq_iff_eq] at hroot
  rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2529 (by rw [hroot]; rfl)]
  exact call_ind_ruleOk data_program indData_program hR hMR hCR

/-- **`BranchRulesCorrect`**: the closure root rules of `lower_branch` — `brif` (1132), `tbnz`
(1137), `tbz` (1138), `jump` (1139), `br_table` (1140) — are correct; the `try_call` rules are
not closure roots. -/
theorem branchRulesCorrect : BranchRulesCorrect program := by
  intro F isem MR hR hMR r hr hroot
  rw [show TId.lower_branch = 687 from rfl, data_program.r687] at hr
  simp only [R.lower_branch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hroot (by decide +kernel)
  · exact tbnz_ruleOk data_program hR hMR
  · exact tbz_ruleOk data_program hR hMR
  · exact absurd hroot (by decide +kernel)
  · exact absurd hroot (by decide +kernel)
  · exact brif_ruleOk data_program hR hMR
  · exact jump_ruleOk data_program hR hMR
  · exact brTable_ruleOk data_program hR hMR

end Backend.Proof

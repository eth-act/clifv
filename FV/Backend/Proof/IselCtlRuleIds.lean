import FV.Backend.Proof.IselData

/-!
# The rule lists of `lower`: ids are distinct, and the terminator/call rules are members

Facts about the exported program's `lower`/`lower_branch` rule lists that the Ctl family
(`IselCtl`) and the coverage/call proofs use. Their own module, so that those proofs need not wait
for the whole Ctl family.
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

theorem mem_lower_2508 : rule_lower_2508 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨161, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

theorem mem_lower_2518 : rule_lower_2518 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨344, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

theorem mem_lower_2529 : rule_lower_2529 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨345, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

end Backend.Proof

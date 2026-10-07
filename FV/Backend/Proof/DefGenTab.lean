import FV.Backend.Proof.DefGenSound
import FV.Backend.Proof.KillTab

/-!
# Definedness of the ISLE runs: the decided rule tables

The terms whose runs the abstract interpreter describes are `defT` (membership in `defTab`, the
closure under `Isle.ruleTerms` of the root rules' terms and the oracles, not descending into the
oracles and the constructor-tree terms). Decided over the exported rule data (`native_decide`):

* `tabOK`: every rule of every non-oracle, non-wrapper term of `defTab` applies terms of
  `defTab` and checks (`aRule`) with both summaries of its term;
* `rootLower`, `rootBranch`: every root rule of `lower` (but `nop`'s 587 and the I128 rules 636,
  637, see `Kill.nop_rhs`, `Kill.lower_636_637_nomatch`) and of `lower_branch` applies terms of
  `defTab` and checks with the root summary (the instruction is the root, results are clean).
-/

namespace Backend.Proof.DefGen

open Backend Isle Isle.Aarch64

set_option maxRecDepth 100000

/-- **The terms whose runs are described**: membership in `defTab`. -/
def defT (t : TermId) : Prop := t ∈ defTab

/-- The rules of term `t` apply terms of `defTab` and check with both summaries. -/
def termOkB (t : TermId) : Bool :=
  oracles.contains t || (wrapper program t).isSome ||
    match program.term? t with
    | some term => (program.rulesOf t).all fun rl =>
        (ruleTerms rl).all (defTab.contains ·) &&
        aRule program (term.args.map (tyA false)) (tyA false term.ret) rl &&
        aRule program (term.args.map (tyA true)) (tyA (zp.contains t) term.ret) rl
    | none => true

theorem defTab_termOk : defTab.all termOkB = true := by native_decide

/-- **The rules of `defTab` check.** -/
theorem tabOK : TabOK program defT := by
  intro t ht ho hw term hterm rl hrl
  have h := List.all_eq_true.mp defTab_termOk t ht
  have ho' : oracles.contains t = false := by simpa using ho
  rw [termOkB, ho', hw, Kill.termOf_program_eq hterm] at h
  simp only [Option.isSome_none, Bool.or_false, Bool.false_or, List.all_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h rl hrl
  exact ⟨fun u hu => by simpa [defT] using h1 u hu, h2, h3⟩

theorem oracles_ok : oracles.all (defTab.contains ·) = true := by native_decide

/-- The oracles are in `defT`. -/
theorem oracles_defT : ∀ t ∈ oracles, defT t := by
  intro t ht
  simpa [defT] using List.all_eq_true.mp oracles_ok t ht

theorem rootLower_ok : (program.rulesOf TId.lower).all (fun rl => defExcl.contains rl.id ||
    ((ruleTerms rl).all (defTab.contains ·) &&
      aRule program [.cl true false] (.cl false false) rl)) = true := by native_decide

theorem rootBranch_ok : (program.rulesOf TId.lower_branch).all (fun rl =>
    (ruleTerms rl).all (defTab.contains ·) &&
      aRule program [.cl true false, .cl false false] (.cl false false) rl) = true := by
  native_decide

/-- **The statement root rules** (but `nop`'s 587 and the I128 rules 636, 637) apply terms of
`defT` and check with the root summary (`lower : Inst → InstOutput`). -/
theorem rootLower : ∀ rl ∈ program.rulesOf TId.lower, rl.id ≠ 587 → rl.id ≠ 636 → rl.id ≠ 637 →
    (∀ u ∈ ruleTerms rl, defT u) ∧
      aRule program [.cl true false] (.cl false false) rl = true := by
  intro rl hrl h1 h2 h3
  have h := List.all_eq_true.mp rootLower_ok rl hrl
  have hx : defExcl.contains rl.id = false := by simp [defExcl, h1, h2, h3]
  rw [hx, Bool.false_or] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun u hu => by simpa [defT] using h.1 u hu, h.2⟩

/-- **The branch root rules** apply terms of `defT` and check with the root summary
(`lower_branch : Inst → MachLabelSlice → Unit`). -/
theorem rootBranch : ∀ rl ∈ program.rulesOf TId.lower_branch,
    (∀ u ∈ ruleTerms rl, defT u) ∧
      aRule program [.cl true false, .cl false false] (.cl false false) rl = true := by
  intro rl hrl
  have h := List.all_eq_true.mp rootBranch_ok rl hrl
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun u hu => by simpa [defT] using h.1 u hu, h.2⟩

end Backend.Proof.DefGen

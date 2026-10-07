import FV.E2E.LinkScope
import FV.E2E.SpillKillFree
import FV.Backend.Proof.SpillDefinedPrep
import FV.Backend.Proof.SpillEdgesLow

/-!
# `SpillDefinedHypE` from definite assignment of `lowerFunction`'s VCode

`SpillDefinedHypE` (`FV/E2E/SpillCheckAlloc.lean`; `SpillDefinedHyp` with the input condition
`entryParamsB`, without which it is false: `not_spillDefinedHyp`) asks for availability sets of
the prepared VCode that hold nothing on entry. Availability is proven (`spillAvailable_of_killFree
spillKillFree`: no use reads a vreg an instruction kills without storing it), so what remains is
definedness alone: `LowerDefinedHyp`, definedness sets (`Spill.DefAvail`: every use defined on
every path from the entry, a parameter defined iff its branch argument is) of `lowerFunction`'s
VCode with nothing defined on entry. `prepare` keeps them (`Spill.defAvail_prepare`), and the
conjunction of availability and definedness sets is availability sets (`Spill.spillAvail_and`):
`spillDefinedHypE_of_lower`. `crate_correct_inScope_lower` is `crate_correct_inScopeE` under
`LowerDefinedHyp`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Definite assignment of `lowerFunction`'s VCode** (the remaining hypothesis of
`crate_correct_inScope_lower`): on in-scope input whose entry block has the signature's
parameters, the VCode has definedness sets (`Spill.DefAvail`) in which nothing is defined on
entry to the function. -/
def LowerDefinedHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc : VCode), InSubset p f → Spill.ArityOk f →
    Dominated f → LowerScope f → Spill.entryParamsB f = true → lowerFunction f = .ok vc →
      ∃ M, Spill.DefAvail vc M ∧ ∀ v, M 0 v = false

/-- **`SpillDefinedHypE` from definite assignment of `lowerFunction`'s VCode.** -/
theorem spillDefinedHypE_of_lower (h : LowerDefinedHyp) : SpillDefinedHypE :=
  fun p f vc vcp hsub har hd hs hen hl hp => by
    obtain ⟨K, hK⟩ := spillAvailable_of_killFree spillKillFree p f vc vcp hsub har hd hs hl hp
    obtain ⟨M, hM, h0⟩ := h p f vc hsub har hd hs hen hl
    obtain ⟨M', hM', h0'⟩ := Spill.defAvail_prepare (Spill.lowOk_of hd hs har hl) hp hM h0
    exact Spill.spillAvail_defined hK hM' h0'

/-- **Non-vacuity of `spillAvail_and`**: on a VCode with a block argument, availability sets and
definedness sets holding nothing on entry exist together. -/
theorem spillAvail_defined_witness : ∃ vc K M, Spill.SpillAvail vc K ∧ Spill.DefAvail vc M ∧
    (∀ v, M 0 v = false) ∧ ∃ vb ∈ vc.blocks.toList, vb.branchArgs ≠ #[] :=
  ⟨Spill.step4Ex, _, fun _ _ => false, Spill.step4Ex_avail,
    ⟨fun succs preds h b vb k i ops hb hi hops o ho _ => by
      match b, hb with
      | 0, hb =>
        cases hb
        match k, hi with
        | 0, hi => cases hi; cases hops; simp at ho
      | 1, hb =>
        cases hb
        match k, hi with
        | 0, hi => cases hi; cases hops; simp at ho,
     fun _ _ _ _ _ _ _ _ _ _ _ _ _ hv => by cases hv⟩,
    fun _ => rfl, ⟨_, List.mem_cons_self, by decide⟩⟩

end E2E

namespace E2E.LinkCheck

open Backend Backend.Proof

/-- **`crate_correct_inScopeE` under definite assignment of `lowerFunction`'s VCode**
(`LowerDefinedHyp`, which gives `SpillDefinedHypE`: `spillDefinedHypE_of_lower`). -/
theorem crate_correct_inScope_lower (hM : LowerDefinedHyp) {I : LinkInput}
    (hin : InScopeP I = true) (hen : I.prog.funcs.all Spill.entryParamsB = true)
    (hlk : linkerOkB I = true) (n : String) : CrateStmtT I n :=
  crate_correct_inScopeE (spillDefinedHypE_of_lower hM) hin hen hlk n

end E2E.LinkCheck

import FV.Link.UnwTryIn
import FV.Link.UnwFnsCompleteWitness

/-!
# Witness: the `try_call` handlers from the input (S10g, #404)

On `E2E.DeadCleanupUnwindWitness`'s `try_call` function `tc` (`source`: one `tag0` handler):
its input conditions hold (`native_decide` on `dominatedB`, `lowerScopeB`, `arityOkB`,
`tryTablesB`, `extendsWidenB`), so `tryInfoOk_of_input`, `fwd_ne_entry_input`,
`alias_ne_entry`, `padsNonzero_complete_of`, `callSites_complete_input` and
`padsNonzero_complete_input` apply to its compiled code.
-/

namespace Link.EhCheck.Complete.Witness

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.DeadCleanupUnwindWitness

/-- The input conditions of `source`, decided. -/
def inputs : Bool :=
  dominatedB source && lowerScopeB source && Spill.arityOkB source && tryTablesB source &&
    (rf.blocks.size == vcp.blocks.size)

set_option maxRecDepth 100000 in
theorem inputs_true : inputs = true := by native_decide

theorem inputs_facts :
    Dominated source ∧ LowerScope source ∧ Spill.ArityOk source ∧ tryTablesB source = true ∧
      rf.blocks.size = vcp.blocks.size := by
  have h := inputs_true
  simp only [inputs, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨dominated_of h1, lowerScope_of h2, Spill.arityOk_of h3, h4, h5⟩

theorem pipe : lowerFunction source = .ok vc ∧ Backend.prepare (DeadCleanup.prune vc) = .ok vcp := by
  obtain ⟨-, -, -, ⟨hl, -, hp, -, -, -, -, -⟩, -⟩ := facts
  exact ⟨hl, hp⟩

/-- `source`'s extensions widen (`extendsWidenB`, part of every input scope), decided. -/
theorem widen_true : extendsWidenB source = true := by native_decide

/-- **`tryInfoOk_of_input` applies** to `source`. -/
theorem tryInfoOk_applies : TryInfoOk vcp :=
  tryInfoOk_of_input inputs_facts.1 inputs_facts.2.1 inputs_facts.2.2.1 inputs_facts.2.2.2.1
    pipe.1 pipe.2

/-- **`fwd_ne_entry_input` applies** to `source`: no block of its allocated code forwards to
the entry block. -/
theorem fwd_applies : ∀ s x, af.fwd? s = some x → x ≠ vb0.label :=
  fwd_ne_entry_input inputs_facts.2.1 widen_true pipe.1 pipe.2 compiled.1 premises_facts.1

/-- **`alias_ne_entry` applies** to `source`'s emitted code. -/
theorem aliasNoEntry_applies : ∀ q ∈ fa.alias, q.1 ≠ vb0.label → q.2 ≠ vb0.label :=
  alias_ne_entry compiled.1 compiled.2.1 premises_facts.1 premises_facts.2.1 fwd_applies

/-- **`padsNonzero_complete_of` applies** to `source`'s emitted code. -/
theorem padsNonzero_of_applies : padsNonzeroB af fa = true :=
  padsNonzero_complete_of compiled.1 compiled.2.1 compiled.2.2 premises_facts.1
    premises_facts.2.1 premises_facts.2.2.2.1 aliasNoEntry_applies

/-- **`callSites_complete_input` and `padsNonzero_complete_input` apply** to `source`. -/
theorem input_applies : (∃ l, callSites af fa = .ok l) ∧ padsNonzeroB af fa = true :=
  ⟨callSites_complete_input inputs_facts.1 inputs_facts.2.1 inputs_facts.2.2.1
      inputs_facts.2.2.2.1 pipe.1 pipe.2 compiled.1 inputs_facts.2.2.2.2 compiled.2.1,
    padsNonzero_complete_input inputs_facts.1 inputs_facts.2.1 inputs_facts.2.2.1
      inputs_facts.2.2.2.1 pipe.1 pipe.2 compiled.1 compiled.2.1 compiled.2.2 premises_facts.1
      premises_facts.2.1 widen_true⟩

end Link.EhCheck.Complete.Witness

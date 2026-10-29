module

public import FV.Link.UnwCheckIn
public import FV.Link.UnwTryInWitness

@[expose] public section

/-!
# Witness: the exceptional-edge validator from the input (S10g, #404)

On `E2E.DeadCleanupUnwindWitness`'s `try_call` function `tc` (`source`: one `tag0` handler, a
signature with one return): its input conditions hold (`UnwTryInWitness.inputs_facts` and
`tryRetsB` by `native_decide`), so `unwCheck_complete` applies to its lowering.
-/

namespace Link.EhCheck.Complete.Witness

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.DeadCleanupUnwindWitness

theorem tryRets_source : tryRetsB source = true := by native_decide

/-- `source` has a `try_call`: `unwCheck` has an exceptional edge to check. -/
theorem source_hasTry : (source.blocks.any fun B => B.term.isTry) = true := by native_decide

/-- **`unwCheck_complete` applies** to `source`. -/
theorem unwCheck_applies : unwCheck source vc = true :=
  unwCheck_complete inputs_facts.1 inputs_facts.2.1 inputs_facts.2.2.2.1 tryRets_source pipe.1

end Link.EhCheck.Complete.Witness

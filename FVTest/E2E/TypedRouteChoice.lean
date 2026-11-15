import FV.E2E.ProductionPipelineWith
import FV.Backend.Lowering.StockVoidCallNI
import FV.E2E.SemanticPipelineCheckT

/-! # The typed Stock checker's route for one function (#1040)

`link-check` does not know which Stock route the compiler took per function: it recovers it
from the executable's bytes, probing the ABI-aware routes (`sret` copy, void call) first and
accepting an artifact that passes either the integer return-pin validator
(`SemanticABI.checkCalls`) or the typed one (`lowerOkTSB`). Where two routes give the same
bytes but different VCode (an `sret` copy: the Stock sret-copy route and `lowerFunction`), it
picks the Stock artifact, which the typed Stock checker `okRWithTS` rejects (`lowerOkTSB` admits
the Stock artifact only without `sret` parameter), although the compiler's typed route
`Link.SemanticCompilerWith.attemptT` lowered that function with `lowerFunction` and was accepted.

`typedRoute?` is the route `link-check` uses for such a function when it takes the typed Stock
checker: the first route of `Stock.VoidCall.NI.lowerRoutes`, in the compiler's order, whose
artifact passes the allocation checker, `prepCheck`, `lowerOkTSB` and `same` (in `link-check`:
the executable's bytes, `artB`). Untrusted route selection: the theorem the proof files state is
about the results of the route list chosen, whatever it is. -/

namespace E2E.LinkCheck
open Backend Backend.Proof.Driver

/-- **The typed Stock checker's route for `fi`** (#1040): the index in
`Stock.VoidCall.NI.lowerRoutes` of the first route whose artifact passes `checkAlloc`,
`prepCheck`, `lowerOkTSB` and `same`. -/
def typedRoute? (I : LinkInput) (cleanup : Bool) (same : Art → Bool) (fi : FnInput) :
    Option Nat :=
  (Stock.VoidCall.NI.lowerRoutes.zipIdx.find? fun (lower, _) =>
    match I.pipeOfWithLowering lower (productionStage cleanup) fi with
    | .error _ => false
    | .ok a => (checkAlloc a.vcp a.rf).toBool &&
        prepCheck (productionStage cleanup fi.func a.vc) a.vcp &&
        lowerOkTSB fi.func a.vc && same a).map (·.2)

end E2E.LinkCheck

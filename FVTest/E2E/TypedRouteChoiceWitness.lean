import FV.E2E.PreparedReturnPinSretWitness
import FV.E2E.TypedProductionChecks
import FVTest.E2E.TypedRouteChoice

/-! # Witness of #1040: the typed Stock checker's route for an `sret` copy

The shape of #1040 on the captured `sret` copy of `PreparedReturnPinSretWitness` (fv-demo's
`black_box`-shaped 16-byte copy, `_RNxC7fv_demo11HawPMC3YC2b`): the Stock sret-copy route
(`stockRoute`, the route `link-check` probes first for such a function since #892) and route 0
(`lowerFunction`'s VCode) emit the same machine words from different VCode. The integer return-pin
checker accepts the Stock route's results, the typed Stock checker `okRWithTS` (used when float
functions are in the program, as in the `--build-std` bundle) rejects them on exactly the lowering
check (`lowerOkTSB`), and `typedRoute?` with "same bytes" picks route 0, whose results
`okRWithTS` accepts; the typed crate statement then holds of them. Evaluated with `native_decide`
on the two fixed pipelines (a witness, not a compiler theorem). -/

namespace E2E.TypedRouteChoiceWitness
open Backend Backend.Proof.Driver LinkCheck

/-- The captured `sret` copy's input (`PreparedReturnPinSretWitness.input`). -/
def input : LinkInput := PreparedReturnPinSretWitness.input

/-- Its only function. -/
def fi : FnInput := input.funcs[0]!

/-- The last route of `Stock.VoidCall.NI.lowerRoutes` (the void-call route, which falls back to
the Stock sret-copy route): the first route `link-check`'s recovery probes for an `sret` copy. -/
def stockRoute : Nat := 22

/-- The artifact of route `idx` of `Stock.VoidCall.NI.lowerRoutes`. -/
def art (cleanup : Bool) (idx : Nat) : Art :=
  getOk (input.pipeOfWithLowering (Stock.VoidCall.NI.lowerRoutes[idx]!) (productionStage cleanup) fi)

/-- The results of the compiler pipeline with `fi` on route `idx`. -/
def results (cleanup : Bool) (idx : Nat) : Res :=
  input.resultsProductionWith (Stock.VoidCall.NI.lowerWithRoutes [(fi.func.name, idx)]) cleanup

/-- **Two routes, the same machine words, different VCode**: the Stock sret-copy route's artifact
passes the integer ABI-aware validator and the Stock sret-copy check, not `SemanticNI.check`
(its return mode is the Stock ABI one) and not the typed lowering check `lowerOkTSB`; route 0's is
`lowerFunction`'s output. -/
theorem same_bytes (cleanup : Bool) :
    (art cleanup stockRoute).fb.words = (art cleanup 0).fb.words ∧
      (art cleanup stockRoute).vc ≠ (art cleanup 0).vc ∧
      SemanticABI.checkCalls fi.func (art cleanup stockRoute).vc = true ∧
      Stock.MemorySretCopy.check fi.func (art cleanup stockRoute).vc = true ∧
      SemanticNI.check fi.func (art cleanup stockRoute).vc = false ∧
      lowerOkTSB fi.func (art cleanup stockRoute).vc = false ∧
      lowersToB fi.func (art cleanup 0).vc = true := by
  cases cleanup <;> native_decide

/-- **The binary check's failure of #1040**: the integer return-pin checker accepts the results
on the Stock sret-copy route, the typed Stock checker rejects them. -/
theorem stock_route_typed_rejected (cleanup : Bool) :
    okRReturnPins (productionStage cleanup) input (results cleanup stockRoute) = true ∧
      okRWithTS (productionStage cleanup) input (results cleanup stockRoute) = false := by
  cases cleanup <;> native_decide

/-- **The typed route with the same bytes** (`typedRoute?`, `link-check`'s choice for the typed
Stock checker): route 0, whose results the typed Stock checker accepts. -/
theorem typed_route (cleanup : Bool) :
    typedRoute? input cleanup (fun a => a.fb.words == (art cleanup stockRoute).fb.words) fi =
        some 0 ∧
      okRWithTS (productionStage cleanup) input (results cleanup 0) = true := by
  cases cleanup <;> native_decide

/-- The typed crate statement (`TypedProductionChecks.CrateStmtProduction`, the statement of the
typed Stock checker's proof files) holds of the re-routed results. -/
theorem crate_correct (cleanup : Bool) :
    TypedProductionChecks.CrateStmtProduction
      (Stock.VoidCall.NI.lowerWithRoutes [(fi.func.name, 0)]) input cleanup fi.func.name :=
  TypedProductionChecks.crate_correct_production input cleanup (typed_route cleanup).2 _

end E2E.TypedRouteChoiceWitness

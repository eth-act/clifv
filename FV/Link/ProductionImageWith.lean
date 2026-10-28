import FV.Link.ProductionImage
import FV.E2E.ProductionPipelineWith

/-! Lowerer-parametric placement and byte writing. The retained entrypoints are
exact specializations, so adding a class does not require a new machine model. -/
set_option autoImplicit false
namespace Link
open Backend E2E E2E.LinkCheck

def parResultsProductionWith (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) : Res :=
  parMap (fun fi => (fi.func, I.pipeProductionWith lower cleanup fi)) I.funcs

theorem parResultsProductionWith_eq (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) :
    parResultsProductionWith lower I cleanup = I.resultsProductionWith lower cleanup := by
  simp only [parResultsProductionWith, parMap_eq, LinkInput.resultsProductionWith]

def LinkSpec.inputProductionWith (S : LinkSpec) (lower : ProductionLowering) (cleanup : Bool) : LinkInput :=
  S.input0.withDepth (S.input0.resultsProductionWith lower cleanup)

theorem LinkSpec.inputProductionWith_results (S : LinkSpec) (lower : ProductionLowering) (cleanup : Bool) :
    (S.inputProductionWith lower cleanup).resultsProductionWith lower cleanup =
      S.input0.resultsProductionWith lower cleanup := rfl

def leanLinkProductionWith (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray)
    (cleanup : Bool) : Except String ByteArray :=
  leanLinkWithResults S file0 (fun I => parResultsProductionWith lower I cleanup)

/-- `I` is bound outside the map so the compiled code builds `S.input0` once (#683). -/
def LinkSpec.placedProductionWith (S : LinkSpec) (lower : ProductionLowering) (cleanup : Bool) : LinkSpec :=
  let I : LinkInput := {S.input0 with addrs := []}
  S.withSizes (S.funcs.map fun fi =>
    (getOk (I.pipeProductionWith lower cleanup fi)).fb.words.size)

theorem LinkSpec.inputProductionWith_original (S : LinkSpec) (cleanup : Bool) :
    S.inputProductionWith Stock.Production.lower cleanup = S.inputProduction cleanup := rfl

theorem leanLinkProductionWith_original (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) :
    leanLinkProductionWith Stock.Production.lower S file0 cleanup = leanLinkProduction S file0 cleanup := rfl

theorem LinkSpec.placedProductionWith_original (S : LinkSpec) (cleanup : Bool) :
    S.placedProductionWith Stock.Production.lower cleanup = S.placedProduction cleanup := rfl
end Link

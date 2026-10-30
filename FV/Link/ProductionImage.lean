import FV.Link.ActualImage
import FV.Link.ExeInput
import FV.E2E.ProductionPipeline

/-! The actual transactional result table drives placement, stack depth and
all bytes written by the existing checked image writer. -/
set_option autoImplicit false
namespace Link
open Backend E2E E2E.LinkCheck

def parResultsProduction (I : LinkInput) (cleanup : Bool) : Res :=
  parMap (fun fi => (fi.func, I.pipeProduction cleanup fi)) I.funcs

theorem parResultsProduction_eq (I : LinkInput) (cleanup : Bool) :
    parResultsProduction I cleanup = I.resultsProduction cleanup := by
  simp only [parResultsProduction, parMap_eq, LinkInput.resultsProduction]

def LinkSpec.inputProduction (S : LinkSpec) (cleanup : Bool) : LinkInput :=
  S.input0.withDepth (S.input0.resultsProduction cleanup)

theorem LinkSpec.inputProduction_results (S : LinkSpec) (cleanup : Bool) :
    (S.inputProduction cleanup).resultsProduction cleanup = S.input0.resultsProduction cleanup := rfl

def leanLinkProduction (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  leanLinkWithResults S file0 (fun I => parResultsProduction I cleanup)

/-- `I` is bound outside the map so the compiled code builds `S.input0` (an
O(symbols × addrs) lookup) once, not once per function (#683). -/
def LinkSpec.placedProduction (S : LinkSpec) (cleanup : Bool) : LinkSpec :=
  let I : LinkInput := {S.input0 with addrs := []}
  S.withSizes (S.funcs.map fun fi =>
    (getOk (I.pipeProduction cleanup fi)).fb.words.size)
end Link

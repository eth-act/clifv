import FV.Backend.Proof.StockReturnStaticSource
import FV.Backend.Proof.StockClassesWitness
namespace Backend.Stock.Proof.ReturnStaticFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
structure Output where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc

def pipeline (implicit : Bool) : Except String Output := do
  let result ← Stock.lower (function implicit)
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force complete Stock return-static fallback")
  let af ← lowerRFunc prepared.code rf
  pure ⟨result,prepared,rf,af⟩
def Observed (implicit : Bool) : Prop := (pipeline implicit).toOption.map (fun out => decide
  (out.result.code.blocks[0]!.insts.back? = some (expected implicit) ∧
   out.prepared.code.blocks[0]!.insts.back? = some (expected implicit))) = some true
/-- Both real ordinary and implicit x8 return sources pass all actual raw,
global-checked fallback and physical stages with their exact final return. -/
theorem observed (implicit : Bool) : Observed implicit := by
  cases implicit <;> unfold Observed pipeline <;> decide +kernel
end Backend.Stock.Proof.ReturnStaticFixture

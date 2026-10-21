import FV.Backend.Proof.StockWholeFormSource
namespace Backend.Stock.Proof.Coverage.WholeFormsFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
structure Data where
  result : Backend.Stock.Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc

def pipeline : Except String Data := do
  let result ← Stock.lower entryFunction
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force whole-form witness fallback")
  let af ← lowerRFunc prepared.code rf
  pure ⟨result,prepared,rf,af⟩

def Observed : Prop := pipeline.toOption.map (fun q => q.result.code.blocks[0]?.map
  (fun block => block.insts.any isArgs && block.insts.any isFrameLoad)) = some (some true)

theorem observed : Observed := by
  unfold Observed pipeline
  decide +kernel


end Backend.Stock.Proof.Coverage.WholeFormsFixture

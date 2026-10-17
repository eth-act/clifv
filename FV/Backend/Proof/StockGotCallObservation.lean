import FV.Backend.Proof.StockGotCallSource
namespace Backend.Stock.Proof.GotCallFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open CallStaticFixture (arguments)
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

structure Output where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
def pipeline (implicit : Bool) : Except String Output := do
  let result ← Stock.lower (function implicit)
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force complete GOT-call checked fallback")
  let af ← lowerRFunc prepared.code rf
  pure ⟨result,prepared,rf,af⟩
def isGot : MInst → Bool | .loadExtNameGot _ _ => true | _ => false
def isCall : MInst → Bool | .call _ => true | _ => false
def callRecord (implicit : Bool) (event : BlockScanEvent) (record : ScanRecord) : Bool :=
  match event.ctx.insts[record.inst]?,record.output.step with
  | some info,some step => info.clif == some (.call 0 (arguments false implicit)) && step.decision == .emitted
  | _,_ => false
def Facts (implicit : Bool) (out : Output) : Prop :=
  out.result.code.blocks.any (fun b => b.insts.any isGot) = true ∧
  out.prepared.code.blocks.any (fun b => b.insts.any isGot) = true ∧
  out.result.code.blocks.any (fun b => b.insts.any isCall) = true ∧
  out.result.blockScans.toList.any (fun event => event.output.records.any (callRecord implicit event)) = true
private instance factsDecidable (implicit : Bool) (out : Output) : Decidable (Facts implicit out) := by
  unfold Facts
  infer_instance
def Observed (implicit : Bool) : Prop :=
  (pipeline implicit).toOption.map (fun out => decide (Facts implicit out)) = some true
/-- Complete ordinary/sret GOT-call sources pass actual lowering, preparation,
global checked fallback and physical lowering with real GOT loads/calls and
retained emitted source records. This observation is cached independently. -/
theorem observed (implicit : Bool) : Observed implicit := by
  cases implicit <;> unfold Observed pipeline <;> decide +kernel
end Backend.Stock.Proof.GotCallFixture

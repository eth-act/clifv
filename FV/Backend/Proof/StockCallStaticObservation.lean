import FV.Backend.Proof.StockCallStaticSource
namespace Backend.Stock.Proof.CallStaticFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.CallAbiStaticDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

def target (result : Result) : Nat := match result.ctx.valueReg? 80 with | some (.vreg n .int) => n | _ => 0
def ctorAt (ctx : Ctx) (term : Term) (args : List V) (before : State) : Except String (V × State) :=
  match Stock.externCtor ctx term args before with
  | .ok out => .ok out
  | .fail => .error "call fixture helper failed"
  | .unmodeled error => .error error
structure Output where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
  outs : V
  afterOut : State
  defs : V
  afterPins : State
  uses : V
  afterArgs : State
  info : V
  afterInfo : State

def pipeline (indirect implicit : Bool) : Except String Output := do
  let result ← Stock.lower (function indirect implicit)
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force complete call-static fallback")
  let af ← lowerRFunc prepared.code rf
  let (outs,afterOut) ← ctorAt result.ctx T.gen_call_output [.op (.sig (signature indirect implicit))] result.initial
  let (defs,afterPins) ← ctorAt result.ctx T.gen_call_rets [.op (.sig (signature indirect implicit)),outs] afterOut
  let (uses,afterArgs) ← ctorAt result.ctx T.gen_call_args [.op (.sig (signature indirect implicit)),
    .regsVec (((numbers indirect implicit).map fun n => Reg.vreg n .int).map fun r => [r])] afterPins
  let (info,afterInfo) ← ctorAt result.ctx (infoTerm indirect)
    (infoArgs indirect (signature indirect implicit) calleeName (target result) uses defs) afterArgs
  pure ⟨result,prepared,rf,af,outs,afterOut,defs,afterPins,uses,afterArgs,info,afterInfo⟩
def isCall : MInst → Bool | .call _ => true | _ => false
def isStackStore : MInst → Bool | .store _ _ (.spOffset _) _ => true | _ => false
def Facts (indirect implicit : Bool) (out : Output) : Prop :=
  out.result.code.blocks.any (fun b => b.insts.any isCall) = true ∧
  out.prepared.code.blocks.any (fun b => b.insts.any isCall) = true ∧
  (arguments indirect implicit).all (fun x => out.result.ctx.valueReg? x == some (.vreg (192+x) .int)) = true ∧
  (if implicit then out.outs = .regsVec [] else out.outs ≠ .regsVec []) ∧
  (if !indirect && !implicit then out.afterArgs.base.emitted.any isStackStore = true else True)
private instance factsDecidable (indirect implicit : Bool) (out : Output) : Decidable (Facts indirect implicit out) := by
  unfold Facts
  infer_instance

def Observed (indirect implicit : Bool) : Prop :=
  (pipeline indirect implicit).toOption.map (fun out => decide (Facts indirect implicit out)) = some true
/-- Four complete original direct/indirect ordinary/sret call pipelines reach
actual call code, raw/global-checked/physical stages and a real helper protocol.
The nine-argument direct case has a nonempty stack-argument store. -/
theorem observed (indirect implicit : Bool) : Observed indirect implicit := by
  cases indirect <;> cases implicit <;> unfold Observed pipeline <;> decide +kernel
end Backend.Stock.Proof.CallStaticFixture

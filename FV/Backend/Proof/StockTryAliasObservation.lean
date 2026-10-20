import FV.Backend.Proof.StockTryAliasSource
namespace Backend.Stock.Proof.TryAliasFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def context (result : Result) : Ctx := {result.ctx with tryRegs := result.initial.tryRegs[1]!}
def isTryCall : MInst → Bool | .tryCall .. => true | _ => false
structure Data where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
  value : Backend.V
  after : State

def pipeline : Except String Data := do
  let result ← Stock.lower function
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force actual try-alias global checked fallback")
  let af ← lowerRFunc prepared.code rf
  let .ok (value,after) := Stock.externCtor (context result) T.gen_try_call_rets [.op (.sig signature)] result.initial
    | throw "try-call reservation helper failed"
  pure ⟨result,prepared,rf,af,value,after⟩

def Observed : Prop := pipeline.toOption.map (fun q => decide
  (q.result.initial.tryRegs[1]? = some ([.vreg 193 .int],[.vreg 194 .int,.vreg 195 .int]) ∧
   (q.after.alias[194]?).join = some 193 ∧ (q.result.final.alias[194]?).join = some 193) &&
    q.result.code.blocks.any (fun b => b.insts.any isTryCall) &&
    q.prepared.code.blocks.any (fun b => b.insts.any isTryCall)) = some true

theorem observed : Observed := by
  unfold Observed pipeline
  decide +kernel

end Backend.Stock.Proof.TryAliasFixture

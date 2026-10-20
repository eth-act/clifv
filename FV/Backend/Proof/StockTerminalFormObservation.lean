import FV.Backend.Proof.StockEmissionCoverageFixture

namespace Backend.Stock.Proof.Coverage.TerminalDraftObservation
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.EmissionCoverageFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def termDataValue : V := (Backend.termData (.ret [7])).toOption.getD (.op .unit)
def context (result : Backend.Stock.Result) : Ctx :=
  {Driver.termCtx result.ctx 1 termDataValue with tryRegs := result.initial.tryRegs[1]!}
def before (result : Backend.Stock.Result) : State := scanState result.initial 1
structure Data where
  result : Backend.Stock.Result
  out : Option V
  after : State
  trace : List RuleId
  emission : Emission
  scan : Scan
  body : BlockScan

def pipeline : Except String Data := do
  let result ← Stock.lower (function false)
  let (out,after,trace) ← Stock.runTerm (context result) "lower" [.inst 1] (before result)
  let emission ← emitInstruction (context result) 1 (before result)
  let scan ← scanInstruction (context result) 0 1 1 false result.initial
  let body ← scanBlock (context result) 0 1 false [1,0] result.initial
  pure ⟨result,out,after,trace,emission,scan,body⟩

def Observed : Prop := pipeline.toOption.map (fun q => decide
  (q.out.isSome = true ∧ q.emission.code ≠ #[] ∧ q.scan.emitted ≠ #[] ∧
    q.body.code.any (fun i => !i.isCtl) = true)) = some true

theorem observed : Observed := by
  unfold Observed pipeline
  decide +kernel

end Backend.Stock.Proof.Coverage.TerminalDraftObservation

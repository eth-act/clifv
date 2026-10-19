import FV.Backend.Proof.StockEmissionCoverageFixture
import FV.Backend.Proof.StockCoverageBlock

namespace Backend.Stock.Proof.Coverage.CoreDraftObservation
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.EmissionCoverageFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def sourceBlock (branch : Bool) : Clif.Block := (function branch).blocks[0]!
def data (branch : Bool) : V := (blockData (function branch) (sourceBlock branch).term).toOption.getD (.op .unit)
def context (branch : Bool) (result : Backend.Stock.Result) : Ctx :=
  {Driver.termCtx result.ctx 1 (data branch) with tryRegs := result.initial.tryRegs[1]!}
structure Data where
  result : Backend.Stock.Result
  branch : Option BranchEmission
  core : LoweredBlockCore

def pipeline (branch : Bool) : Except String Data := do
  let result ← Stock.lower (function branch)
  let br ← (if branch then some <$> (emitBranch (context branch result) (function branch)
    (sourceBlock branch).term 0 1 result.order.successors[0]! result.initial) else pure none)
  let core ← lowerBlockCore result.ctx result.order (function branch) (sourceBlock branch) 0 0 2
    (data branch) result.order.successors[0]! result.initial
  pure ⟨result,br,core⟩

def Observed (branch : Bool) : Prop := (pipeline branch).toOption.map (fun q => decide
  (q.core.code.any (fun i => !i.isCtl) = true ∧
    (if branch then q.branch.any (fun br => br.code.any (fun i => !i.isCtl)) = true else q.branch = none))) = some true

theorem observed (branch : Bool) : Observed branch := by
  cases branch <;> unfold Observed pipeline <;> decide +kernel

end Backend.Stock.Proof.Coverage.CoreDraftObservation

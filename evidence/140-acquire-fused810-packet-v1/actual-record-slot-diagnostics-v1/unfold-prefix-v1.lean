import FV.Backend.Proof.StockAcquirePreparedRecordOrigin

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

/-- Actual core execution retains its original source branch classification. -/
theorem blockCore_source_branch {ctx : Ctx} {order : Order} {f : Clif.Function} {block : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f block bi start stop data targets input = .ok core) :
    core.scan.isBranch = Coverage.blockBranch block.term := by
  unfold lowerBlockCore at run
  dsimp only at run
  trace_state

end Backend.Stock.Proof.Acquire810

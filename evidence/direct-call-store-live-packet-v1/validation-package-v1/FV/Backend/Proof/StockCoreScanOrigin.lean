import FV.Backend.Proof.StockNodeRecordOrigin

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
attribute [local irreducible] emitBranch collectOutgoing scanBlock

/-- The block core's retained scan is its actual successful scan call, with
the exact term override, block range and final state used by the driver. -/
theorem stock_lowerBlockCore_scanOrigin {ctx : Ctx} {order : Order}
    {f : Clif.Function} {b : Clif.Block} {bi start stop : Nat} {data : Backend.V}
    {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    core.state = core.scan.output.state ∧
      core.scan.ctx = { Driver.termCtx ctx (stop - 1) data with tryRegs := input.tryRegs[stop - 1]! } ∧
      core.scan.block = bi ∧ core.scan.termInst = stop - 1 ∧
      core.scan.indices = (((Array.range (stop - start)).map (start + ·)).reverse.toList) ∧
      scanBlock core.scan.ctx core.scan.block core.scan.termInst core.scan.isBranch
        core.scan.indices core.scan.input = .ok core.scan.output := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals
    cases run
    exact ⟨rfl, rfl, rfl, rfl, rfl, by assumption⟩

/-- The successful core from an actual node witness has the exact scan call
and metadata, and emits a jump. All core-origin premises are inhabited. -/
theorem stock_lowerBlockCore_scanOrigin_witness :
    ∃ (ctx : Ctx) (order : Order) (f : Clif.Function) (b : Clif.Block)
      (bi start stop : Nat) (data : Backend.V) (targets : Array Nat)
      (input : State) (core : LoweredBlockCore),
      lowerBlockCore ctx order f b bi start stop data targets input = .ok core ∧
      core.state = core.scan.output.state ∧
      core.scan.ctx = { Driver.termCtx ctx (stop - 1) data with tryRegs := input.tryRegs[stop - 1]! } ∧
      core.scan.block = bi ∧ core.scan.termInst = stop - 1 ∧
      core.scan.indices = (((Array.range (stop - start)).map (start + ·)).reverse.toList) ∧
      scanBlock core.scan.ctx core.scan.block core.scan.termInst core.scan.isBranch
        core.scan.indices core.scan.input = .ok core.scan.output := by
  obtain ⟨_, output, event, call, insts, member, new, bi, data, core, node, coreRun, eventEq, stateEq⟩ :=
    stock_lowerNode_newBlockScan_witness
  exact ⟨_, _, _, _, bi, _, _, data, _, _, core, coreRun,
    stock_lowerBlockCore_scanOrigin coreRun⟩

end Backend.Stock.Proof

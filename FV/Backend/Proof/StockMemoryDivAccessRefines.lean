import FV.Backend.Proof.StockMemoryAccessScanTrap
import FV.Backend.Proof.StockMemoryAccessReach
import FV.Backend.Proof.StockDivSourceTrap
import FV.Backend.Proof.StockDivUdivWideSourceValues

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual unsigned division preserves the ordinary memory relation on success. -/
theorem stock_udiv_memory_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.div .udiv .i64 x y)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {env : Clif.Env} {cp : Clif.Program} {MR : MemRelT}
    (statementResults : stm.results = [z]) (stable : MRStable F MR) :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  intro before after stepped ρ world related
  obtain ⟨index,advance,executedSource⟩ := stepped
  have position : before.1 = j := Nat.add_left_cancel (index.symm.trans current)
  obtain ⟨func,dfg,memory,held⟩ := related
  rw [position] at dfg held
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg executedSource
  obtain ⟨u,v,d,q,outputs,bounds,division,sameMemory,execution⟩ :=
    ScalarDiv.stock_lower_udiv_wide_source_by_instruction run scope dominated events records
      block statement current source clif results statementResults mapped recorded emitted refines dfg held executedSource
  obtain ⟨regs,next,executed,same,post⟩ := execution world
  have details := executedSource
  obtain ⟨actual,inst,vals,sourceRegs,rest,found,original,body,outcome,written,updated⟩ := details
  have nextFunc : after.2.1.func = f := by rw [updated]; exact func
  have nextSlots : after.2.1.slots = before.2.1.slots := by rw [updated]
  refine ⟨regs,next,executed,nextFunc,?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [nextSlots,sameMemory]
    exact stable _ _ _ _ same memory
  · simpa only [advance,position] using post.2.2

/-- A source division fault takes the explicit-trap branch without a divisor guard. -/
theorem stock_udiv_access_first_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.div .udiv .i64 x y)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {env : Clif.Env} {cp : Clif.Program} {MR : MemRelT}
    (initial : Clif.State) {sb : Nat} {code : Clif.TrapCode}
    (property : BitVec 64 → Nat → Prop) :
    LocalAccessTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx bi)
      sb isem result.final.alias
      (ReachedGuardedRel f result event.ctx bi MR env cp initial) property record code := by
  intro point failed ρ world related
  have position : point.1 = j := Nat.add_left_cancel (failed.1.symm.trans current)
  obtain ⟨func,dfg,memory,held⟩ := related.1
  rw [position] at dfg held
  obtain ⟨index,actual,inst,rest,present,original,remaining,outcome⟩ := failed
  cases Option.some.inj (present.symm.trans source)
  cases Option.some.inj (original.symm.trans clif)
  obtain ⟨d,outputs,bounds,execution⟩ := ScalarDiv.stock_lower_udiv_source_trap run scope dominated events records
    block statement current source clif results mapped recorded emitted refines dfg held outcome
  exact Or.inl (execution world)

end Backend.Stock.Proof.MemoryFaults

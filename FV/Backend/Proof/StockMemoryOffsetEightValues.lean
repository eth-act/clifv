import FV.Backend.Proof.StockMemoryIntegerRecordValues
import FV.Backend.Proof.StockMemoryOffsetEightLoadRecord

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- A retained parameter-load record executes on the original source memory and
transfers the source-available demanded set. Code, fresh definitions, binding,
final aliases and demand preservation are derived from the actual whole run. -/
theorem stock_lower_integer_load_eight_values (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load width.sourceTy flags x 8)) (results : info.results = [z])
    (statementResults : stm.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none)
    (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState} {v : Clif.Val}
    (memory : MR fr.slots cm w) (dfg : DFGCons event.ctx fr)
    (operands : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) x)
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (little : flags.endianness ≠ some .big)
    (evaluated : Clif.evalInst fr cm (.load .load width.sourceTy flags x 8) = .ok ([v],cm')) :
    ∃ ρ' w',seqRun isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') ∧
      SameWorld F w' w ∧ MR fr.slots cm' w' ∧
      VHolds v (ρ' record.input.base.nextVreg) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx (withValue fr z v)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨outputs,code,upper,finalAlias,_⟩ := stock_lower_integer_load_eight_record width run scope dominated events records
    source clif results mapped parameter pointer recorded emitted
  have bound : result.final.alias.size ≤ record.input.base.nextVreg := by
    simpa only [scan_frontier] using stock_lower_blockScanAliasBounds run event events record records
  have fixed : aliasNum result.final.alias record.input.base.nextVreg = record.input.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bound]
    rfl
  have resolved : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [.load width.loadOp (.vreg record.input.base.nextVreg .int)
        (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 8) flags] := by
    rw [code]
    change [MInst.load width.loadOp
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg record.input.base.nextVreg .int))
      (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg nreg .int)) 8) flags] = _
    rw [resolve_vreg,resolve_vreg]
    change [MInst.load width.loadOp (.vreg (aliasNum result.final.alias record.input.base.nextVreg) .int)
      (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 8) flags] = _
    rw [fixed]
  have pointerTy := (stock_lower_record_context run scope events).1.addr64 _ _ _ x source clif rfl
  have address := mapped_unsigned_address (sb := sb) (bytes := width.loadOp.bytes) (w := w) operands pointer dfg pointerTy
    (off := 8) (by cases width <;> decide)
  obtain ⟨ρ',w',executed,same,memory',values,keep⟩ := load_source_seqRun stable memorySem memoryOk memory
    (ρ := ρ) (d := record.input.base.nextVreg)
    (am := .unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 8)
    (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩)
    (aop := width.loadOp) (by cases width <;> decide)
    (by cases width <;> rfl) (by cases width <;> rfl) (by cases width <;> decide) little
    (fun pv hpv => by simpa [amUses,amVregs,AMode.regs,amodeAddr,LoadOp.bytes] using address pv hpv) evaluated
  have value := values v (by simp)
  have actualRun : seqRun isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') := by
    rwa [resolved]
  have defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),∀ key ∈ vdefs m,
      record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
    rw [resolved]
    intro m member key defined
    have equal := List.mem_singleton.mp member
    subst m
    change key ∈ [record.input.base.nextVreg] at defined
    have equal := List.mem_singleton.mp defined
    subst key
    rw [upper]
    exact ⟨Nat.le_refl _,Nat.lt_succ_self _⟩
  exact ⟨ρ',w',actualRun,same,memory',value,
    stock_lower_fresh_record_values_auto_demand run scope dominated events records block statement current
      source clif results statementResults mapped recorded emitted outputs (Nat.le_refl _) held defs actualRun value⟩

end Backend.Stock.Memory.IntegerRoots

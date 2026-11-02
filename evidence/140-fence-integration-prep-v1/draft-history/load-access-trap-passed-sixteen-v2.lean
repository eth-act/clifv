import FV.Backend.Proof.StockMemoryAccessScanTrap
import FV.Backend.Proof.StockMemoryAccessReach
import FV.Backend.Proof.StockMemoryOffsetSixteenSourceValues

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver Backend.Stock.Memory
open Backend.Stock.Memory.IntegerRoots
set_option autoImplicit false
set_option Elab.async false

/-- The actual scalar load is the fault boundary; its memory access is not executed. -/
theorem AccessTrapRun.load {sb : Nat} {isem : Backend.Proof.Sem} {op : LoadOp}
    {d : Nat} {am : AMode} (vregs : AmVregs am) {flags : Clif.MemFlags}
    {ρ : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {address : BitVec 64} {property : BitVec 64 → Nat → Prop}
    (flag : flags.trapCode = some code)
    (access : amodeAddr sb am op.bytes (amUses am ρ) world = some address)
    (holds : property address op.bytes) :
    AccessTrapRun sb isem [.load op (.vreg d .int) am flags] ρ world code property := by
  obtain ⟨ops,operands,uses,defs,update⟩ := (load_ops op d vregs flags).ops
  exact ⟨[],.load op (.vreg d .int) am flags,[],ρ,world,ops,amUses am ρ,
    address,op.bytes,rfl,rfl,operands,uses ρ,.load flag access,holds⟩

/-- A retained original offset16 load reaches its actual access at the source fault.
The original guarded relation supplies the mapped pointer and actual source reachability. -/
theorem stock_load_sixteen_access_trap (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load width.sourceTy flags x 16)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none) (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {env : Clif.Env} {cp : Clif.Program} (initial : Clif.State) {code : Clif.TrapCode}
    {sb : Nat} {isem : Backend.Proof.Sem} {MR : MemRelT} (Q : Nat → Nat → Prop)
    (allFaults : ∀ state addr bytes,Reach env cp initial state →
      Clif.MemTrapAt env cp state code addr bytes → Q addr bytes) :
    LocalAccessTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx bi)
      sb isem result.final.alias
      (ReachedGuardedRel f result event.ctx bi MR env cp initial)
      (sourceAddrPred Q) record code := by
  intro point failed ρ world related
  have required := stock_lower_integer_load_sixteen_operand_coverage width run scope dominated events records
    block statement current source clif results mapped parameter pointer recorded emitted
  have position : point.1 = j := Nat.add_left_cancel (failed.1.symm.trans current)
  obtain ⟨value,pointerValue,property,flag⟩ := indexed_load_property initial Q allFaults related.2 source clif failed
  obtain ⟨func,dfg,memory,held⟩ := related.1
  rw [position] at dfg held
  have pointerRegs : point.2.1.regs x = some value := by
    cases actual : point.2.1.regs x with
    | none => simp [Clif.Frame.get,actual,Clif.Res.ofOption] at pointerValue
    | some actualValue =>
      have equal : actualValue = value := by
        simpa only [Clif.Frame.get,actual,Clif.Res.ofOption,Clif.Res.ok.injEq] using pointerValue
      exact congrArg some equal
  have restrictedHeld : ValueHeld event.ctx (restrict point.2.1 (availOf f (availIn f result.ctx) bi j))
      (fun k => ρ (aliasNum result.final.alias k)) x := by
    intro val found
    rw [restrict_regs_of_mem required.2] at found
    exact held x required val found
  have pointerType := (stock_lower_record_context run scope events).1.addr64 _ _ _ x source clif rfl
  have address := mapped_unsigned_address (sb := sb) (bytes := width.loadOp.bytes) (w := world)
    restrictedHeld pointer dfg pointerType (off := 16) (by cases width <;> decide) value
    (by simpa only [restrict_regs_of_mem required.2] using pointerRegs)
  obtain ⟨outputs,codeShape,upper,finalAlias,demands⟩ := stock_lower_integer_load_sixteen_record width
    run scope dominated events records source clif results mapped parameter pointer recorded emitted
  have frontier : (scanState record.input record.inst).base.nextVreg = record.input.base.nextVreg := by
    unfold scanState; dsimp only; split <;> rfl
  have bound : result.final.alias.size ≤ record.input.base.nextVreg := by
    simpa only [frontier] using stock_lower_blockScanAliasBounds run event events record records
  have fixed : aliasNum result.final.alias record.input.base.nextVreg = record.input.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bound]
    rfl
  have resolved : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [.load width.loadOp (.vreg record.input.base.nextVreg .int)
        (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 16) flags] := by
    rw [codeShape]
    change [MInst.load width.loadOp
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg record.input.base.nextVreg .int))
      (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg nreg .int)) 16) flags] = _
    rw [resolve_vreg,resolve_vreg]
    change [MInst.load width.loadOp (.vreg (aliasNum result.final.alias record.input.base.nextVreg) .int)
      (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 16) flags] = _
    rw [fixed]
  apply Or.inr
  rw [resolved]
  apply AccessTrapRun.load (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩) flag
  · simpa only [amUses,amVregs,AMode.regs,List.filterMap_cons,List.filterMap_nil,List.map_cons,List.map_nil,amodeAddr]
      using address
  · exact ⟨Clif.effAddr value 16,rfl,by cases width <;> exact property⟩

end Backend.Stock.Proof.MemoryFaults

import FV.Backend.Proof.StockMemoryAccessScanTrap
import FV.Backend.Proof.StockMemoryAccessReach
import FV.Backend.Proof.StockMemoryOffsetEightStoreScanRefines

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver Backend.Stock.Memory
open Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false

/-- Store access uses exclude the stored value when computing the address. -/
theorem AccessTrapRun.store {sb : Nat} {isem : Backend.Proof.Sem} {op : StoreOp}
    {v : Nat} {am : AMode} (vregs : AmVregs am) {flags : Clif.MemFlags}
    {ρ : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {address : BitVec 64} {property : BitVec 64 → Nat → Prop}
    (flag : flags.trapCode = some code)
    (access : amodeAddr sb am op.bytes (amUses am ρ) world = some address)
    (holds : property address op.bytes) :
    AccessTrapRun sb isem [.store op (.vreg v .int) am flags] ρ world code property := by
  obtain ⟨ops,operands,uses,defs,update⟩ := (store_ops op v vregs flags).ops
  exact ⟨[],.store op (.vreg v .int) am flags,[],ρ,world,ops,ρ v :: amUses am ρ,
    address,op.bytes,rfl,rfl,operands,uses ρ,.store flag access,holds⟩

/-- An actual offset8 i64 store reaches the source fault with its computed value.
No parameter restriction applies to the stored value. -/
theorem stock_store_eight_i64_access_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store .store .i64 flags value pointer 8))
    (typed : event.ctx.valueType? value = some (.int 64))
    (parameter : event.ctx.defInst? pointer = none)
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
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
  have typed' : Kind.sourceOp .plain64 = .store → event.ctx.valueType? value = some (.int 64) := fun _ => typed
  have required := stock_lower_integer_store_eight_operand_coverage .plain64 run scope dominated events records
    block statement current source clif typed' parameter pointerMapped valueMapped recorded emitted
  have needPointer := required pointer (Or.inr rfl)
  have position : point.1 = j := Nat.add_left_cancel (failed.1.symm.trans current)
  obtain ⟨addressValue,pointerValue,property,flag⟩ := indexed_store_property initial Q allFaults related.2 source clif failed
  obtain ⟨func,dfg,memory,held⟩ := related.1
  rw [position] at dfg held
  have pointerRegs : point.2.1.regs pointer = some addressValue := by
    cases actual : point.2.1.regs pointer with
    | none => simp [Clif.Frame.get,actual,Clif.Res.ofOption] at pointerValue
    | some actualValue =>
      have equal : actualValue = addressValue := by
        simpa only [Clif.Frame.get,actual,Clif.Res.ofOption,Clif.Res.ok.injEq] using pointerValue
      exact congrArg some equal
  have restrictedHeld : ValueHeld event.ctx (restrict point.2.1 (availOf f (availIn f result.ctx) bi j))
      (fun k => ρ (aliasNum result.final.alias k)) pointer := by
    intro val found
    rw [restrict_regs_of_mem needPointer.2] at found
    exact held pointer needPointer val found
  have pointerType := (stock_lower_record_context run scope events).1.addr64 _ _ _ pointer source clif rfl
  have address := mapped_unsigned_address (sb := sb) (bytes := 8) (w := world)
    restrictedHeld pointerMapped dfg pointerType (off := 8) (by decide) addressValue
    (by simpa only [restrict_regs_of_mem needPointer.2] using pointerRegs)
  obtain ⟨empty,allowed,outputs,state,codeShape,upper,alias,demands⟩ := stock_lower_integer_store_eight_record .plain64
    run scope events records source clif typed' parameter pointerMapped valueMapped recorded emitted
  have resolved : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [.store .store64 (.vreg (aliasNum result.final.alias valueReg) .int)
        (.unsignedOffset (.vreg (aliasNum result.final.alias pointerReg) .int) 8) flags] := by
    rw [codeShape]
    change [MInst.store .store64
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg valueReg .int))
      (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointerReg .int)) 8) flags] = _
    rw [resolve_vreg,resolve_vreg]
    rfl
  apply Or.inr
  rw [resolved]
  apply AccessTrapRun.store (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩) flag
  · simpa only [amUses,amVregs,AMode.regs,List.filterMap_cons,List.filterMap_nil,List.map_cons,List.map_nil,amodeAddr,StoreOp.bytes]
      using address
  · exact ⟨Clif.effAddr addressValue 8,rfl,property⟩

end Backend.Stock.Proof.MemoryFaults

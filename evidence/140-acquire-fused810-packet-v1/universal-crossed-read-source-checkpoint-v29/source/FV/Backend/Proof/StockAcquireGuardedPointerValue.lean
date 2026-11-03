import FV.Backend.Proof.StockAcquireSelectedOriginalPointerRequest
import FV.Backend.Proof.StockAcquirePointerAvailable
import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockDemandMono

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The actual original pointer is demanded at the retained record's forward entry. -/
theorem stock_lower_acquire_selected_original_pointer_demanded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {rootInfo : IInfo} {target : Clif.Ty} {value : Nat}
    (rootInstalled : event.ctx.insts[record.inst]? = some rootInfo)
    (rootSource : rootInfo.clif = some (.extend .uextend target value))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (producer : Nat) (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat) (address : Reg),
      event.ctx.defInst? value = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧ event.ctx.valueReg? pointer = some address ∧
      Demanded record.output.state pointer := by
  obtain ⟨producer,info,ty,flags,pointer,middle,requested,address,out,next,fired,
    defined,installed,source,integer,little,root,sink,request,safe,mapped,marked,demand⟩ :=
    stock_lower_acquire_selected_original_pointer_request run scope events records
      rootInstalled rootSource recorded emitted selectedId
  have inside := (Extent.lower_mapped_demand_bounds run scope events records mapped).1
  have middleDemand : middle.demand = record.input.demand := by
    rw [(sink_accepted sink).2.2.2.2]
    unfold scanState
    dsimp only
    split <;> rfl
  have middleInside : pointer < middle.demand.size := by rwa [middleDemand]
  have positive : Demanded requested pointer := by
    rw [marked]
    exact (demanded_mark_iff middle pointer pointer middleInside).mpr (Or.inl rfl)
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have same := Except.ok.inj (root.symm.trans receipt.rootRun)
  have nextEq : next = receipt.next := congrArg (fun p : Option V × State × List RuleId => p.2.1) same
  have finalDemand : record.output.state.demand = next.demand := by
    rw [receipt.state,stock_bindResults_demand receipt.binding,nextEq]
  refine ⟨producer,info,ty,flags,pointer,address,defined,installed,source,integer,little,mapped,?_⟩
  change record.output.state.demand[pointer]! ≠ 0
  rw [finalDemand,demand]
  exact positive


/-- The unchanged source availability relation supplies the actual original deferred pointer. -/
theorem stock_lower_acquire_guarded_pointer_held {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {rootInfo : IInfo} {target : Clif.Ty} {value : Nat}
    (rootInstalled : event.ctx.insts[record.inst]? = some rootInfo)
    (rootSource : rootInfo.clif = some (.extend .uextend target value))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (producer : Nat) (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat) (address : Reg),
      event.ctx.defInst? value = some producer ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ eTy ty = true ∧ flags.endianness ≠ some .big ∧
      event.ctx.valueReg? pointer = some address ∧
      ∀ (fr : Clif.Frame) (regs : Nat → CV),
        ValuesHeld (fun y => Demanded record.output.state y ∧ y ∈ availOf f (availIn f result.ctx) bi j)
          event.ctx fr regs → ValueHeld event.ctx fr regs pointer := by
  obtain ⟨producer,info,ty,flags,pointer,address,defined,installed,source,integer,little,mapped,demand⟩ :=
    stock_lower_acquire_selected_original_pointer_demanded run scope events records rootInstalled rootSource
      recorded emitted selectedId
  obtain ⟨otherProducer,otherInfo,otherTy,otherFlags,otherPointer,otherDefined,otherInstalled,
    otherSource,_,_,available⟩ := stock_lower_acquire_selected_pointer_available run scope dominated
      events records blockAt statement current rootInstalled rootSource recorded emitted selectedId
  have sameProducer : otherProducer = producer := Option.some.inj (otherDefined.symm.trans defined)
  subst otherProducer
  have sameInfo : otherInfo = info := Option.some.inj (otherInstalled.symm.trans installed)
  subst otherInfo
  have sameInst := Option.some.inj (otherSource.symm.trans source)
  have samePointer : otherPointer = pointer := (Clif.Inst.atomicLoad.inj sameInst).2.2
  rw [samePointer] at available
  exact ⟨producer,info,ty,flags,pointer,address,defined,installed,source,integer,little,mapped,
    fun fr regs held => held pointer ⟨demand,available⟩⟩

end Backend.Stock.Proof.Acquire810

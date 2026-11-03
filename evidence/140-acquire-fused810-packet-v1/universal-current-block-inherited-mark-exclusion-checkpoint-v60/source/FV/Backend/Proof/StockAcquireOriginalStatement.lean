import FV.Backend.Proof.StockAcquireSelectedSingleton

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- A retained source definition identifies its exact original statement and source position. -/
theorem stock_lower_event_original_definition {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {value producer : Nat} {info : IInfo} {inst : Clif.Inst}
    (defined : event.ctx.defInst? value = some producer)
    (installed : event.ctx.insts[producer]? = some info) (source : info.clif = some inst) :
    ∃ bi block j stm, f.blocks[bi]? = some block ∧ block.body[j]? = some stm ∧
      value ∈ stm.results ∧ producer = blockStart f bi+j ∧ stm.inst = inst := by
  have resultInfo := (stock_lower_record_context run scope events).2.2 producer info inst installed source
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeIndex,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1] at defined
  have originalDef : original.defInst? value = some producer := by
    simpa only [Ctx.defInst?,termCtx,view.valDef] using defined
  obtain ⟨bi,block,j,stm,blockAt,statement,valueResult,position⟩ := spec.defOf value producer originalDef
  obtain ⟨actual,present,actualSource,actualResults⟩ := spec.facts.stmt bi block j stm blockAt statement
  rw [view.insts,position] at resultInfo
  have same : actual = info := Option.some.inj (present.symm.trans resultInfo)
  subst actual
  have originalInst : stm.inst = inst := Option.some.inj (actualSource.symm.trans source)
  exact ⟨bi,block,j,stm,blockAt,statement,valueResult,position,originalInst⟩

/-- Actual root810 selection derives the original atomic statement without a source-position certificate. -/
theorem stock_lower_acquire_selected_original_statement {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (value producer bi : Nat) (block : Clif.Block) (j : Nat) (stm : Clif.Stmt)
      (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      f.blocks[bi]? = some block ∧ block.body[j]? = some stm ∧ value ∈ stm.results ∧
      producer = blockStart f bi+j ∧ stm.inst = .atomicLoad ty flags pointer ∧
      eTy ty = true ∧ flags.endianness ≠ some .big := by
  obtain ⟨value,producer,info,ty,flags,pointer,out,next,fired,
    defined,once,installed,source,integer,little,root,pending,sunk,color⟩ :=
    stock_lower_acquire_selected_singleton run scope events records recorded emitted selectedId
  obtain ⟨bi,block,j,stm,blockAt,statement,valueResult,position,original⟩ :=
    stock_lower_event_original_definition run scope events defined installed source
  exact ⟨value,producer,bi,block,j,stm,ty,flags,pointer,blockAt,statement,valueResult,position,
    original,integer,little⟩

end Backend.Stock.Proof.Acquire810

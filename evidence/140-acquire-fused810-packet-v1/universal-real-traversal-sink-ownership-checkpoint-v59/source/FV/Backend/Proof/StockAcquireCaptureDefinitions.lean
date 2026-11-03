import FV.Backend.Proof.StockAcquireCaptureMarkSync

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual source payload excludes the synthetic terminator and derives its original body position. -/
theorem stock_lower_source_record_body_position {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some inst) :
    ∃ (block : Clif.Block) (j : Nat) (stm : Clif.Stmt),f.blocks[event.block]? = some block ∧
      block.body[j]? = some stm ∧ record.inst = blockStart f event.block+j ∧
      info.results = stm.results := by
  have notTerm : record.inst ≠ event.termInst := by
    intro same
    have noSource := stock_lower_event_term_source_none run events
    have actual : event.ctx.insts[event.termInst]!.clif = some inst := by
      rw [← same]
      simp only [getElem!_def,installed,source]
    rw [noSource] at actual
    cases actual
  obtain ⟨block,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bodyMember : record ∈ body.records := by
    rw [split.records] at records
    rcases List.mem_cons.mp records with same | member
    · exact False.elim (notTerm ((congrArg ScanRecord.inst same).trans split.termInst))
    · exact member
  obtain ⟨j,stm,statement,current⟩ := split.positions record bodyMember
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events (split.retained record bodyMember)
  obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of built).facts.stmt event.block block j stm split.block statement
  have view := stock_lower_event_build_source_slots run scope events built
  have sameInfo : actualInfo = info := by
    have actual : event.ctx.insts[record.inst]? = some actualInfo := by
      rw [current]
      exact view _ actualInfo stm.inst present actualSource
    exact Option.some.inj (actual.symm.trans installed)
  exact ⟨block,j,stm,split.block,statement,current,by rw [← sameInfo];exact results⟩

/-- Original SSA derives every captured result's exact source definition in the actual event context. -/
theorem stock_lower_source_record_results_defined {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some inst) :
    ∀ value ∈ info.results,event.ctx.defInst? value = some record.inst := by
  obtain ⟨block,j,stm,blockAt,statement,current,results⟩ :=
    stock_lower_source_record_body_position run scope events records installed source
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,ordered,
    initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  intro value resultMember
  have defined := defInst_res spec.facts dominated.ssa blockAt statement (by rwa [← results] : value ∈ stm.results)
  rw [← current] at defined
  rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
  simpa only [Ctx.defInst?,Driver.termCtx,view.valDef] using defined

/-- Capture definitions come from actual lowering and source execution, not a caller's result certificate. -/
theorem stock_lower_sunk_snapshot_definitions {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {program : Clif.Program} (captured : SunkReadSnapshot event.ctx env program)
    (retained : captured.record ∈ event.output.records) :
    ∀ value ∈ event.ctx.insts[captured.record.inst]!.results,event.ctx.defInst? value = some captured.record.inst := by
  obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,written,frame⟩ := captured.source
  have bang : event.ctx.insts[captured.record.inst]! = info := by simp only [getElem!_def,installed]
  rw [bang]
  exact stock_lower_source_record_results_defined run scope dominated events retained installed source

end Backend.Stock.Proof.Acquire810

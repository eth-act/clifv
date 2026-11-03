import FV.Backend.Proof.StockAcquirePendingValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem statement_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j) {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst) :
    info.results = stm.results := by
  have globalSource := (stock_lower_record_context run scope events).2.2 _ _ _ source clif
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,ordered,
    initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨other,found,originalClif,results⟩ := spec.facts.stmt bi block j stm blockAt statement
  have actual : original.insts[blockStart f bi+j]? = some info := by
    rw [← view.insts,← current]
    exact globalSource
  cases Option.some.inj (found.symm.trans actual)
  exact results

/-- A successful actual sunk source read records its exact snapshot and preserves the remaining driver relation.
No demanded-result zero condition or singleton restriction is used. Faults are retained separately below. -/
theorem stock_lower_sunk_pending_transfer {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (marked : record.input.sunk[record.inst]! = true)
    {bi j : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {isem : Backend.Proof.Sem}
    {before after : SourcePoint} (source : IndexedSourceInst env program f event.ctx bi record.inst before after)
    {snapshots : List (SunkReadSnapshot event.ctx env program)} {regs : Nat → CV} {world : Arm.ArmState}
    (prior : PendingGuardedScanRel f result event.ctx bi env program MR snapshots record.output.state before regs world) :
    ∃ captured : SunkReadSnapshot event.ctx env program,
      captured.record = record ∧ captured.before = before.2 ∧ captured.after = after.2 ∧
      seqRun isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
          some (.fall regs world) ∧
      PendingGuardedScanRel f result event.ctx bi env program MR (snapshots++[captured]) record.input after regs world := by
  obtain ⟨indexed,advance,sourceStep⟩ := source
  have position : before.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func,dfg,memory,values⟩ := prior
  rw [position] at dfg values
  have postDFG := stock_lower_source_step_dfg run scope dominated events blockAt statement current func dfg sourceStep
  have read := stock_lower_record_marked_source_read run scope events records record.inst marked
  let captured : SunkReadSnapshot event.ctx env program := ⟨record,before.2,after.2,marked,sourceStep,read⟩
  have memorySame := captured.memory
  have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
  have outputEq := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked))
  have stateEq : record.output.state = record.input := congrArg Scan.state outputEq
  have empty : record.output.emitted = #[] := congrArg Scan.emitted outputEq
  obtain ⟨info,inst,vals,writtenRegs,rest,installed,clif,body,outcome,written,frame⟩ := sourceStep
  have names := statement_results run scope events blockAt statement current installed clif
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,installed]
  refine ⟨captured,rfl,rfl,rfl,?_,?_,?_,?_,?_⟩
  · simp only [empty,Array.toList_empty,List.map_nil,seqRun]
  · rw [frame]
    exact func
  · simpa only [advance,position] using postDFG
  · rw [frame,memorySame]
    exact memory
  · intro value required notSuspended v lookup
    have notResult : value ∉ info.results := by
      intro resultMember
      apply notSuspended
      apply suspended_read_result_append_last snapshots captured
      simpa only [captured,bang] using resultMember
    have notOld : ¬SuspendedReadResult snapshots value := fun member =>
      notSuspended (suspended_read_result_append_left member)
    have available := available_before_of_after_not_result blockAt statement
      (by simpa only [advance,position] using required.2) (by rwa [← names])
    have demanded : Demanded record.output.state value := by rw [stateEq];exact required.1
    have old : before.2.1.regs value = some v := by
      rw [frame] at lookup
      change writtenRegs value = some v at lookup
      rwa [setMany_other written notResult] at lookup
    exact values value ⟨demanded,available⟩ notOld v old

/-- An actual sunk source fault is retained with its original record and code, without a success assumption. -/
theorem stock_lower_sunk_fault_snapshot {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (marked : record.input.sunk[record.inst]! = true)
    {env : Clif.Env} {program : Clif.Program} {before : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (failed : SourceInstFault env program event.ctx record.inst before code) :
    ∃ captured : SunkFaultSnapshot event.ctx env program,
      captured.record = record ∧ captured.before = before ∧ captured.code = code := by
  exact ⟨⟨record,before,code,marked,failed,
    stock_lower_record_marked_source_read run scope events records record.inst marked⟩,rfl,rfl,rfl⟩

end Backend.Stock.Proof.Acquire810

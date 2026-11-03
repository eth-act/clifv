import FV.Backend.Proof.StockAcquireConsumerSourceSlot

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual selected unary consumers occupy original body statements rather than synthetic terminator slots. -/
theorem stock_lower_acquire_consumer_body_position {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (block : Clif.Block) (j : Nat) (stm : Clif.Stmt) (info : IInfo),
      f.blocks[event.block]? = some block ∧ block.body[j]? = some stm ∧
      record.inst = blockStart f event.block+j ∧ event.termInst = blockStart f event.block+block.body.length ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some stm.inst := by
  obtain ⟨info,inst,installed,source⟩ := stock_lower_acquire_consumer_source run scope events records recorded emitted selectedId
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
  have original : info.clif = some stm.inst := by rw [← sameInfo];exact actualSource
  exact ⟨block,j,stm,info,split.block,statement,current,split.termIndex,installed,original⟩

end Backend.Stock.Proof.Acquire810

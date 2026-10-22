namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Reuse all previously proved scalar-family handlers at one actual quiet
prefix record, while other source positions may contain real division. -/
theorem highmul_source_record_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {record : ScanRecord} (records : record ∈ event.output.records)
    {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    (family : HighMulBody.Family stm.inst)
    (recordSource : PureBody.SourceRecord f event.ctx bi record)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := recordSource
  have sameB : b' = b := Option.some.inj (found.symm.trans block)
  subst b'
  have sameJ : j' = j := Nat.add_left_cancel (indexed.symm.trans current)
  subst j'
  have sameStmt : stm' = stm := Option.some.inj (atStmt.symm.trans statement)
  subst stm'
  rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
  · exact stock_lower_omitted_scan_fall_refines run scope dominated events records
      block statement current recorded omitted
  · have classified := HighMulBody.emitted_record_family block statement current recorded emitted
      source clif one results mapped family
    exact stock_lower_mixed_highmul_record_fall_refines run scope dominated events records
      sourceFamily classified refines driver stable
end Backend.Stock.Proof.QuietSourceColors
#print axioms Backend.Stock.Proof.QuietSourceColors.highmul_source_record_fall_refines

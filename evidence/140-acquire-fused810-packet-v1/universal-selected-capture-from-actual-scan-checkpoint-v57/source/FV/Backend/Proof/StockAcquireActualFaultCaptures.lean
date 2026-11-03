import FV.Backend.Proof.StockAcquireActualReadCaptures

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual retained-prefix membership is derived from the complete scan, not supplied by callers. -/
theorem stock_lower_actual_prefix_read_captures {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (count : Nat)
    {env : Clif.Env} {program : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    (executed : SourceSteps (SourceInstResult env program event.ctx)
      ((event.output.records.reverse.take count).map (·.inst)) before after) :
    ∃ captures,SourceReadCaptures event.ctx env program (event.output.records.reverse.take count) before after captures ∧
      ∀ captured ∈ captures,captured.record ∈ event.output.records := by
  apply stock_lower_source_read_captures run scope events ?_ executed
  intro record member
  exact List.mem_reverse.mp (List.mem_of_mem_take member)

/-- Every first source fault retains its complete preceding capture history and the exact failing record. -/
theorem stock_lower_source_fault_captures {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {records : List ScanRecord} (retained : ∀ record ∈ records,record ∈ event.output.records)
    {env : Clif.Env} {program : Clif.Program} {before : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (failed : SourceTrapSteps (SourceInstResult env program event.ctx) (SourceInstFault env program event.ctx)
      (records.map (·.inst)) before code) :
    ∃ (earlier : List ScanRecord) (faultRecord : ScanRecord) (later : List ScanRecord)
      (atFault : Clif.Frame × Clif.Mem) (captures : List (SunkReadSnapshot event.ctx env program)),
      records = earlier++faultRecord::later ∧
      SourceReadCaptures event.ctx env program earlier before atFault captures ∧
      SourceInstFault env program event.ctx faultRecord.inst atFault code ∧
      (faultRecord.input.sunk[faultRecord.inst]! = true →
        ∃ captured : SunkFaultSnapshot event.ctx env program,
          captured.record = faultRecord ∧ captured.before = atFault ∧ captured.code = code) := by
  induction records generalizing before with
  | nil => cases failed
  | cons record records ih =>
    cases failed with
    | here fault =>
      refine ⟨[],record,records,before,[],rfl,.nil _,fault,?_⟩
      intro marked
      exact stock_lower_sunk_fault_snapshot run scope events (retained record (List.mem_cons_self ..)) marked fault
    | @next slot rest state middle code source tail =>
      obtain ⟨earlier,faultRecord,later,atFault,captures,parts,trace,fault,faultSnapshot⟩ :=
        ih (fun actual member => retained actual (List.mem_cons_of_mem _ member)) tail
      cases marked : record.input.sunk[record.inst]! with
      | false =>
        refine ⟨record::earlier,faultRecord,later,atFault,captures,?_,.skipped marked source trace,fault,faultSnapshot⟩
        rw [parts]
        rfl
      | true =>
        have read := stock_lower_record_marked_source_read run scope events (retained record (List.mem_cons_self ..)) record.inst marked
        refine ⟨record::earlier,faultRecord,later,atFault,⟨record,before,middle,marked,source,read⟩::captures,
          ?_,.captured marked source read trace,fault,faultSnapshot⟩
        rw [parts]
        rfl

/-- The actual Stock prefix derives first-fault captures without an external record or capture certificate. -/
theorem stock_lower_actual_prefix_fault_captures {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (count : Nat)
    {env : Clif.Env} {program : Clif.Program} {before : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (failed : SourceTrapSteps (SourceInstResult env program event.ctx) (SourceInstFault env program event.ctx)
      ((event.output.records.reverse.take count).map (·.inst)) before code) :
    ∃ (earlier : List ScanRecord) (faultRecord : ScanRecord) (later : List ScanRecord)
      (atFault : Clif.Frame × Clif.Mem) (captures : List (SunkReadSnapshot event.ctx env program)),
      event.output.records.reverse.take count = earlier++faultRecord::later ∧
      SourceReadCaptures event.ctx env program earlier before atFault captures ∧
      SourceInstFault env program event.ctx faultRecord.inst atFault code ∧
      (faultRecord.input.sunk[faultRecord.inst]! = true →
        ∃ captured : SunkFaultSnapshot event.ctx env program,
          captured.record = faultRecord ∧ captured.before = atFault ∧ captured.code = code) := by
  apply stock_lower_source_fault_captures run scope events ?_ failed
  intro record member
  exact List.mem_reverse.mp (List.mem_of_mem_take member)

end Backend.Stock.Proof.Acquire810

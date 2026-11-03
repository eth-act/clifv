import FV.Backend.Proof.StockAcquireExecutedScanFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual selected sink derives a singleton group in the stronger frontier.
The complete global queue remains unrestricted. -/
theorem executed_frontier_acquire_singleton {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {pending : List Nat} (frontier : ExecutedRecordFrontier f event.ctx record pending) : pending = [R.producer] := by
  obtain ⟨producer,info,ty,flags,pointer,middle,requested,address,out,next,fired,
    defined,installed,source,integer,little,root,sink,request,safe,register,marked,demand⟩ :=
    stock_lower_acquire_selected_original_pointer_request run scope events records R.rootInstalled R.rootSource recorded emitted selectedId
  have producerEq := Option.some.inj (defined.symm.trans R.defined)
  subst producer
  have started := (sink_accepted sink).2.1
  rw [scanState_entry_colors] at started
  obtain ⟨positive,finished⟩ := stock_lower_acquire_original_definition_color run scope events records recorded emitted selectedId
    R.rootInstalled R.rootSource R.defined
  have trace := (frontier.2 step recorded emitted).forget.forget
  have distance := trace.color_distance finished
  have equal := Option.some.inj (started.symm.trans distance)
  have length : pending.length = 1 := by omega
  obtain ⟨actual,shape⟩ := List.length_eq_one_iff.mp length
  have member : actual ∈ pending := by rw [shape];exact List.mem_cons_self ..
  have bounds := trace.member_color_bounds finished actual member
  rw [scanState_entry_colors,shape] at bounds
  simp only [List.length_cons,List.length_nil] at bounds
  have sameColor : record.input.entryColor[actual]! = record.input.entryColor[R.producer]! := by omega
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  rw [← sourceMetadata_color_events] at table
  have buildEq := Except.ok.inj (built.symm.trans R.built)
  have ctxEq := congrArg Prod.fst buildEq
  have rangesEq := congrArg (fun value => value.2.1) buildEq
  dsimp only at ctxEq rangesEq
  rw [ctxEq,rangesEq] at table
  have scannedMeta := (scanState_entry_colors record.input record.inst).trans table
  have actualSource := trace.source_members R.built scannedMeta actual member
  have source : some R.producer ∈ sourceColorEvents R.original R.ranges := by
    rw [R.position]
    exact original_colored_statement_event R.built R.blockAt R.producerAt (by rw [R.atomic];rfl)
  rw [table] at sameColor
  have before := source_color_le_reflects_slots R.built actualSource source (Nat.le_of_eq sameColor)
  have after := source_color_le_reflects_slots R.built source actualSource (Nat.le_of_eq sameColor.symm)
  have actualEq := Nat.le_antisymm before after
  simpa only [actualEq] using shape

/-- Actual queue membership binds the selected deferred producer to the actual final-alias acquire segment. -/
theorem stock_lower_acquire_executed_effect_binding {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) {pending : List Nat}
    (frontier : ExecutedRecordFrontier f event.ctx record pending) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest label index : Nat) (block : VBlock),
      pending = [R.producer] ∧ event.ctx.valueReg? R.pointer = some (.vreg pointerReg .int) ∧
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] := by
  obtain ⟨R,pointerReg,dest,resultId,key,label,index,block,register,results,resultReg,fresh,terminal,finalAlias,finalNum,found,segment⟩ :=
    stock_lower_acquire_selected_resolved_segment run scope dominated events records recorded emitted selectedId
  exact ⟨R,pointerReg,dest,label,index,block,
    executed_frontier_acquire_singleton run scope events records recorded emitted selectedId R frontier,register,found,segment⟩

end Backend.Stock.Proof.Acquire810

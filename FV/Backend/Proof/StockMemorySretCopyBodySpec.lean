import FV.Backend.Proof.StockMemoryOffsetEightStoreRetention
import FV.Backend.Proof.StockMemoryStoredLoadSpec
import FV.Backend.Proof.StockMemoryOffsetEightLoadRecord
import FV.Backend.Proof.StockGuardedOmission

namespace Backend.Stock.Memory.SretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

structure BodyRecord (f : Clif.Function) (event : BlockScanEvent) (body : BlockScan)
    (j : Nat) (inst : Clif.Inst) (outputs : List Nat) where
  record : ScanRecord
  step : Step
  info : IInfo
  member : record ∈ body.records
  current : record.inst = blockStart f event.block+j
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some inst
  results : info.results = outputs

structure BodySpec (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block)
    (i0 i8 j0 j8 base destination low high : Nat) (lf0 lf8 sf0 sf8 : Clif.MemFlags) where
  term : ScanRecord
  body : BlockScan
  split : SourceBodySplit f event b term body
  baseReg : Nat
  destinationReg : Nat
  lowReg : Nat
  highReg : Nat
  baseMapped : event.ctx.valueReg? base = some (.vreg baseReg .int)
  destinationMapped : event.ctx.valueReg? destination = some (.vreg destinationReg .int)
  lowMapped : event.ctx.valueReg? low = some (.vreg lowReg .int)
  highMapped : event.ctx.valueReg? high = some (.vreg highReg .int)
  baseParameter : event.ctx.defInst? base = none
  destinationParameter : event.ctx.defInst? destination = none
  lowType : event.ctx.valueType? low = some (.int 64)
  highType : event.ctx.valueType? high = some (.int 64)
  loadLow : BodyRecord f event body i0 (.load .load .i64 lf0 base 0) [low]
  loadHigh : BodyRecord f event body i8 (.load .load .i64 lf8 base 8) [high]
  storeLow : BodyRecord f event body j0 (.store .store .i64 sf0 low destination 0) []
  storeHigh : BodyRecord f event body j8 (.store .store .i64 sf8 high destination 8) []
  family : ∀ record ∈ body.records,record = loadLow.record ∨ record = loadHigh.record ∨
    record = storeLow.record ∨ record = storeHigh.record ∨
    ∃ step,record.output.step = some step ∧ step.decision = .omitted

private theorem source_record {f : Clif.Function} {event : BlockScanEvent}
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) :
    ∃ record ∈ body.records,record.inst = blockStart f event.block+j := by
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have indexed : blockStart f event.block+j ∈ sourceBodyIndices f event.block b := by
    unfold sourceBodyIndices
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨j,List.mem_range.mpr inside,rfl⟩)
  rw [← split.scanned.order] at indexed
  exact List.mem_map.mp indexed

/-- Original source syntax derives all four retained records from actual store demands.
The shared specification supports single-world and paired body composition. -/
theorem captured_sret_copy_body_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {i0 i8 j0 j8 base destination low high : Nat} {lf0 lf8 sf0 sf8 : Clif.MemFlags}
    (loadLow : b.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩)
    (loadHigh : b.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩)
    (storeLow : b.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩)
    (storeHigh : b.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩)
    (lowEarlier : i0 < j0) (highEarlier : i8 < j8)
    (shape : ∀ j stm,b.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop)
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (baseParameter : base ∈ pb.params.map (·.1))
    (destinationParameter : destination ∈ pb.params.map (·.1)) :
    Nonempty (BodySpec f result event b i0 i8 j0 j8 base destination low high lf0 lf8 sf0 sf8) := by
  obtain ⟨term,s0,body,step0,split,member0,current0,_,_,records0,recorded0,emitted0⟩ :=
    stock_lower_mixed_store_emitted run scope events block storeLow
  obtain ⟨term8,s8,body8,step8,split8,member8,current8,_,_,records8,recorded8,emitted8⟩ :=
    stock_lower_mixed_store_emitted run scope events block storeHigh
  have sameRecords : body8.records = body.records :=
    (List.cons.inj (split8.records.symm.trans split.records)).2
  have member8 : s8 ∈ body.records := by rw [← sameRecords]; exact member8
  obtain ⟨storeInfo0,storeSource0,storeClif0,storeResults0⟩ :=
    ArithmeticBody.body_source_info run events split storeLow current0
  obtain ⟨storeInfo8,storeSource8,storeClif8,storeResults8⟩ :=
    ArithmeticBody.body_source_info run events split storeHigh current8
  obtain ⟨r0,_,at0⟩ := source_record split loadLow
  obtain ⟨r8,_,at8⟩ := source_record split loadHigh
  obtain ⟨info0,source0,clif0,results0⟩ := ArithmeticBody.body_source_info run events split loadLow at0
  obtain ⟨info8,source8,clif8,results8⟩ := ArithmeticBody.body_source_info run events split loadHigh at8
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨_,_,resultType0⟩ := IntegerRoots.integer_load_source_data_offset .w64 inv source0 clif0
  obtain ⟨_,_,resultType8⟩ := IntegerRoots.integer_load_source_data_offset .w64 inv source8 clif8
  have lowType : event.ctx.valueType? low = some (.int 64) :=
    StoreRoots.stock_lower_source_result_type run scope dominated events (m := 0) source0 clif0
      (by simp [results0]) (by simpa only [List.head?_eq_getElem?,IntegerRoots.Width.bits] using resultType0)
  have highType : event.ctx.valueType? high = some (.int 64) :=
    StoreRoots.stock_lower_source_result_type run scope dominated events (m := 0) source8 clif8
      (by simp [results8]) (by simpa only [List.head?_eq_getElem?,IntegerRoots.Width.bits] using resultType8)
  obtain ⟨lowReg,lowMapped⟩ := inv.typedReg low _ lowType
  obtain ⟨highReg,highMapped⟩ := inv.typedReg high _ highType
  obtain ⟨baseReg,baseMapped⟩ := inv.typedReg base _ (inv.addr64 _ _ _ base source0 clif0 rfl)
  obtain ⟨destinationReg,destinationMapped⟩ := inv.typedReg destination _
    (inv.addr64 _ _ _ destination storeSource0 storeClif0 rfl)
  have baseDefinition := stock_lower_source_parameter_definition run dominated events parameterBlock baseParameter
  have destinationDefinition := stock_lower_source_parameter_definition run dominated events parameterBlock destinationParameter
  let first : StoreRoots.RetainedStoreReturnSpec .plain64 .i64 f result event b j0 low destination sf0 :=
    ⟨term,s0,body,step0,storeInfo0,lowReg,destinationReg,split,member0,current0,records0,recorded0,emitted0,
      storeSource0,storeClif0,(fun _ => lowType),lowMapped,destinationDefinition,destinationMapped⟩
  obtain ⟨l0,lstep0,lmember0,lcurrent0,_,_,_,lrecords0,lrecorded0,lemitted0⟩ :=
    StoreRoots.stock_retained_stored_definition_emitted .plain64 .i64 run scope dominated events first
      loadLow lowEarlier (by simp)
  obtain ⟨l8,lstep8,lmember8,lcurrent8,_,_,_,_,lrecords8,lrecorded8,lemitted8⟩ :=
    StoreRoots.stock_lower_integer_store_eight_definition_emitted .plain64 run scope dominated events split
      member8 current8 storeSource8 storeClif8 (fun _ => highType) destinationDefinition destinationMapped
      highMapped recorded8 emitted8 loadHigh highEarlier (by simp)
  obtain ⟨linfo0,lsource0,lclif0,lresults0⟩ := ArithmeticBody.body_source_info run events split loadLow lcurrent0
  obtain ⟨linfo8,lsource8,lclif8,lresults8⟩ := ArithmeticBody.body_source_info run events split loadHigh lcurrent8
  let a : BodyRecord f event body i0 (.load .load .i64 lf0 base 0) [low] :=
    ⟨l0,lstep0,linfo0,lmember0,lcurrent0,lrecorded0,lemitted0,lsource0,lclif0,lresults0⟩
  let c : BodyRecord f event body i8 (.load .load .i64 lf8 base 8) [high] :=
    ⟨l8,lstep8,linfo8,lmember8,lcurrent8,lrecorded8,lemitted8,lsource8,lclif8,lresults8⟩
  let d : BodyRecord f event body j0 (.store .store .i64 sf0 low destination 0) [] :=
    ⟨s0,step0,storeInfo0,member0,current0,recorded0,emitted0,storeSource0,storeClif0,storeResults0⟩
  let g : BodyRecord f event body j8 (.store .store .i64 sf8 high destination 8) [] :=
    ⟨s8,step8,storeInfo8,member8,current8,recorded8,emitted8,storeSource8,storeClif8,storeResults8⟩
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  refine ⟨⟨term,body,split,baseReg,destinationReg,lowReg,highReg,baseMapped,destinationMapped,
    lowMapped,highMapped,baseDefinition,destinationDefinition,lowType,highType,a,c,d,g,?_⟩⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  rcases shape j stm statement with rfl | rfl | rfl | rfl | nop
  · exact Or.inl (split.scanned.record_unique unique member lmember0 (current.trans lcurrent0.symm))
  · exact Or.inr (Or.inl (split.scanned.record_unique unique member lmember8 (current.trans lcurrent8.symm)))
  · exact Or.inr (Or.inr (Or.inl (split.scanned.record_unique unique member member0 (current.trans current0.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (split.scanned.record_unique unique member member8 (current.trans current8.symm)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (MaskBody.actual_nop_record_at_block run scope events split member statement current nop))))

end Backend.Stock.Memory.SretCopy

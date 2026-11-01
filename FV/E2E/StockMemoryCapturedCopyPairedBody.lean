import FV.Backend.Proof.StockMemoryLoadedPointerStoreRetention
import FV.Backend.Proof.StockMemoryComputedStoreRecordSpec
import FV.E2E.StockMemoryOffsetEightPairedScan
import FV.E2E.StockMemoryIntegerPairedScan
import FV.E2E.StockMemoryLoadedPointerPairedScan
import FV.E2E.StockMemoryOmittedPairedScan
import FV.Backend.Proof.StockMaskBlockRecords

namespace E2E.StockMemory.CapturedCopy
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

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

/-- Original load/load/store syntax derives the complete guarded body execution.
Both loaded operands are retained by the actual store demand, including a loaded destination pointer. -/
theorem captured_copy_paired_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {iv ip is base value pointer : Nat} {vf pf sf : Clif.MemFlags}
    (valueStatement : b.body[iv]? = some ⟨[value],.load .load .i64 vf base 8⟩)
    (pointerStatement : b.body[ip]? = some ⟨[pointer],.load .load .i64 pf base 0⟩)
    (storeStatement : b.body[is]? = some ⟨[],.store .store .i64 sf value pointer 0⟩)
    (valueEarlier : iv < is) (pointerEarlier : ip < is)
    (shape : ∀ j stm,b.body[j]? = some stm → j = iv ∨ j = ip ∨ j = is ∨ stm.inst = .nop)
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (parameter : base ∈ pb.params.map (·.1))
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ w →
          ∃ ρ' w',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' w' := by
  obtain ⟨term,store,body,storeStep,split,storeMember,storeCurrent,_,_,storeRecords,storeRecorded,storeEmitted⟩ :=
    stock_lower_mixed_store_emitted run scope events block storeStatement
  obtain ⟨storeInfo,storeSource,storeClif,_⟩ :=
    ArithmeticBody.body_source_info run events split storeStatement storeCurrent
  obtain ⟨vr,_,vc⟩ := source_record split valueStatement
  obtain ⟨pr,_,pc⟩ := source_record split pointerStatement
  obtain ⟨valueInfo,valueSource,valueClif,valueResults⟩ :=
    ArithmeticBody.body_source_info run events split valueStatement vc
  obtain ⟨pointerInfo,pointerSource,pointerClif,pointerResults⟩ :=
    ArithmeticBody.body_source_info run events split pointerStatement pc
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨_,_,valueType⟩ := IntegerRoots.integer_load_source_data_offset .w64 inv valueSource valueClif
  obtain ⟨_,pointerData,pointerType⟩ :=
    IntegerRoots.integer_load_source_data_offset .w64 inv pointerSource pointerClif
  have valueTyped : event.ctx.valueType? value = some (.int 64) :=
    StoreRoots.stock_lower_source_result_type run scope dominated events (m := 0) valueSource valueClif
      (by simp [valueResults]) (by simpa only [List.head?_eq_getElem?,IntegerRoots.Width.bits] using valueType)
  obtain ⟨valueReg,valueMapped⟩ := inv.typedReg value _ valueTyped
  obtain ⟨pointerReg,pointerMapped⟩ := inv.typedReg pointer _ (inv.addr64 _ _ _ pointer storeSource storeClif rfl)
  obtain ⟨baseReg,baseMapped⟩ := inv.typedReg base _ (inv.addr64 _ _ _ base pointerSource pointerClif rfl)
  have baseDefinition := stock_lower_source_parameter_definition run dominated events parameterBlock parameter
  have pointerDefinition : event.ctx.defInst? pointer = some pr.inst := by
    rw [pc]
    exact stock_lower_source_result_definition run dominated events block pointerStatement (by simp)
  have typed : StoreRoots.Kind.sourceOp .plain64 = .store →
      event.ctx.valueType? value = some (.int (StoreRoots.Kind.width .plain64).bits) := fun _ => valueTyped
  obtain ⟨valueRecord,valueStep,valueMember,valueCurrent,_,_,_,_,valueRecords,valueRecorded,valueEmitted⟩ :=
    StoreRoots.stock_lower_loaded_pointer_store_definition_emitted .plain64 run scope dominated events split
      storeMember storeCurrent storeSource storeClif typed pointerDefinition pointerSource pointerData pointerType
      pointerMapped valueMapped storeRecorded storeEmitted valueStatement valueEarlier (by simp) (Or.inl rfl)
  obtain ⟨pointerRecord,pointerStep,pointerMember,pointerCurrent,_,_,_,_,pointerRecords,pointerRecorded,pointerEmitted⟩ :=
    StoreRoots.stock_lower_loaded_pointer_store_definition_emitted .plain64 run scope dominated events split
      storeMember storeCurrent storeSource storeClif typed pointerDefinition pointerSource pointerData pointerType
      pointerMapped valueMapped storeRecorded storeEmitted pointerStatement pointerEarlier (by simp) (Or.inr rfl)
  have valueSource' : event.ctx.insts[valueRecord.inst]? = some valueInfo := by
    rw [valueCurrent,← vc]; exact valueSource
  have pointerSource' : event.ctx.insts[pointerRecord.inst]? = some pointerInfo := by
    rw [pointerCurrent,← pc]; exact pointerSource
  have valueRefines := IntegerRoots.stock_lower_integer_load_eight_paired_scan .w64 run scope dominated
    events valueRecords block valueStatement valueCurrent valueSource' valueClif valueResults rfl valueMapped
    baseDefinition baseMapped valueRecorded valueEmitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have pointerRefines := IntegerRoots.stock_lower_integer_load_paired_scan .w64 run scope dominated
    events pointerRecords block pointerStatement pointerCurrent pointerSource' pointerClif pointerResults rfl pointerMapped
    baseDefinition baseMapped pointerRecorded pointerEmitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have storeRefines := StoreRoots.stock_lower_loaded_pointer_store_paired_scan .plain64 .i64 run scope dominated
    events storeRecords block storeStatement storeCurrent storeSource storeClif typed pointerDefinition pointerSource
    pointerData pointerType pointerMapped valueMapped storeRecorded storeEmitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  have each : ∀ record ∈ body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      (pairSem (csem Γ.F fc X)) result.final.alias (PairedScanRel f result event.ctx event.block Γ c D) record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    rcases shape j stm statement with rfl | rfl | rfl | nop
    · have same := split.scanned.record_unique unique member valueMember (current.trans valueCurrent.symm)
      simpa only [same] using valueRefines
    · have same := split.scanned.record_unique unique member pointerMember (current.trans pointerCurrent.symm)
      simpa only [same] using pointerRefines
    · have same := split.scanned.record_unique unique member storeMember (current.trans storeCurrent.symm)
      simpa only [same] using storeRefines
    · obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events split member statement current nop
      exact stock_lower_omitted_paired_scan run scope dominated events (split.retained record member)
        block statement current (records_execute split.scanned record member) recorded omitted
  refine ⟨term,body,split,?_⟩
  intro s s' steps ρ w held
  apply split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [split.state] using held

end E2E.StockMemory.CapturedCopy

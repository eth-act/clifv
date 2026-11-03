import FV.Backend.Proof.StockMemoryOffsetEightLoadRecord
import FV.Backend.Proof.StockMemoryOffsetEightStoreRecord
import FV.Backend.Proof.StockMemoryComputedStoreRecordWitness

namespace Backend.Stock.Memory.StoreRoots.ComputedFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def flags : Clif.MemFlags := {trapCode := none}
private def observed : Option Bool :=
  (Stock.lower function).toOption.map fun result =>
    lowerScopeB function && dominatedB function &&
    result.blockScans.toList.any fun event =>
      decide (event.ctx.defInst? 0 = none) && decide (event.ctx.defInst? 1 = none) &&
      event.output.records.any fun load =>
        decide (load.inst = 4) && load.output.step.any fun loadStep =>
          decide (loadStep.decision = .emitted) &&
          (event.ctx.insts[load.inst]?).any fun loadInfo =>
            decide (loadInfo.clif = some (.load .load .i64 flags 1 8)) &&
            decide (loadInfo.results = [3]) &&
            decide (loadInfo.resTys[0]? = some (.int 64)) &&
            event.output.records.any fun store =>
              decide (store.inst = 6) && store.output.step.any fun storeStep =>
                decide (storeStep.decision = .emitted) &&
                (event.ctx.insts[store.inst]?).any fun storeInfo =>
                  decide (storeInfo.clif = some (.store .store .i64 flags 3 0 8))
private theorem observed_true : observed = some true := by native_decide

/-- Original captured offset8 records inhabit source matching, dispatch and result binding.
The source function retains its sret purpose, source blocks and load-result stores. -/
theorem captured_offset_eight_records_witness :
    ∃ (result : Result) (event : BlockScanEvent) (load store : ScanRecord)
      (loadStep storeStep : Step) (valueReg loadPointer storePointer : Nat),
      Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧
      load ∈ event.output.records ∧ store ∈ event.output.records ∧ load.inst = 4 ∧ store.inst = 6 ∧
      load.output.step = some loadStep ∧ loadStep.decision = .emitted ∧
      store.output.step = some storeStep ∧ storeStep.decision = .emitted ∧
      loadStep.rules.getLast? = some rule_lower_2613.id ∧
      storeStep.rules.getLast? = some rule_lower_2717.id ∧
      loadStep.results = [[.vreg load.input.base.nextVreg .int]] ∧
      load.output.emitted = #[.load .uload64 (.vreg load.input.base.nextVreg .int)
        (.unsignedOffset (.vreg loadPointer .int) 8) flags] ∧
      aliasNum result.final.alias valueReg = load.input.base.nextVreg ∧
      store.output.emitted = #[.store .store64 (.vreg valueReg .int)
        (.unsignedOffset (.vreg storePointer .int) 8) flags] ∧
      DemandAllowed event.ctx (scanState store.input store.inst) 3 := by
  have actual := observed_true
  unfold observed at actual
  cases run : Stock.lower function with
  | error message => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨scopeB,domB,event,events,storeParameter,loadParameter,load,loads,loadIndex,loadStep,
      loadRecorded,loadEmitted,loadInfo,loadSource,loadClif,loadResults,loadType,
      store,stores,storeIndex,storeStep,storeRecorded,storeEmitted,storeInfo,storeSource,storeClif⟩ :=
      (by simpa only [List.any_eq_true,Option.any_eq_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc]
        using actual :
        lowerScopeB function = true ∧ dominatedB function = true ∧
        ∃ event ∈ result.blockScans.toList,
          event.ctx.defInst? 0 = none ∧ event.ctx.defInst? 1 = none ∧
          ∃ load ∈ event.output.records,load.inst = 4 ∧
          ∃ loadStep,load.output.step = some loadStep ∧ loadStep.decision = .emitted ∧
          ∃ loadInfo,event.ctx.insts[load.inst]? = some loadInfo ∧
            loadInfo.clif = some (.load .load .i64 flags 1 8) ∧ loadInfo.results = [3] ∧
            loadInfo.resTys[0]? = some (.int 64) ∧
          ∃ store ∈ event.output.records,store.inst = 6 ∧
          ∃ storeStep,store.output.step = some storeStep ∧ storeStep.decision = .emitted ∧
          ∃ storeInfo,event.ctx.insts[store.inst]? = some storeInfo ∧
            storeInfo.clif = some (.store .store .i64 flags 3 0 8))
    have scope := lowerScope_of scopeB
    have dominated := dominated_of domB
    have inv := (stock_lower_record_context run scope events).1
    have valueType := stock_lower_source_result_type run scope dominated events loadSource loadClif
      (by rw [loadResults]; rfl : loadInfo.results[0]? = some 3) loadType
    obtain ⟨valueReg,valueMapped⟩ := inv.typedReg 3 _ valueType
    obtain ⟨loadPointer,loadMapped⟩ := inv.typedReg 1 _ (inv.addr64 _ _ _ 1 loadSource loadClif rfl)
    obtain ⟨storePointer,storeMapped⟩ := inv.typedReg 0 _ (inv.addr64 _ _ _ 0 storeSource storeClif rfl)
    have loadId := IntegerRoots.stock_lower_integer_load_selected_id_offset .w64 run scope events loads
      loadSource loadClif loadRecorded loadEmitted
    have storeId := stock_lower_integer_store_selected_id_offset .plain64 run scope events stores
      storeSource storeClif (by intro plain; exact valueType) storeRecorded storeEmitted
    obtain ⟨outputs,loadCode,frontier,alias,demand⟩ := IntegerRoots.stock_lower_integer_load_eight_record
      .w64 run scope dominated events loads loadSource loadClif loadResults valueMapped loadParameter
      loadMapped loadRecorded loadEmitted
    obtain ⟨empty,guard,noResults,state,storeCode,_,_,_⟩ := stock_lower_integer_store_eight_record
      .plain64 run scope events stores storeSource storeClif (by intro plain; exact valueType)
      storeParameter storeMapped valueMapped storeRecorded storeEmitted
    exact ⟨result,event,load,store,loadStep,storeStep,valueReg,loadPointer,storePointer,rfl,events,
      loads,stores,loadIndex,storeIndex,loadRecorded,loadEmitted,storeRecorded,storeEmitted,
      loadId,storeId,outputs,loadCode,alias,storeCode,guard⟩

end Backend.Stock.Memory.StoreRoots.ComputedFixture

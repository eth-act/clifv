import FV.Backend.Proof.StockMemoryLoadedPointerStoreRetention
import FV.Backend.Proof.StockMemoryLoadedPointerFixture
import FV.Backend.Proof.StockMemoryIntegerSelected

namespace Backend.Stock.Memory.StoreRoots.LoadedPointerWitness
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open IntegerRoots.LoadedPointerFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def flags : Clif.MemFlags := {trapCode := none}
private def observed : Option Bool :=
  (Stock.lower function).toOption.map fun result =>
    lowerScopeB function && dominatedB function &&
    result.blockScans.toList.any fun event =>
      decide (function.blocks[event.block]? = some function.blocks[1]!) &&
      decide (function.blocks[1]!.body[3]? = some ⟨[],.store .store .i64 flags 2 3 0⟩) &&
      decide (function.blocks[1]!.body[1]? = some ⟨[2],.load .load .i64 flags 0 8⟩) &&
      decide (function.blocks[1]!.body[2]? = some ⟨[3],.load .load .i64 flags 0 0⟩) &&
      decide (event.ctx.defInst? 3 = some 4) &&
      (event.ctx.insts[3]?).any fun valueInfo =>
        decide (valueInfo.clif = some (.load .load .i64 flags 0 8)) &&
        decide (valueInfo.results[0]? = some 2) && decide (valueInfo.resTys[0]? = some (.int 64)) &&
        (event.ctx.insts[4]?).any fun pointerInfo =>
          decide (pointerInfo.clif = some (.load .load .i64 flags 0 0)) &&
          event.output.records.any fun record =>
            decide (record.inst = 5) && decide (record.inst = blockStart function event.block+3) &&
            record.output.step.any fun step => decide (step.decision = .emitted) &&
              (event.ctx.insts[record.inst]?).any fun info =>
                decide (info.clif = some (.store .store .i64 flags 2 3 0))
private theorem observed_true : observed = some true := by native_decide

/-- The unchanged captured function retains both loads through its computed-pointer store. -/
theorem captured_loaded_pointer_store_record_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block) (record : ScanRecord)
      (step : Step) (valueReg pointerReg : Nat),
      Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧
      function.blocks[event.block]? = some b ∧
      b.body[3]? = some ⟨[],.store .store .i64 flags 2 3 0⟩ ∧
      record ∈ event.output.records ∧ record.inst = 5 ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2717.id ∧
      step.results = [] ∧
      record.output.emitted = #[.store .store64 (.vreg valueReg .int)
        (.unsignedOffset (.vreg pointerReg .int) 0) flags] ∧
      record.output.state.base.nextVreg = record.input.base.nextVreg ∧
      record.output.state.alias = record.input.alias ∧
      DemandAllowed event.ctx (scanState record.input record.inst) 3 ∧
      DemandAllowed event.ctx (scanState record.input record.inst) 2 ∧
      (∀ key,key = 2 ∨ key = 3 → Demanded record.output.state key ∧
        key ∈ availOf function (availIn function result.ctx) event.block 3) ∧
      ∀ key,key = 2 ∨ key = 3 → ∃ (producer : ScanRecord) (producerStep : Step),
        producer ∈ event.output.records ∧ event.ctx.defInst? key = some producer.inst ∧
        producer.input.sunk[producer.inst]! = false ∧
        producer.output.step = some producerStep ∧ producerStep.decision = .emitted := by
  have actual := observed_true
  unfold observed at actual
  cases run : Stock.lower function with
  | error message => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨scopeB,domB,event,events,block,statement,valueStatement,pointerStatement,defined,valueInfo,valueSource,valueClif,valueResult,
      valueTypeAt,pointerInfo,pointerSource,pointerClif,record,records,index,current,step,recorded,emitted,
      info,source,clif⟩ :=
      (by simpa only [List.any_eq_true,Option.any_eq_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc]
        using actual : lowerScopeB function = true ∧ dominatedB function = true ∧
        ∃ event ∈ result.blockScans.toList,
          function.blocks[event.block]? = some function.blocks[1]! ∧
          function.blocks[1]!.body[3]? = some ⟨[],.store .store .i64 flags 2 3 0⟩ ∧
          function.blocks[1]!.body[1]? = some ⟨[2],.load .load .i64 flags 0 8⟩ ∧
          function.blocks[1]!.body[2]? = some ⟨[3],.load .load .i64 flags 0 0⟩ ∧
          event.ctx.defInst? 3 = some 4 ∧
          ∃ valueInfo,event.ctx.insts[3]? = some valueInfo ∧
            valueInfo.clif = some (.load .load .i64 flags 0 8) ∧
            valueInfo.results[0]? = some 2 ∧ valueInfo.resTys[0]? = some (.int 64) ∧
          ∃ pointerInfo,event.ctx.insts[4]? = some pointerInfo ∧
            pointerInfo.clif = some (.load .load .i64 flags 0 0) ∧
          ∃ record ∈ event.output.records,record.inst = 5 ∧ record.inst = blockStart function event.block+3 ∧
          ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          ∃ info,event.ctx.insts[record.inst]? = some info ∧
            info.clif = some (.store .store .i64 flags 2 3 0))
    have scope := lowerScope_of scopeB
    have dominated := dominated_of domB
    have inv := (stock_lower_record_context run scope events).1
    have valueType := stock_lower_source_result_type run scope dominated events valueSource valueClif
      valueResult valueTypeAt
    obtain ⟨valueReg,valueMapped⟩ := inv.typedReg 2 _ valueType
    obtain ⟨pointerReg,pointerMapped⟩ := inv.typedReg 3 _ (inv.addr64 _ _ _ 3 source clif rfl)
    obtain ⟨little,pointerData,pointerType⟩ := IntegerRoots.integer_load_source_data_offset .w64 inv
      pointerSource pointerClif
    have typed : Kind.plain64.sourceOp = .store → event.ctx.valueType? 2 = some (.int Kind.plain64.width.bits) := by
      intro plain
      exact valueType
    obtain ⟨empty,pointerSafe,valueSafe,results,state,code,frontier,alias,demand⟩ :=
      stock_lower_loaded_pointer_store_record .plain64 run scope events records source clif typed defined
        pointerSource pointerData pointerType pointerMapped valueMapped recorded emitted
    have selected := stock_lower_integer_store_selected_id .plain64 run scope events records source clif
      typed recorded emitted
    have coverage := stock_lower_loaded_pointer_store_operand_coverage .plain64 run scope dominated events
      records block statement current source clif typed defined pointerSource pointerData pointerType
      pointerMapped valueMapped recorded emitted
    obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
    have same : b = function.blocks[1]! := Option.some.inj (split.block.symm.trans block)
    subst b
    have storeMember : record ∈ body.records := by
      have member := records
      rw [split.records] at member
      rcases List.mem_cons.mp member with equal | member
      · have index := congrArg ScanRecord.inst equal
        rw [current,split.termInst,split.termIndex] at index
        have bound := lt_of_getElem? statement
        omega
      · exact member
    refine ⟨result,event,function.blocks[1]!,record,step,valueReg,pointerReg,rfl,events,block,statement,
      records,index,recorded,emitted,selected,results,code,frontier,alias,pointerSafe,valueSafe,coverage,?_⟩
    intro key used
    rcases used with rfl | rfl
    · obtain ⟨producer,producerStep,member,producerCurrent,producerDefinition,safe,demanded,actual,
        producers,producerRecorded,producerEmitted⟩ := stock_lower_loaded_pointer_store_definition_emitted
          .plain64 run scope dominated events split storeMember current source clif typed defined pointerSource
          pointerData pointerType pointerMapped valueMapped recorded emitted valueStatement
          (by decide +kernel) (by simp) (Or.inl rfl)
      exact ⟨producer,producerStep,producers,producerDefinition,safe,producerRecorded,producerEmitted⟩
    · obtain ⟨producer,producerStep,member,producerCurrent,producerDefinition,safe,demanded,actual,
        producers,producerRecorded,producerEmitted⟩ := stock_lower_loaded_pointer_store_definition_emitted
          .plain64 run scope dominated events split storeMember current source clif typed defined pointerSource
          pointerData pointerType pointerMapped valueMapped recorded emitted pointerStatement
          (by decide +kernel) (by simp) (Or.inr rfl)
      exact ⟨producer,producerStep,producers,producerDefinition,safe,producerRecorded,producerEmitted⟩

end Backend.Stock.Memory.StoreRoots.LoadedPointerWitness

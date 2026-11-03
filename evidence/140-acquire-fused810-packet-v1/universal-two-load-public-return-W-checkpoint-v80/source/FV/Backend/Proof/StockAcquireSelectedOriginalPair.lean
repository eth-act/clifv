import FV.Backend.Proof.StockAcquireConsumerOperandData

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual consumer matching identifies the original extension and its exact source operand. -/
theorem acquire_args_original_extension {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {st : State} {env : Isle.Interp.Env V} {ii value : Nat}
    (args : matchArgs program (Stock.sem ctx) st rule_lower_1272.args [.inst ii]
      (Array.replicate rule_lower_1272.vars.length none) = .ok (some env))
    (held : env[3]? = some (some (.value value))) {info : IInfo} {inst : Clif.Inst}
    (installed : ctx.insts[ii]? = some info) (source : info.clif = some inst) :
    ∃ target,inst = .extend .uextend target value ∧ eTy target = true := by
  obtain ⟨actual,found,data⟩ := acquire_root_args_original_operand_data args held
  have equal := Option.some.inj (found.symm.trans installed)
  subst actual
  have encoded := mapped.data ii info inst installed source
  rw [data] at encoded
  obtain ⟨target,operand,original,operandEq,integer⟩ := instData_extend_inv encoded (Or.inl rfl)
  have valueEq : value = operand := V.value.inj operandEq
  subst operand
  exact ⟨target,by simpa using original,integer⟩

/-- One actual retained selection derives both original instructions and the deferred output color. -/
theorem stock_lower_acquire_selected_original_pair {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (rootInfo : IInfo) (target : Clif.Ty) (value producer : Nat)
      (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      event.ctx.insts[record.inst]? = some rootInfo ∧ rootInfo.clif = some (.extend .uextend target value) ∧
      event.ctx.defInst? value = some producer ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ eTy ty = true ∧ flags.endianness ≠ some .big ∧
      record.input.entryColor[producer]! ≠ 0 ∧
      record.output.state.color = some record.input.entryColor[producer]! := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some 810 := by rw [← receipt.rules];exact selectedId
  have chosen := acquire_selected_rule receipt.selected last
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuel := receipt.selected.fuelBound
  rw [count] at fuel
  obtain ⟨m,fuelEq⟩ : ∃ m,receipt.selected.matchFuel = m+5 := ⟨receipt.selected.matchFuel-5,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  have rhs := receipt.selected.rhsRun
  rw [chosen] at rhs
  obtain ⟨env,value,producer,args,held,originalSource,matchedEq,traceEq,producerBinding⟩ := acquire_root_match_source matched
  obtain ⟨rootInfo,rootInst,rootInstalled,rootSource⟩ := stock_lower_acquire_consumer_source run scope events records recorded emitted selectedId
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨target,rootShape,targetInteger⟩ := acquire_args_original_extension mapped args held rootInstalled rootSource
  obtain ⟨actualValue,actualProducer,sunk,info,ty,flags,pointer,defined,once,arity,positive,color,
    sink,state,installed,source,integer,little,binding,sameState,sameTrace⟩ :=
    acquire_rule_pending_source mapped (n := 999979) matched rhs
  have sameProducer : producer = actualProducer := V.inst.inj (Option.some.inj (Option.some.inj (producerBinding.symm.trans binding)))
  subst actualProducer
  have originalDefined := (source_effect_eligible originalSource positive).1
  rw [sameState,sameTrace] at rhs
  obtain ⟨middle,sinkUnit,pending,sunkEq,colorEq⟩ := acquire_rhs_pending (n := 999899) binding rhs
  obtain ⟨entries,boundColor,boundSunk⟩ := bindResults_mark_fields receipt.binding
  have inputPositive : record.input.entryColor[producer]! ≠ 0 := by
    simpa only [scanState_entry_colors] using positive
  refine ⟨rootInfo,target,value,producer,info,ty,flags,pointer,rootInstalled,
    rootSource.trans (congrArg some rootShape),originalDefined,installed,source,integer,little,inputPositive,?_⟩
  rw [receipt.state,boundColor,colorEq,scanState_entry_colors]

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockAcquireOriginalProducer
import FV.Backend.Proof.StockAcquireSelectedBinding
import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockAvailableProvenance

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Original dominance supplies the deferred pointer at the real extension boundary. -/
theorem stock_lower_acquire_selected_pointer_available {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {rootInfo : IInfo} {target : Clif.Ty} {value : Nat}
    (rootInstalled : event.ctx.insts[record.inst]? = some rootInfo)
    (rootSource : rootInfo.clif = some (.extend .uextend target value))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (producer : Nat) (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      event.ctx.defInst? value = some producer ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ eTy ty = true ∧ flags.endianness ≠ some .big ∧
      pointer ∈ availOf f (availIn f result.ctx) bi j := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some 810 := by
    rw [← receipt.rules]
    exact selectedId
  have chosen := acquire_selected_rule receipt.selected last
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuel := receipt.selected.fuelBound
  rw [count] at fuel
  obtain ⟨m,fuelEq⟩ : ∃ m,receipt.selected.matchFuel = m+5 :=
    ⟨receipt.selected.matchFuel-5,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  have rhs := receipt.selected.rhsRun
  rw [chosen] at rhs
  obtain ⟨producer,info,ty,flags,pointer,defined,installed,source,integer,little⟩ :=
    acquire_rule_original_extension_source (stock_lower_record_context run scope events).1
      rootInstalled rootSource (n := 999979) matched rhs
  have operand := stock_lower_record_args_available run scope dominated events blockAt statement current
    rootInstalled rootSource value (by simp only [Driver.instArgs,List.mem_singleton])
  have originalDefined := defined
  have originalInfo := (stock_lower_record_context run scope events).2.2 producer info _ installed source
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeIndex,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1] at originalDefined
  have definition : result.ctx.defInst? value = some producer := by
    simpa only [Ctx.defInst?,termCtx] using originalDefined
  have reached : Prov result.ctx producer pointer :=
    .arg originalInfo source (by simp only [Driver.instArgs,List.mem_singleton])
  have available := stock_available_provenance build dominated operand definition reached
  exact ⟨producer,info,ty,flags,pointer,defined,installed,source,integer,little,available⟩

end Backend.Stock.Proof.Acquire810

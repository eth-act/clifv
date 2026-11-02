import FV.Backend.Proof.StockLogicalSelected
import FV.Backend.Proof.StockRootOpcodeMatch

namespace Backend.Stock.Proof.LogicalComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open LogicalSelected
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def opcode : Kind → Nat
  | .band => 97 | .bor => 98 | .bxor => 99

def candidateIds : Kind → List RuleId
  | .band => [842,841,836]
  | .bor => [862,863,855,854,849]
  | .bxor => [870,869,864]

private theorem and_inventory : sourceOpcodeIds 97 = [842,841,836] := by
  unfold sourceOpcodeIds
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel
private theorem or_inventory : sourceOpcodeIds 98 = [862,863,855,854,849] := by
  unfold sourceOpcodeIds
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel
private theorem xor_inventory : sourceOpcodeIds 99 = [870,869,864] := by
  unfold sourceOpcodeIds
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel

/-- Exact source-opcode candidates, including every fused logical root. -/
theorem opcode_inventory (kind : Kind) : sourceOpcodeIds (opcode kind) = candidateIds kind := by
  cases kind with
  | band => exact and_inventory
  | bor => exact or_inventory
  | bxor => exact xor_inventory

section ContextData
attribute [local semireducible] Isle.Aarch64.program

/-- Actual source context supplies the typed logical data without a selected
rule certificate or a new input condition. -/
theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y)) :
    ty.width ≤ 64 ∧ info.data = .data 152 2 [.data 151 (opcode kind) [], .values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have supported := inv.instE i info _ source clif
  have he : eTy ty = true := by
    cases kind <;> simpa [Kind.cop,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using supported
  have data := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨eTy_width he,?_,?_⟩
  · have shape : instData f (.binary kind.cop ty x y) =
        .ok (.data 152 2 [.data 151 (opcode kind) [], .values [x,y]]) := by
      cases kind <;> simp only [Kind.cop,opcode,instData,binaryOpcode,he,ite_true] <;> rfl
    exact Except.ok.inj (data.symm.trans shape)
  · rw [typed]; simp [ofClif_int_width (isInt_of_eTy he)]

end ContextData

/-- First-match selection is restricted by the original source opcode; no
chosen-root premise or default-only subset is introduced. -/
theorem selected_rule_ids {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) :
    selected.rule.id ∈ candidateIds kind := by
  obtain ⟨_,data,_⟩ := source_data inv kind source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rwa [opcode_inventory] at member

/-- Every actual retained logical record has one of the complete source-family
root IDs, derived from lowering and source facts rather than supplied by callers. -/
theorem record_selected_rule_ids {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (kind : Kind) {info : IInfo} {ty : Clif.Ty} {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.rules.getLast?.any (candidateIds kind).contains = true := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have member := selected_rule_ids (stock_lower_record_context run scope events).1 kind source clif receipt.selected
  rw [receipt.rules,receipt.selected.last_rule]
  simpa only [Option.any_some,List.contains_iff_mem] using member

/-- Complete sparse-ID Stock runs inhabit the dispatch boundary for all three
operators; the old explicit selected-root variants remain available. -/
theorem dispatch_witness (kind : Kind) :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent)
      (record : ScanRecord) (info : IInfo) (step : Step),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ event.ctx.insts[record.inst]? = some info ∧
      info.clif = some (.binary kind.cop .i64 7 31) ∧ record.output.step = some step ∧
      step.decision = .emitted ∧ step.rules.getLast?.any (candidateIds kind).contains = true := by
  obtain ⟨result,event,record,info,step,run,scope,events,records,source,clif,recorded,emitted,_,_⟩ :=
    stock_logical_selected_witness kind
  exact ⟨_,result,event,record,info,step,run,scope,events,records,source,clif,recorded,emitted,
    record_selected_rule_ids run scope events records kind source clif recorded emitted⟩

end Backend.Stock.Proof.LogicalComplete

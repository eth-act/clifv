import FV.Backend.Proof.StockBnotMatch
import FV.Backend.Proof.StockRootOpcodeMatch

namespace Backend.Stock.Proof.BnotComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def candidateIds : List RuleId := [834,833,828]
private theorem inventory : sourceOpcodeIds 100 = candidateIds := by
  unfold sourceOpcodeIds candidateIds
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-- Original NOT syntax bounds every actual first-match root, including fused
XOR and shifted operands, without a caller-selected root certificate. -/
theorem selected_rule_ids {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bnot ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) :
    selected.rule.id ∈ candidateIds := by
  obtain ⟨_,data,_⟩ := Bnot.stock_bnot_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rwa [inventory] at member

/-- The successful driver supplies selection and bindings for every retained NOT. -/
theorem record_selected_rule_ids {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {x : Nat}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.rules.getLast?.any candidateIds.contains = true := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have member := selected_rule_ids (stock_lower_record_context run scope events).1 source clif receipt.selected
  rw [receipt.rules,receipt.selected.last_rule]
  simpa only [Option.any_some,List.contains_iff_mem] using member
end Backend.Stock.Proof.BnotComplete

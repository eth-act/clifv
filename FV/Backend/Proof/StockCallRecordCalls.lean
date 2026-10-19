import FV.Backend.Proof.StockCallRootMatch
namespace Backend.Stock.Proof.CallRecordCallsDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open CallRhsCallsDraft CallRootMatchDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem call_data {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {ti fn : Nat} {info : IInfo} {args : List Nat}
    (slot : ctx.insts[ti]? = some info) (clif : info.clif = some (.call fn args)) :
    info.data = .data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)] := by
  have data := mapped.data ti info _ slot clif
  simp only [instData] at data
  cases external : f.extern? fn with
  | none => simp only [external] at data; cases data
  | some ext =>
    simp only [external] at data
    split at data
    · unfold instDataV opcodeV mkVariant variantIdx variantNames Isle.Aarch64.program at data
      change Except.ok (V.data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)]) = .ok info.data at data
      exact (Except.ok.inj data).symm
    · cases data

/-- Actual retained emitted direct-call records derive their selected helper
protocol from source context and first-match execution. The complete result
binder/copies and after-state remain those of the same real record receipt.
Mandatory call emission, GOT/indirect protocols, final-alias and value/world
composition remain separate whole-goal obligations. -/
theorem stock_lower_direct_call_record_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (colocated : ext.colocated = true)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ receipt : RecordSelection event record step,
      receipt.selected.rule = rule_lower_2508 ∧ step.rules.getLast? = some rule_lower_2508.id ∧
      receipt.selected.env = directEnv args ext.sig ext.name false ∧
      receipt.selected.matched = scanState record.input record.inst ∧ receipt.selected.matchTrace = #[] ∧
      DirectRootCalls program event.ctx args ext.sig ext.name false
        (scanState record.input record.inst) receipt.next #[] receipt.selected.rhsTrace receipt.out := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  have data := call_data mapped slot clif
  have extCtx : event.ctx.func.extern? fn = some ext := by rw [mapped.func]; exact external
  obtain ⟨chosen,environment,state,trace,calls⟩ := stock_selected_direct_call_rhs_calls slot data extCtx colocated receipt.selected
  refine ⟨receipt,chosen,?_,environment,state,trace,calls⟩
  rw [receipt.rules,receipt.selected.last_rule,chosen]
end Backend.Stock.Proof.CallRecordCallsDraft

import FV.Backend.Proof.StockAcquirePendingPointerHeld
import FV.Backend.Proof.StockGuardedRecordValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Landed fresh-register framing preserves the general pending capture relation.
Actual lowering derives demand monotonicity. The new emitted result remains bound normally. -/
theorem stock_lower_pending_fresh_record_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst} {z a d : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (output : step.results = [[.vreg d .int]]) (fresh : record.input.base.nextVreg ≤ d)
    {W : Type} {sem : ISem CV W} {fr : Clif.Frame} {ρ ρ' : Nat → CV} {w w' : W} {v : Clif.Val}
    {env : Clif.Env} {program : Clif.Program} {snapshots : List (SunkReadSnapshot event.ctx env program)}
    (held : PendingValuesHeld snapshots (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) fr (fun k => ρ (aliasNum result.final.alias k)))
    (defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))), ∀ key ∈ vdefs m,
        record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg)
    (executed : seqRun sem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w = some (.fall ρ' w'))
    (value : VHolds v (ρ' d)) :
    PendingValuesHeld snapshots (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi (j + 1)) (withValue fr z v)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  have demand : ∀ y,Demanded record.input y → Demanded record.output.state y := by
    intro y required
    have grows := stock_lower_record_demand_mono run events records recorded emitted y
    change record.input.demand[y]! ≠ 0 at required
    change record.output.state.demand[y]! ≠ 0
    omega
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records source clif
    results mapped recorded emitted output fresh).2
  have maps := (stock_lower_record_context run scope events).2.1
  intro y required notSuspended val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue, eq_self, ite_true] at lookup
    cases lookup
    exact ⟨a, mapped, by change VHolds v (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue, ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults, List.mem_singleton] using equal)
    obtain ⟨key, map, old⟩ := held y ⟨demand y required.1, before⟩ notSuspended val lookup
    have preserved := stock_lower_available_fresh_frame run scope dominated events records block statement current
      before (by rw [← maps]; exact map) defs executed
    exact ⟨key, map, by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [preserved]; exact old⟩


end Backend.Stock.Proof.Acquire810

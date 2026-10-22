import FV.Backend.Proof.StockGuardedRecordValues
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- A family may supply its proved fresh-write frame directly; all original guarded variants remain. -/
theorem stock_lower_fresh_record_values_of_frame {f : Clif.Function} {result : Result}
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
    {fr : Clif.Frame} {ρ ρ' : Nat → CV} {v : Clif.Val}
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (kept : ∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key)
    (value : VHolds v (ρ' d)) :
    ValuesHeld (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx (withValue fr z v)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records source clif
    results mapped recorded emitted output fresh).2
  have maps := (stock_lower_record_context run scope events).2.1
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds v (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have needed : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨needed,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records block statement current
      before (by rw [← maps]; exact map)
    refine ⟨key,map,?_⟩
    change VHolds val (ρ' (aliasNum result.final.alias key))
    rw [kept _ outside]
    exact old

end Backend.Stock.Proof

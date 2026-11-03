import FV.Backend.Proof.StockConstantRecordValues
import FV.Backend.Proof.StockFenceRecordOrigin
import FV.Backend.Proof.StockAcquirePendingValues

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem scan_next (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl
private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Actual constant execution preserves an arbitrary required set.
The whole lowering derives final aliases and register noninterference. -/
theorem stock_lower_constant_needed_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : stm.results = [x]) (infoResults : info.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
    {m n : Nat} (matchFuel : 2 ≤ m) (evalFuel : 50 ≤ n)
    {matched next : State} {matchTrace evalTrace : Array RuleId}
    {env : Isle.Interp.Env V} {out : V} {trace : List RuleId}
    (matchRun : (matchRule program (Stock.sem event.ctx) {} m rule_lower_53 [.inst record.inst]).run
      (scanState record.input record.inst, #[]) = .ok (some env, matched, matchTrace))
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} n rule_lower_53.rhs env).run
      (matched, matchTrace) = .ok (some out, next, evalTrace))
    (needed : Nat → Prop)
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (d : Nat),
      inst = .iconst ty imm ∧ aliasNum result.final.alias a = d ∧
      record.output.state.demand = record.input.demand ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV),
        ValuesHeld (fun y => needed y ∧
          y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr
            (fun k => ρ (aliasNum result.final.alias k)) →
        ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
          VHolds ⟨ty, imm⟩ (ρ' d) ∧
          ValuesHeld (fun y => needed y ∧
            y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
              (withValue fr x ⟨ty, imm⟩) (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨context, maps, sources⟩ := stock_lower_record_context run scope events
  obtain ⟨ty, imm, ms, d, bound, constant, output, binding, boundEq, shape, execution⟩ :=
    stock_iconst_available_resolved data_program context source clif rfl refines semantics
      matchFuel evalFuel matchRun evalRun block statement results infoResults mapped
  have evalRun' := evalRun
  have rootRun' := rootRun
  rw [output] at evalRun' rootRun'
  obtain ⟨selected, selectedRun, selectedState, selectedCode, selectedResults⟩ :=
    stock_iconst_emission_alias data_program source infoResults mapped rfl matchRun evalRun' rootRun'
  obtain ⟨actual, actualRun, actualScan⟩ := stock_emitted_scan
    (stock_fence_record_execute run events records) recorded emitted
  have same : selected = actual := Except.ok.inj (selectedRun.symm.trans actualRun)
  rw [← same] at actualScan
  have full : next = {scanState record.input record.inst with base := next.base} := by
    rw [stock_iconst_rhs_frame data_program event.ctx rfl evalRun,
      stock_iconst_match_frame data_program event.ctx rfl matchRun]
  have boundState : bound = selected.state := by
    rw [boundEq, full, selectedState]
  have code : record.output.emitted.toList = ms := by
    rw [actualScan]
    change selected.code.toList = ms
    rw [selectedCode]
    have boundBase : bound.base = next.base := by rw [boundEq]
    rw [← boundBase, shape.emitted, scan_empty, Array.empty_append, List.toList_toArray]
  have demands : record.output.state.demand = record.input.demand := by
    rw [actualScan]
    change selected.state.demand = record.input.demand
    rw [selectedState]
    exact scanState_demands _ _
  have aliasesBound := stock_lower_blockScanAliasBounds run event events record records
  have entry : (result.final.alias[a]?).join = some d := by
    rw [stock_lower_record_finalAliasEntry run ((fun h => scope.nonempty (List.length_eq_zero_iff.mp h)))
      dominated.ssa events records (x := x) (key := a) (sources _ _ _ source clif)
        (by rw [infoResults]; simp) (by rw [← maps]; exact mapped)]
    rw [actualScan]
    change (selected.state.alias[a]?).join = some d
    rw [selectedState, aliasStep_get]
    simp only [ite_true]
  have target : aliasNum result.final.alias d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by have := shape.res; omega)]
    rfl
  have resolved : aliasNum result.final.alias a = d :=
    (stock_lower_alias_step run scope dominated entry).trans target
  refine ⟨ty, imm, d, constant, resolved, demands, ?_⟩
  intro fr ρ held
  obtain ⟨ρ', executed, value, installed⟩ := execution result.final.alias aliasesBound ρ
  have heldAfter := installed needed fr held resolved (by
    intro y key _ available map _
    have excluded := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current available (by rw [← maps]; exact map)
    rw [scan_next, boundState] at *
    simpa only [actualScan, Emission.scan] using excluded)
  exact ⟨ρ', by simpa only [code] using executed, value, heldAfter⟩


end Backend.Stock.Proof

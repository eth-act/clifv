import FV.Backend.Proof.StockMemoryIntegerDispatch
import FV.Backend.Proof.StockMemoryOffsetEightLoad
import FV.Backend.Proof.StockMemoryLoad
import FV.Backend.Proof.StockGuardedRecordValues

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

private theorem record_execute {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) :
    scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input =
      .ok record.output := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq] at records ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record records

private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl
private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Actual retained load-root receipts determine emitted code, its fresh result,
the allocation endpoint and installed final alias. No code/binding certificate
is supplied separately. -/
private theorem record_full (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {z a x nreg n : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load width.sourceTy flags x 8)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none)
    (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n+120) width.root.rhs
      (env3 (.value x) (.op (.memFlags flags)) (.int 8))).run
        (scanState record.input record.inst,#[]) = .ok (some out,next,evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out,next,trace)) :
    step.results = [[.vreg record.input.base.nextVreg .int]] ∧
    record.output.emitted = #[.load width.loadOp (.vreg record.input.base.nextVreg .int)
      (.unsignedOffset (.vreg nreg .int) 8) flags] ∧
    record.output.state.base.nextVreg = record.input.base.nextVreg + 1 ∧
    aliasNum result.final.alias a = record.input.base.nextVreg ∧
    record.output.state.demand = (record.input.mark x).demand := by
  obtain ⟨computed,actual⟩ := stock_parameter_integer_load_eight_rhs data_program width event.ctx (cfg := {}) rfl parameter pointer flags
    (scanState record.input record.inst) #[] n
  have equal := Except.ok.inj (evalRun.symm.trans actual)
  simp only [Prod.mk.injEq] at equal
  have outEq := equal.1
  have nextEq := equal.2.1
  have installed := bindResults_virtual event.ctx next [(z,a,record.input.base.nextVreg)] (by
    intro p member
    have equal := List.mem_singleton.mp member
    subst p
    exact mapped)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at installed
  have outEq' : out = .regsVec [[.vreg record.input.base.nextVreg .int]] := by
    simpa only [LState.fresh,scan_frontier,Option.some.injEq] using outEq
  rw [outEq'] at rootRun
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  have emitter : emitInstruction event.ctx record.inst (scanState record.input record.inst) =
      .ok ⟨{next with alias := aliasStep next.alias (a,record.input.base.nextVreg)},
        next.base.emitted,[[.vreg record.input.base.nextVreg .int]],trace⟩ := by
    unfold emitInstruction
    rw [infoBang,rootRun]
    simp only [bind,Except.bind]
    simp [results,installed]
  obtain ⟨actualEmission,actualRun,actualScan⟩ := stock_emitted_scan (record_execute run events records) recorded emitted
  have same := Except.ok.inj (actualRun.symm.trans emitter)
  subst actualEmission
  have stepRecorded := recorded
  rw [actualScan] at stepRecorded
  have stepEq := Option.some.inj stepRecorded.symm
  have outputs : step.results = [[.vreg record.input.base.nextVreg .int]] := by rw [stepEq]
  refine ⟨outputs,?_,?_,(stock_lower_record_fresh_result run scope dominated.ssa events records source clif
    results mapped recorded emitted outputs (Nat.le_refl _)).2,?_⟩
  · rw [actualScan,nextEq]
    change ((scanState record.input record.inst).base.fresh .int).2.emitted.push _ = _
    simp [LState.fresh,scan_empty,scan_frontier]
  · rw [actualScan,nextEq]
    change ((scanState record.input record.inst).base.fresh .int).2.nextVreg = _
    simp only [LState.fresh,scan_frontier]

  · rw [actualScan,nextEq]
    change ((scanState record.input record.inst).mark x).demand = (record.input.mark x).demand
    simp only [State.mark,scanState_demands]

/-- Actual offset8 records derive code, fresh allocation and final result binding internally. -/
theorem stock_lower_integer_load_eight_record (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load width.sourceTy flags x 8)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none)
    (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.results = [[.vreg record.input.base.nextVreg .int]] ∧
    record.output.emitted = #[.load width.loadOp (.vreg record.input.base.nextVreg .int)
      (.unsignedOffset (.vreg nreg .int) 8) flags] ∧
    record.output.state.base.nextVreg = record.input.base.nextVreg + 1 ∧
    aliasNum result.final.alias a = record.input.base.nextVreg ∧
    record.output.state.demand = (record.input.mark x).demand := by
  have selected := stock_lower_integer_load_selected_id_offset width run scope events records
    source clif recorded emitted
  obtain ⟨little,out,next,trace,rhsTrace,rootRun,evalRun⟩ :=
    stock_lower_integer_load_selected_receipts_offset width run scope events records source clif
      recorded emitted selected
  exact record_full width run scope dominated events records source clif results mapped parameter pointer
    recorded emitted (n := 999879) evalRun rootRun

end Backend.Stock.Memory.IntegerRoots

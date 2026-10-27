import FV.Backend.Proof.StockMemoryLoadSelection
import FV.Backend.Proof.StockMemoryLoad
import FV.Backend.Proof.StockGuardedRecordValues

namespace Backend.Stock.Memory
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
theorem stock_lower_parameter_load_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {z a x nreg n : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load .i32 flags x 0)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none)
    (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n+120) rule_lower_2610.rhs
      (env3 (.value x) (.op (.memFlags flags)) (.int 0))).run
        (scanState record.input record.inst,#[]) = .ok (some out,next,evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out,next,trace)) :
    step.results = [[.vreg record.input.base.nextVreg .int]] ∧
    record.output.emitted = #[.load .uload32 (.vreg record.input.base.nextVreg .int)
      (.unsignedOffset (.vreg nreg .int) 0) flags] ∧
    record.output.state.base.nextVreg = record.input.base.nextVreg + 1 ∧
    aliasNum result.final.alias a = record.input.base.nextVreg := by
  obtain ⟨computed,actual⟩ := stock_parameter_load_rhs data_program event.ctx (cfg := {}) rfl parameter pointer flags
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
    results mapped recorded emitted outputs (Nat.le_refl _)).2⟩
  · rw [actualScan,nextEq]
    change ((scanState record.input record.inst).base.fresh .int).2.emitted.push _ = _
    simp [LState.fresh,scan_empty,scan_frontier]
  · rw [actualScan,nextEq]
    change ((scanState record.input record.inst).base.fresh .int).2.nextVreg = _
    simp only [LState.fresh,scan_frontier]

/-- A retained parameter-load record executes on the original source memory and
transfers the source-available demanded set. Code, fresh definitions, binding,
final aliases and demand preservation are derived from the actual whole run. -/
theorem stock_lower_parameter_load_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x nreg n : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load .i32 flags x 0)) (results : info.results = [z])
    (statementResults : stm.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none)
    (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n+120) rule_lower_2610.rhs
      (env3 (.value x) (.op (.memFlags flags)) (.int 0))).run
        (scanState record.input record.inst,#[]) = .ok (some out,next,evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out,next,trace))
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState} {v : Clif.Val}
    (memory : MR fr.slots cm w) (dfg : DFGCons event.ctx fr)
    (operands : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) x)
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (little : flags.endianness ≠ some .big)
    (evaluated : Clif.evalInst fr cm (.load .load .i32 flags x 0) = .ok ([v],cm')) :
    ∃ ρ' w',seqRun isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') ∧
      SameWorld F w' w ∧ MR fr.slots cm' w' ∧
      VHolds v (ρ' record.input.base.nextVreg) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx (withValue fr z v)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨outputs,code,upper,finalAlias⟩ := stock_lower_parameter_load_record run scope dominated events records
    source clif results mapped parameter pointer recorded emitted evalRun rootRun
  have bound : result.final.alias.size ≤ record.input.base.nextVreg := by
    simpa only [scan_frontier] using stock_lower_blockScanAliasBounds run event events record records
  have fixed : aliasNum result.final.alias record.input.base.nextVreg = record.input.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bound]
    rfl
  have resolved : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [.load .uload32 (.vreg record.input.base.nextVreg .int)
        (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0) flags] := by
    rw [code]
    change [MInst.load .uload32
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg record.input.base.nextVreg .int))
      (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg nreg .int)) 0) flags] = _
    rw [resolve_vreg,resolve_vreg]
    change [MInst.load .uload32 (.vreg (aliasNum result.final.alias record.input.base.nextVreg) .int)
      (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0) flags] = _
    rw [fixed]
  have pointerTy := (stock_lower_record_context run scope events).1.addr64 _ _ _ x source clif rfl
  have address := mapped_unsigned_address (sb := sb) (bytes := 4) (w := w) operands pointer dfg pointerTy
    (off := 0) (by decide)
  obtain ⟨ρ',w',executed,same,memory',values,keep⟩ := load_source_seqRun stable memorySem memoryOk memory
    (ρ := ρ) (d := record.input.base.nextVreg)
    (am := .unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0)
    (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩)
    (aop := .uload32) (by decide) rfl rfl (by decide) little
    (fun pv hpv => by simpa [amUses,amVregs,AMode.regs,amodeAddr,LoadOp.bytes] using address pv hpv) evaluated
  have value := values v (by simp)
  have actualRun : seqRun isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') := by
    rwa [resolved]
  have defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),∀ key ∈ vdefs m,
      record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
    rw [resolved]
    intro m member key defined
    have equal := List.mem_singleton.mp member
    subst m
    change key ∈ [record.input.base.nextVreg] at defined
    have equal := List.mem_singleton.mp defined
    subst key
    rw [upper]
    exact ⟨Nat.le_refl _,Nat.lt_succ_self _⟩
  exact ⟨ρ',w',actualRun,same,memory',value,
    stock_lower_fresh_record_values_auto_demand run scope dominated events records block statement current
      source clif results statementResults mapped recorded emitted outputs (Nat.le_refl _) held defs actualRun value⟩

end Backend.Stock.Memory

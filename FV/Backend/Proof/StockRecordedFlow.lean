import FV.Backend.Proof.StockSelectedBindingFlow
import FV.Backend.Proof.StockEmittedScan
import FV.Backend.Proof.StockRecordFinalAlias

/-! Alias origins of emitted source records retained by the actual whole driver.
Core metadata, record transitions, allocation facts and final transport are derived. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
attribute [local irreducible] Isle.Aarch64.program emitInstruction

private theorem allocation_trans {a b c : State} (ab : AllocationLe a b) (bc : AllocationLe b c) :
    AllocationLe a c := ⟨Nat.le_trans ab.1 bc.1, bc.2.trans ab.2⟩

private theorem normalization (input : State) (i : Nat) :
    (scanState input i).base.nextVreg = input.base.nextVreg ∧
      (scanState input i).tryRegs = input.tryRegs ∧
      (scanState input i).alias = input.alias := by
  unfold scanState
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem record_origin {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {input : State} {output : BlockScan} {initial : State}
    (allocation : AllocationLe initial input)
    (run : scanBlock ctx block ti branch indices input = .ok output) :
    ∀ record ∈ output.records, AllocationLe initial record.input ∧
      scanInstruction ctx block record.inst ti branch record.input = .ok record.output := by
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨allocation, head⟩
    · exact ih (allocation_trans allocation (stock_scan_allocationLe head)) record member

private theorem term_placeholder {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) :
    ctx.insts[blockStart f bi + b.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
  obtain ⟨original, st, old, spec, view⟩ := buildCtx_source build
  have model := congrArg Ctx.insts (buildCtx_model old).1
  simp only [ctxModel, blockFold, Array.empty_append] at model
  rw [view.insts, model]
  simpa only [List.getElem?_toArray, blockStart_eq, placeholder] using instsOf_term f f.blocks bi b block

private theorem emitted_record_origins {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {block ti : Nat} {branch : Bool} {indices : List Nat} {input : State} {output : BlockScan}
    (allocation : AllocationLe initial input) (data : V)
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (run : scanBlock { Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]! }
      block ti branch indices input = .ok output)
    {record : ScanRecord} (member : record ∈ output.records) {step : Step}
    (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[record.inst]? = some info) (original : info.clif = some inst)
    (nonempty : info.results ≠ []) :
    ∀ x key target, ctx.valueReg? x = some (.vreg key .int) →
      (record.output.state.alias[key]?).join = some target →
      (record.input.alias[key]?).join = some target ∨
      (record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
        (∃ y, Prov ctx record.inst y ∧ ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ initial.tryRegs[ti]!.1 ++ initial.tryRegs[ti]!.2 ∧
          target < initial.base.nextVreg ∧ ∀ y, ctx.valueReg? y ≠ some (.vreg target .int)) := by
  obtain ⟨recordAllocation, scanned⟩ := record_origin allocation run record member
  have normal := normalization record.input record.inst
  have beforeAllocation : AllocationLe initial (scanState record.input record.inst) := by
    exact ⟨by rw [normal.1]; exact recordAllocation.1, normal.2.1.trans recordAllocation.2⟩
  have slots : (scanState record.input record.inst).tryRegs = input.tryRegs :=
    beforeAllocation.2.trans allocation.2.symm
  have distinct : record.inst ≠ ti := by
    intro same
    rw [same, placeholder] at source
    cases source
    cases original
  obtain ⟨emission, actual, outputEq⟩ := stock_emitted_scan scanned recorded emitted
  have selected : emitInstruction
      { Driver.termCtx ctx ti data with tryRegs := (scanState record.input record.inst).tryRegs[ti]! }
      record.inst (scanState record.input record.inst) = .ok emission := by
    rw [slots]
    exact actual
  have origins := stock_selected_emitInstruction_sourceAliasOrigins build scope placeholder distinct
    data source original nonempty beforeAllocation selected
  intro x key target map entry
  have emissionEntry : (emission.state.alias[key]?).join = some target := by
    simpa only [outputEq, Emission.scan] using entry
  have classified := origins x key target map emissionEntry
  simpa only [normal.1, normal.2.2, beforeAllocation.2, outputEq, Emission.scan] using classified

/-- Every final alias of an actually emitted source definition is inherited
from its actual record input or targets a fresh/source-provenanced/exact reserved
register. The whole driver supplies its core, real record transition, reservation
state and record-to-final alias transport; no caller edge-origin premise is used. -/
theorem stock_lower_emitted_record_finalAliasOrigins {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (nonempty : f.blocks.length ≠ 0) (ssa : (valueDefs f).Nodup)
    {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x key : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : result.ctx.insts[record.inst]? = some info) (original : info.clif = some inst)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int)) :
    ∀ target, (result.final.alias[key]?).join = some target →
      (record.input.alias[key]?).join = some target ∨
      (record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
        (∃ y, Prov result.ctx record.inst y ∧ result.ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
            result.initial.tryRegs[event.termInst]!.2 ∧
          target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int)) := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run eventMem
  obtain ⟨labelBound, _⟩ := stock_backward_suffix_split parts
  have lookup : result.order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos result.order.nodes label labelBound] at node
    simp only [Array.getElem?_eq_getElem labelBound, node]
  have projected : bi ∈ stockOriginals result.order.nodes := by
    unfold stockOriginals
    exact List.mem_filterMap.mpr ⟨.original bi,
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩
  have biBound := (stock_blockOrder_originals_nodup ordered nonempty).2 bi projected
  have block : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨originalCtx, st, old, spec, view⟩ := buildCtx_source build
  have range := spec.ranges bi f.blocks[bi] block
  have rangeEq : ranges[bi]! = (blockStart f bi, blockStart f bi + f.blocks[bi].body.length + 1) := by
    simp only [getElem!_def, range]
  have initialBound : starting.state.alias.size ≤ result.initial.base.nextVreg ∧
      result.initial.base.nextVreg ≤ starting.state.base.nextVreg ∧
      starting.state.tryRegs = result.initial.tryRegs := by
    rw [initial]
    obtain ⟨ctx0, st0, requests, _, _, allocated⟩ := buildCtx_allocation build
    have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) allocated
    change result.initial = _ at state
    rw [state]
    exact ⟨Nat.zero_le _, Nat.le_refl _, rfl⟩
  have beforeBound := stock_lowerNodes_allocationBounds build initialBound prefixRun
  have inputAllocation := stock_lowerBlockCore_scanAllocationBounds build beforeBound coreRun
  obtain ⟨coreState, scanCtx, scanBlockId, scanTerm, scanIndices, scanRun⟩ :=
    stock_lowerBlockCore_scanOrigin coreRun
  have placeholder : result.ctx.insts[ranges[bi]!.2 - 1]? = some ⟨.op .unit, [], [], none⟩ := by
    rw [rangeEq]
    simpa only [Nat.add_sub_cancel] using term_placeholder build block
  have normalized : scanBlock
      { Driver.termCtx result.ctx (ranges[bi]!.2 - 1) data with
        tryRegs := core.scan.input.tryRegs[ranges[bi]!.2 - 1]! }
      bi (ranges[bi]!.2 - 1) core.scan.isBranch core.scan.indices core.scan.input = .ok core.scan.output := by
    simpa only [scanCtx, scanBlockId, scanTerm, inputAllocation.2, beforeBound.2.2] using scanRun
  have member : record ∈ core.scan.output.records := by simpa only [eventEq] using recordMem
  have nonemptyResults : info.results ≠ [] := by intro empty; rw [empty] at defines; cases defines
  have origins := emitted_record_origins build scope inputAllocation data placeholder normalized
    member recorded emitted source original nonemptyResults x key
  have entryEq := stock_lower_record_finalAliasEntry run nonempty ssa eventMem recordMem source defines mapped
  intro target entry
  have classification := origins target mapped (entryEq.symm.trans entry)
  simpa only [eventEq, scanTerm] using classification

/-- Source-provenanced final alias targets from actual emitted records are
available at an actual source boundary; fresh and exact reservations stay separate. -/
theorem stock_lower_emitted_record_finalAliasAvailable {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (nonempty : f.blocks.length ≠ 0) {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x key bi j n : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : result.ctx.insts[record.inst]? = some info) (original : info.clif = some inst)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (available : n ∈ availOf f (availIn f result.ctx) bi j)
    (definition : result.ctx.defInst? n = some record.inst) :
    ∀ target, (result.final.alias[key]?).join = some target →
      (record.input.alias[key]?).join = some target ∨
      (record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
        (∃ y, y ∈ availOf f (availIn f result.ctx) bi j ∧
          result.ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
            result.initial.tryRegs[event.termInst]!.2 ∧
          target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int)) := by
  intro target entry
  rcases stock_lower_emitted_record_finalAliasOrigins run scope nonempty dominated.ssa eventMem
      recordMem recorded emitted source original defines mapped target entry with
      old | fresh | ⟨y, reached, register⟩ | reserved
  · exact .inl old
  · exact .inr (.inl fresh)
  · obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
        label, bi', data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem
    exact .inr (.inr (.inl ⟨y,
      stock_available_provenance build dominated available definition reached, register⟩))
  · exact .inr (.inr (.inr reserved))

/-- Actual whole-driver source aliases have fresh, source-provenanced or exact
reserved origins. Inherited entries are excluded by the derived input absence. -/
theorem stock_lower_emitted_record_finalAliasOrigins_noInherited {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (nonempty : f.blocks.length ≠ 0) (ssa : (valueDefs f).Nodup)
    {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x key : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : result.ctx.insts[record.inst]? = some info) (original : info.clif = some inst)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int)) :
    ∀ target, (result.final.alias[key]?).join = some target →
      (record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
        (∃ y, Prov result.ctx record.inst y ∧ result.ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
            result.initial.tryRegs[event.termInst]!.2 ∧
          target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int)) := by
  intro target entry
  have absent := stock_lower_record_inputNoAlias run nonempty ssa eventMem recordMem
    source defines mapped
  rcases stock_lower_emitted_record_finalAliasOrigins run scope nonempty ssa eventMem
      recordMem recorded emitted source original defines mapped target entry with old | origins
  · rw [absent] at old; cases old
  · exact origins

/-- Actual whole-driver source aliases have fresh, source-provenanced or exact
reserved origins. Inherited entries are excluded by the derived input absence. -/
theorem stock_lower_emitted_record_finalAliasAvailable_noInherited {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (nonempty : f.blocks.length ≠ 0) {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x key bi j n : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : result.ctx.insts[record.inst]? = some info) (original : info.clif = some inst)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (available : n ∈ availOf f (availIn f result.ctx) bi j)
    (definition : result.ctx.defInst? n = some record.inst) :
    ∀ target, (result.final.alias[key]?).join = some target →
      (record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
        (∃ y, y ∈ availOf f (availIn f result.ctx) bi j ∧
          result.ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
            result.initial.tryRegs[event.termInst]!.2 ∧
          target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int)) := by
  intro target entry
  have absent := stock_lower_record_inputNoAlias run nonempty dominated.ssa eventMem recordMem
    source defines mapped
  rcases stock_lower_emitted_record_finalAliasAvailable run scope dominated nonempty eventMem
      recordMem recorded emitted source original defines mapped available definition target entry with old | origins
  · rw [absent] at old; cases old
  · exact origins

attribute [local semireducible] Isle.Aarch64.program
private def recordedSignature : Clif.Signature := {
  returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV }
private def recordedFunction : Clif.Function := {
  name := "emitted_record_alias"
  sig := recordedSignature
  externs := [(0, { name := "callee", sig := recordedSignature })]
  blocks := [{ id := 0, params := [], body := [⟨[0], .call 0 []⟩], term := .ret [0] }] }
private def recordedInfo := infoOf recordedFunction ⟨[0], .call 0 []⟩
private def recordedBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx recordedFunction).toOption.getD (sinkCtx, #[], sinkState)
private def recordedCall := Stock.lower recordedFunction
private theorem recorded_build : Stock.buildCtx recordedFunction = .ok recordedBuilt := rfl
private theorem recorded_scope : LowerScope recordedFunction := lowerScope_of (by decide +kernel)
private theorem recorded_ssa : (valueDefs recordedFunction).Nodup := by decide
private theorem recorded_nonempty : recordedFunction.blocks.length ≠ 0 := by decide
set_option maxRecDepth 20000 in
private theorem recorded_success : recordedCall.isOk = true := by decide +kernel
set_option maxRecDepth 20000 in
private theorem recorded_observed : recordedCall.toOption.map (fun r =>
    (r.ctx.valueReg? 0,
      r.blockScans.toList.any (fun e => e.output.records.any (fun record =>
        record.inst == 0 && record.output.step.any (fun step => step.decision == .emitted))),
      (r.final.alias[192]?).join.isSome)) = some (some (.vreg 192 .int), true, true) := by
  decide +kernel

private def recordedOriginal : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx recordedFunction).toOption.getD (sinkCtx, #[], sinkState.base)
private theorem recorded_original_build : Backend.buildCtx recordedFunction = .ok recordedOriginal := rfl
private theorem recorded_original_defs : recordedOriginal.1.valDef = #[some 0] := rfl
private theorem recorded_original_args (x : Nat) : defArgs recordedOriginal.1 x = [] := by
  cases x with
  | zero => simp [defArgs, Ctx.defInst?, recorded_original_defs]; rfl
  | succ x => simp [defArgs, Ctx.defInst?, recorded_original_defs]
private theorem recorded_dominated : Dominated recordedFunction := by
  constructor
  · exact recorded_ssa
  · intro ctx ranges st build bi B block
    cases bi with
    | zero =>
      simp [recordedFunction] at block
      subst B
      constructor
      · intro j stmt lookup y member
        cases j with
        | zero => simp at lookup; subst stmt; simp [Backend.Proof.Driver.instArgs] at member
        | succ j => simp at lookup
      · intro y member
        change y ∈ [0] at member
        simp only [List.mem_singleton] at member
        subst y
        change 0 ∈ ((availIn recordedFunction ctx).getD 0 [] ++ [0]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    | succ bi => simp [recordedFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    rw [recorded_original_build] at build
    cases build
    change y ∈ defArgs recordedOriginal.1 x at member
    rw [recorded_original_args] at member
    cases member
private theorem recorded_available (ctx : Ctx) :
    (0 : Nat) ∈ availOf recordedFunction (availIn recordedFunction ctx) 0 1 := by
  change 0 ∈ ((availIn recordedFunction ctx).getD 0 [] ++ [0]).filter
    (fun x => decide (x ∉ ([] : List Nat)))
  simp

/-- A successful whole-driver direct-call/return emits source0, retains its
real record and transports a nonempty installed alias into the final array. -/
theorem stock_lower_emitted_record_finalAliasOrigins_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (target : Nat),
      LowerScope recordedFunction ∧ Dominated recordedFunction ∧
      recordedFunction.blocks.length ≠ 0 ∧ Stock.lower recordedFunction = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.inst = 0 ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      result.ctx.insts[record.inst]? = some recordedInfo ∧
      result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧ result.ctx.defInst? 0 = some record.inst ∧
      (result.final.alias[192]?).join = some target ∧
      ((record.input.alias[192]?).join = some target ∨
        (record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
          (∃ y, Prov result.ctx record.inst y ∧ result.ctx.valueReg? y = some (.vreg target .int)) ∨
          ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
              result.initial.tryRegs[event.termInst]!.2 ∧ target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int))) := by
  cases call : recordedCall with
  | error e =>
    have success := recorded_success
    simp only [call, Except.isOk] at success
    cases success
  | ok result =>
    have observation := recorded_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observation
    obtain ⟨event, eventMem, record, recordMem, which, step, recorded, emitted⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true]
        using observation.2.1 : ∃ event ∈ result.blockScans.toList,
          ∃ record ∈ event.output.records, record.inst = 0 ∧
            ∃ step, record.output.step = some step ∧ step.decision = .emitted)
    have actual : Stock.lower recordedFunction = .ok result := call
    obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
      label, bi, data, core, build, _⟩ := stock_lower_blockScanOrigin actual eventMem
    rw [recorded_build] at build
    have ctxEq : result.ctx = recordedBuilt.1 :=
      (congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.1) (Except.ok.inj build)).symm
    have source : result.ctx.insts[record.inst]? = some recordedInfo := by rw [which, ctxEq]; rfl
    have definition : result.ctx.defInst? 0 = some record.inst := by rw [which, ctxEq]; rfl
    cases entry : (result.final.alias[192]?).join with
    | none => rw [entry] at observation; cases observation.2.2
    | some target =>
      refine ⟨result, event, record, step, target, recorded_scope, recorded_dominated, recorded_nonempty,
        actual, eventMem, recordMem, which, recorded, emitted, source, observation.1, definition, entry, ?_⟩
      exact stock_lower_emitted_record_finalAliasOrigins actual recorded_scope recorded_nonempty
        recorded_ssa eventMem recordMem recorded emitted source (by rfl) (by decide) observation.1 target entry

/-- The same actual emitted record and final alias inhabit the availability
classification at source0's post-body boundary with actual dominance. -/
theorem stock_lower_emitted_record_finalAliasAvailable_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (target : Nat),
      LowerScope recordedFunction ∧ Dominated recordedFunction ∧
      recordedFunction.blocks.length ≠ 0 ∧ Stock.lower recordedFunction = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      result.ctx.insts[record.inst]? = some recordedInfo ∧ result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      result.ctx.defInst? 0 = some record.inst ∧
      (0 : Nat) ∈ availOf recordedFunction (availIn recordedFunction result.ctx) 0 1 ∧
      (result.final.alias[192]?).join = some target ∧
      ((record.input.alias[192]?).join = some target ∨
        (record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
          (∃ y, y ∈ availOf recordedFunction (availIn recordedFunction result.ctx) 0 1 ∧
            result.ctx.valueReg? y = some (.vreg target .int)) ∨
          ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
              result.initial.tryRegs[event.termInst]!.2 ∧ target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int))) := by
  obtain ⟨result, event, record, step, target, scope, dominated, nonempty, actual, eventMem,
    recordMem, which, recorded, emitted, source, mapped, definition, entry, _⟩ :=
    stock_lower_emitted_record_finalAliasOrigins_witness
  refine ⟨result, event, record, step, target, scope, dominated, nonempty, actual, eventMem,
    recordMem, recorded, emitted, source, mapped, definition, recorded_available result.ctx, entry, ?_⟩
  exact stock_lower_emitted_record_finalAliasAvailable actual scope dominated nonempty eventMem
    recordMem recorded emitted source (by rfl) (by decide) mapped (recorded_available result.ctx)
    definition target entry

/-- The real emitted direct-call record and nonempty final alias also witness
classification with inherited entries eliminated. -/
theorem stock_lower_emitted_record_finalAliasOrigins_noInherited_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (target : Nat),
      LowerScope recordedFunction ∧ Dominated recordedFunction ∧
      recordedFunction.blocks.length ≠ 0 ∧ Stock.lower recordedFunction = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.inst = 0 ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      result.ctx.insts[record.inst]? = some recordedInfo ∧
      result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧ result.ctx.defInst? 0 = some record.inst ∧
      (result.final.alias[192]?).join = some target ∧
      ((record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
          (∃ y, Prov result.ctx record.inst y ∧ result.ctx.valueReg? y = some (.vreg target .int)) ∨
          ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
              result.initial.tryRegs[event.termInst]!.2 ∧ target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int))) := by
  obtain ⟨result, event, record, step, target, scope, dominated, nonempty, actual, eventMem,
    recordMem, which, recorded, emitted, source, mapped, definition, entry, _⟩ :=
    stock_lower_emitted_record_finalAliasOrigins_witness
  refine ⟨result, event, record, step, target, scope, dominated, nonempty, actual, eventMem,
    recordMem, which, recorded, emitted, source, mapped, definition, entry, ?_⟩
  exact stock_lower_emitted_record_finalAliasOrigins_noInherited actual scope nonempty dominated.ssa
    eventMem recordMem recorded emitted source (by rfl) (by decide) mapped target entry

/-- The real emitted direct-call record and nonempty final alias also witness
classification with inherited entries eliminated. -/
theorem stock_lower_emitted_record_finalAliasAvailable_noInherited_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (target : Nat),
      LowerScope recordedFunction ∧ Dominated recordedFunction ∧
      recordedFunction.blocks.length ≠ 0 ∧ Stock.lower recordedFunction = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      result.ctx.insts[record.inst]? = some recordedInfo ∧ result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      result.ctx.defInst? 0 = some record.inst ∧
      (0 : Nat) ∈ availOf recordedFunction (availIn recordedFunction result.ctx) 0 1 ∧
      (result.final.alias[192]?).join = some target ∧
      ((record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg) ∨
          (∃ y, y ∈ availOf recordedFunction (availIn recordedFunction result.ctx) 0 1 ∧
            result.ctx.valueReg? y = some (.vreg target .int)) ∨
          ((.vreg target .int) ∈ result.initial.tryRegs[event.termInst]!.1 ++
              result.initial.tryRegs[event.termInst]!.2 ∧ target < result.initial.base.nextVreg ∧
            ∀ y, result.ctx.valueReg? y ≠ some (.vreg target .int))) := by
  obtain ⟨result, event, record, step, target, scope, dominated, nonempty, actual, eventMem,
    recordMem, recorded, emitted, source, mapped, definition, available, entry, _⟩ :=
    stock_lower_emitted_record_finalAliasAvailable_witness
  refine ⟨result, event, record, step, target, scope, dominated, nonempty, actual, eventMem,
    recordMem, recorded, emitted, source, mapped, definition, available, entry, ?_⟩
  exact stock_lower_emitted_record_finalAliasAvailable_noInherited actual scope dominated nonempty
    eventMem recordMem recorded emitted source (by rfl) (by decide) mapped available definition target entry

end Backend.Stock.Proof

module

public import FV.Backend.Proof.StockCoverageBlock
public import FV.Backend.Proof.StockSourceOrder
public import FV.Backend.Proof.StockRecordedFlow

@[expose] public section

/-! Empty remembered definitions through the actual node loop and whole Stock driver.
Source scope is unchanged; no caller-supplied metadata or acceptance certificate. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The actual stored block scans have empty remembered definitions at every
scan/record boundary. This is a proof invariant, not a replay certificate. -/
def RecordsEmpty (events : Array BlockScanEvent) : Prop :=
  ∀ event ∈ events.toList, NoOpportunity event.input ∧
    ∀ record ∈ event.output.records, NoOpportunity record.input ∧ NoOpportunity record.output.state

section Preservation
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore assembleOriginalBlock

private theorem original_bound {f : Clif.Function} (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order) {label bi : Nat}
    (inside : label < order.nodes.size) (node : order.nodes[label]! = .original bi) :
    bi < f.blocks.length := by
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have lookup : order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos order.nodes label inside] at node
    simp only [Array.getElem?_eq_getElem inside, node]
  apply (stock_blockOrder_originals_nodup ordered nonempty).2 bi
  unfold stockOriginals
  apply List.mem_filterMap.mpr
  exact ⟨.original bi, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩

/-- Every actual original or critical-edge node in the constructed order
preserves empty remembered definitions. Actual blocks/ranges are derived. -/
private theorem node_invariant {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order)
    {params : List Nat} {label : Nat} (inside : label < order.nodes.size)
    {input output : DriverState} (empty : NoOpportunity input.state)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    NoOpportunity output.state ∧ (RecordsEmpty input.blockScans → RecordsEmpty output.blockScans) := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases edge : branchArgs ctx input.state pred k with
    | error e => simp only [edge, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args, next⟩
      simp only [edge, bind, Except.bind, pure, Except.pure] at run
      cases run
      refine ⟨?_, fun old => old⟩
      intro v
      rw [branchArgs_noOpportunity edge]
      exact empty v
  | original bi =>
    have valid := original_bound scope ordered inside node
    let b := f.blocks[bi]!
    have block : f.blocks[bi]? = some b := by
      simp only [b, getElem!_pos f.blocks bi valid, List.getElem?_eq_getElem valid]
    obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
    let start := blockStart f bi
    let stop := start + b.body.length + 1
    have rangeRun : ranges[bi]? = some (start, stop) := spec.ranges bi b block
    have range : ranges[bi]! = (start, stop) := by simp only [getElem!_def, rangeRun, Option.getD_some]
    let reject : Bool := (match b.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
        let data ← blockData f b.term
        if reject then throw "sret parameter is not an entry-block parameter"
        let lowered ← lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state
        let assembled ← assembleOriginalBlock ctx f b bi label order.successors[label]!
          lowered.outgoing params lowered.state.uses lowered.code
        pure {recordCore input lowered bi stop with
          blocks := input.blocks.set! label assembled,
          edgeArgs := input.edgeArgs.set! label lowered.outgoing}) := by
      unfold lowerNode
      simp only [node]
      rw [range]
      dsimp only [blockData, reject, b]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : blockData f b.term with
    | error e => simp only [dataRun, bind, Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun, bind, Except.bind] at run
      split at run
      · cases run
      · cases core : lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state with
        | error e => simp only [core] at run; cases run
        | ok lowered =>
          simp only [core] at run
          cases assembled : assembleOriginalBlock ctx f b bi label order.successors[label]!
              lowered.outgoing params lowered.state.uses lowered.code with
          | error e => simp only [assembled] at run; cases run
          | ok finished =>
            simp only [assembled, pure, Except.pure] at run
            cases run
            refine ⟨blockCore_noOpportunity build scope block rangeRun dataRun empty core, ?_⟩
            intro old event member
            change event ∈ (input.blockScans.push lowered.scan).toList at member
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
            rcases member with member | rfl
            · exact old event member
            · exact blockCore_records_noOpportunity build scope block rangeRun dataRun empty core

/- The state-only theorem keeps its original interface. -/
theorem node_noOpportunity {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order)
    {params : List Nat} {label : Nat} (inside : label < order.nodes.size)
    {input output : DriverState} (empty : NoOpportunity input.state)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    NoOpportunity output.state :=
  (node_invariant build scope ordered inside empty run).1

private theorem traversal_invariant {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order) {params labels : List Nat}
    (inside : ∀ label ∈ labels, label < order.nodes.size)
    {input output : DriverState} (empty : NoOpportunity input.state)
    (old : RecordsEmpty input.blockScans)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    NoOpportunity output.state ∧ RecordsEmpty output.blockScans := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨empty, old⟩
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      have preserved := node_invariant build scope ordered (inside label (List.mem_cons_self)) empty call
      exact ih (fun k member => inside k (List.mem_cons_of_mem label member)) preserved.1 (preserved.2 old) run

/-- The actual complete Stock driver never creates remembered definitions on
the existing source scope. All node metadata and loop bounds are derived. -/
private theorem lower_invariant {f : Clif.Function} (scope : LowerScope f) {result : Result}
    (run : Stock.lower f = .ok result) :
    NoOpportunity result.final ∧ RecordsEmpty result.blockScans := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  change NoOpportunity driver.state ∧ RecordsEmpty driver.blockScans
  have initial := buildCtx_noOpportunity (ctx := built.1) (ranges := built.2.1)
    (initial := built.2.2) hbuild
  apply traversal_invariant (ctx := built.1) (ranges := built.2.1) (initial := built.2.2)
    hbuild scope horder ?_ initial (by simp [RecordsEmpty]) hdriver
  intro label member
  simpa only [Array.toList_reverse, Array.toList_range, List.mem_reverse, List.mem_range] using member
theorem lower_noOpportunity {f : Clif.Function} (scope : LowerScope f) {result : Result}
    (run : Stock.lower f = .ok result) : NoOpportunity result.final :=
  (lower_invariant scope run).1

/-- Every actual block scan retained by successful whole Stock lowering has
empty remembered state at its input and both endpoints of every source record. -/
theorem lower_records_noOpportunity {f : Clif.Function} (scope : LowerScope f) {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (member : event ∈ result.blockScans.toList) :
    NoOpportunity event.input ∧
      ∀ record ∈ event.output.records, NoOpportunity record.input ∧ NoOpportunity record.output.state :=
  (lower_invariant scope run).2 event member

end Preservation

/-- Reuse the real emitted-call whole-driver witness, with its original source
scope and emitted record, to inhabit the complete invariant. -/
theorem lower_noOpportunity_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step),
      LowerScope f ∧ Stock.lower f = .ok result ∧ f.blocks.length ≠ 0 ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ NoOpportunity result.final := by
  obtain ⟨result, event, record, step, target, scope, dominated, nonempty, run,
    events, records, index, recorded, emitted, rest⟩ :=
    stock_lower_emitted_record_finalAliasOrigins_noInherited_witness
  exact ⟨_, result, event, record, step, scope, run, nonempty, events, records, recorded, emitted,
    lower_noOpportunity scope run⟩

private def criticalFunction : Clif.Function := {
  name := "stock_critical_edge_invariant"
  sig := {params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩]}
  blocks := [
    {id := 0, params := [(0, .i64)], term := .brif 0 ⟨1, [0]⟩ ⟨1, [0]⟩},
    {id := 1, params := [(1, .i64)], term := .ret [1]}] }
private def criticalBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx criticalFunction).toOption.getD (sinkCtx, #[], sinkState)
private def criticalOrder : Order :=
  ⟨#[.original 0, .edge 0 0 1, .edge 0 1 1, .original 1],
    #[#[1, 2], #[3], #[3], #[]]⟩
private def criticalInput : DriverState := {
  state := criticalBuilt.2.2
  blocks := Array.replicate 4 default
  edgeArgs := Array.replicate 4 #[]
  schedule := #[], scans := #[], blockScans := #[], rules := #[] }
private def criticalOutput : DriverState := {criticalInput with
  state := criticalInput.state.mark 0
  blocks := criticalInput.blocks.set! 1 {label := 1, insts := #[.jump 3], branchArgs := #[.vreg 192 .int]}
  edgeArgs := criticalInput.edgeArgs.set! 1 #[#[.vreg 192 .int]] }
private theorem critical_build : Stock.buildCtx criticalFunction = .ok criticalBuilt := rfl
private theorem critical_scope : LowerScope criticalFunction := lowerScope_of (by decide +kernel)
private theorem critical_order : blockOrder criticalFunction = .ok criticalOrder := by cbv
private theorem critical_run : lowerNode criticalBuilt.1 criticalBuilt.2.1 criticalOrder
    criticalFunction [8] 1 criticalInput = .ok criticalOutput := rfl

/-- The actual constructed order contains a critical-edge node that collects a
real register argument, marks its demand, and emits its jump without ISLE. -/
theorem node_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (order : Order) (input output : DriverState),
      Stock.buildCtx f = .ok (ctx, ranges, initial) ∧ LowerScope f ∧ blockOrder f = .ok order ∧
      1 < order.nodes.size ∧ order.nodes[1]? = some (.edge 0 0 1) ∧ NoOpportunity input.state ∧
      lowerNode ctx ranges order f [8] 1 input = .ok output ∧
      output.blocks[1]!.insts = #[.jump 3] ∧ output.blocks[1]!.branchArgs = #[.vreg 192 .int] ∧
      input.state.demand[0]! = 0 ∧ output.state.demand[0]! = 1 ∧ NoOpportunity output.state := by
  have empty : NoOpportunity criticalInput.state := buildCtx_noOpportunity critical_build
  exact ⟨criticalFunction, criticalBuilt.1, criticalBuilt.2.1, criticalBuilt.2.2, criticalOrder,
    criticalInput, criticalOutput, critical_build, critical_scope, critical_order, by decide, rfl,
    empty, critical_run, rfl, rfl, rfl, rfl,
    node_noOpportunity critical_build critical_scope critical_order (by decide) empty critical_run⟩

/-- Reuse the actual emitted-call record to inhabit all whole-driver record
premises, including its recorded selection step. -/
theorem lower_records_noOpportunity_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step),
      LowerScope f ∧ Stock.lower f = .ok result ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      NoOpportunity event.input ∧ NoOpportunity record.input ∧ NoOpportunity record.output.state := by
  obtain ⟨f, result, event, record, step, scope, run, nonempty, events, records, recorded, emitted, final⟩ :=
    lower_noOpportunity_witness
  have all := lower_records_noOpportunity scope run events
  exact ⟨f, result, event, record, step, scope, run, events, records, recorded, emitted,
    all.1, all.2 record records⟩

end Backend.Stock.Proof.Coverage

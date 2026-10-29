module

public import FV.Backend.Proof.StockTerminalBlocks
public import FV.Backend.Proof.StockCoverageDriver
public import FV.Backend.Proof.StockSourceOrder
public import FV.Backend.Proof.StockRecordedFlow

@[expose] public section

/-! Empty remembered definitions through the actual node loop and whole Stock driver.
Source scope is unchanged; no caller-supplied metadata or acceptance certificate. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Every retained scan boundary respects the global original empty-CLIF slots. -/
def RecordsTerminalUnsunk (ctx : Ctx) (events : Array BlockScanEvent) : Prop :=
  ∀ event ∈ events.toList,TerminalUnsunk ctx event.input ∧
    ∀ record ∈ event.output.records,TerminalUnsunk ctx record.input ∧ TerminalUnsunk ctx record.output.state

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
    {input output : DriverState} (empty : NoOpportunity input.state) (safe : TerminalUnsunk ctx input.state)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    TerminalUnsunk ctx output.state ∧ (RecordsTerminalUnsunk ctx input.blockScans → RecordsTerminalUnsunk ctx output.blockScans) := by
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
      intro i slot
      rw [stock_branchArgs_sunk edge]
      exact safe i slot
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
            refine ⟨(stock_blockCore_terminal_unsunk build scope block rangeRun dataRun empty safe core).1, ?_⟩
            intro old event member
            change event ∈ (input.blockScans.push lowered.scan).toList at member
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
            rcases member with member | rfl
            · exact old event member
            · exact (stock_blockCore_terminal_unsunk build scope block rangeRun dataRun empty safe core).2

private theorem traversal_invariant {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order) {params labels : List Nat}
    (inside : ∀ label ∈ labels, label < order.nodes.size)
    {input output : DriverState} (empty : NoOpportunity input.state) (safe : TerminalUnsunk ctx input.state)
    (old : RecordsTerminalUnsunk ctx input.blockScans)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    TerminalUnsunk ctx output.state ∧ RecordsTerminalUnsunk ctx output.blockScans := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨safe, old⟩
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      have preserved := node_invariant build scope ordered (inside label (List.mem_cons_self)) empty safe call
      have nextEmpty := node_noOpportunity build scope ordered (inside label (List.mem_cons_self)) empty call
      exact ih (fun k member => inside k (List.mem_cons_of_mem label member)) nextEmpty preserved.1 (preserved.2 old) run

/-- The actual complete Stock driver never creates remembered definitions on
the existing source scope. All node metadata and loop bounds are derived. -/
private theorem lower_invariant {f : Clif.Function} (scope : LowerScope f) {result : Result}
    (run : Stock.lower f = .ok result) :
    TerminalUnsunk result.ctx result.final ∧ RecordsTerminalUnsunk result.ctx result.blockScans := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  change TerminalUnsunk built.1 driver.state ∧ RecordsTerminalUnsunk built.1 driver.blockScans
  have empty := buildCtx_noOpportunity (ctx := built.1) (ranges := built.2.1)
    (initial := built.2.2) hbuild
  have initial := stock_buildCtx_terminal_unsunk hbuild
  apply traversal_invariant (ctx := built.1) (ranges := built.2.1) (initial := built.2.2)
    hbuild scope horder ?_ empty initial (by simp [RecordsTerminalUnsunk]) hdriver
  intro label member
  simpa only [Array.toList_reverse, Array.toList_range, List.mem_reverse, List.mem_range] using member
theorem stock_lower_terminal_unsunk {f : Clif.Function} (scope : LowerScope f) {result : Result}
    (run : Stock.lower f = .ok result) : TerminalUnsunk result.ctx result.final :=
  (lower_invariant scope run).1

/-- Every actual block scan retained by successful whole Stock lowering has
empty remembered state at its input and both endpoints of every source record. -/
theorem stock_lower_records_terminal_unsunk {f : Clif.Function} (scope : LowerScope f) {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (member : event ∈ result.blockScans.toList) :
    TerminalUnsunk result.ctx event.input ∧
      ∀ record ∈ event.output.records,TerminalUnsunk result.ctx record.input ∧ TerminalUnsunk result.ctx record.output.state :=
  (lower_invariant scope run).2 event member

end Preservation
end Backend.Stock.Proof.Coverage

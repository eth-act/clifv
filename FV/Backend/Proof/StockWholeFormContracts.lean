import FV.Backend.Proof.StockEntryFormContracts
import FV.Backend.Proof.StockCoverageDriver

namespace Backend.Stock.Proof.Coverage.WholeFormsDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.Coverage.CoreDraft Backend.Stock.Proof.Coverage.EntryDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore assembleOriginalBlock branchArgs

private def BlocksCovered (blocks : Array VBlock) : Prop :=
  ∀ block ∈ blocks.toList,∀ i ∈ block.insts.toList,Covered i = true

private theorem set_covered {blocks : Array VBlock} {label : Nat} {block : VBlock}
    (old : BlocksCovered blocks) (fresh : ∀ i ∈ block.insts.toList,Covered i = true) :
    BlocksCovered (blocks.set! label block) := by
  intro vb member
  obtain ⟨j,found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at found
  split at found
  · split at found
    · cases found; exact fresh
    · cases found
  · exact old vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))

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

private theorem node_invariant {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order)
    {params : List Nat} {label : Nat} (inside : label < order.nodes.size)
    {input output : DriverState} (old : BlocksCovered input.blocks)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    BlocksCovered output.blocks := by
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
      apply set_covered old
      intro i member
      simp only [Array.toList_push,Array.toList_empty,List.mem_singleton] at member
      subst i
      rfl
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
            apply set_covered old
            exact stock_assemble_form_coverage (buildCtx_mappedInv scope build).valueReg
              (fun i member => (stock_blockCore_form_coverage build scope block rangeRun dataRun core i member).1)
              assembled

private theorem traversal_invariant {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order) {params labels : List Nat}
    (inside : ∀ label ∈ labels, label < order.nodes.size)
    {input output : DriverState} (old : BlocksCovered input.blocks)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    BlocksCovered output.blocks := by
  induction labels generalizing input with
  | nil => cases run; exact old
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      have preserved := node_invariant build scope ordered (inside label (List.mem_cons_self)) old call
      exact ih (fun k member => inside k (List.mem_cons_of_mem label member)) preserved run

private theorem map_covered {blocks : Array VBlock} (old : BlocksCovered blocks)
    (aliases : Array (Option Nat)) :
    BlocksCovered (blocks.map fun b => {b with
      insts := b.insts.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))
      params := b.params.map (Backend.lowerFunction.resolve aliases (aliases.size+1))
      branchArgs := b.branchArgs.map (Backend.lowerFunction.resolve aliases (aliases.size+1))}) := by
  intro block member i inside
  obtain ⟨raw,retained,rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using member)
  obtain ⟨inst,emitted,rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using inside)
  obtain ⟨gn,hg⟩ := resolve_vrenaming aliases (aliases.size+1)
  rw [covered_mapRegs hg]
  exact old raw retained inst emitted

/-- Every instruction of actual returned Stock VCode has a covered form and
ordinary spill-static validity, under the original source scope. All traversal,
critical-edge jumps, entry materialization, scans, branch rewrites, assembly
and final alias transport are derived from the successful actual driver. -/
theorem stock_lower_form_coverage {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    ∀ block ∈ result.code.blocks.toList,∀ i ∈ block.insts.toList,
      Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : BlocksCovered (Array.replicate order.nodes.size (default : VBlock)) := by
    intro block member i inside
    have same : block = default := (List.mem_replicate.mp
      (show block ∈ List.replicate order.nodes.size (default : VBlock) from
        by simpa only [Array.toList_replicate] using member)).2
    subst block
    cases inside
  have raw := traversal_invariant (ctx := built.1) (ranges := built.2.1) (initial := built.2.2)
    hbuild scope horder (fun label member => by
      simpa only [Array.toList_reverse,Array.toList_range,List.mem_reverse,List.mem_range] using member)
    initial hdriver
  have resolved := map_covered raw driver.state.alias
  intro block member i inside
  have form := resolved block member i inside
  refine ⟨form,fun ordinary => spillInstOk_of_formOk (ctx := default) ?_⟩
  simpa only [Covered,ordinary,Bool.false_or] using form

/-- The actual Stock producer supplies the existing allocation/semantic
consumer's FormsCovered interface from original inputs. -/
theorem stock_lower_formsCovered {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ctx : FnCtx) :
    FormsCovered ctx result.code := by
  intro b block k i placed emitted
  have form := (stock_lower_form_coverage run scope block
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? placed)) i
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? emitted))).1
  have irrelevant : FormOk ctx i = FormOk default i := by
    unfold FormOk
    rfl
  rw [irrelevant]
  exact (Bool.or_eq_true _ _).mp form

end Backend.Stock.Proof.Coverage.WholeFormsDraft

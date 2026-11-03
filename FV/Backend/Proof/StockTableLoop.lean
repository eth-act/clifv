import FV.Backend.Proof.StockTableCarry
import FV.Backend.Proof.StockOriginalEntryPrelude
import FV.Backend.Proof.StockParameterPrelude

/-! `br_table` blocks in the loop induction (#140, CB-14c).

The pieces of the loop induction for a `br_table` block, as for a `brif` block:

* a nonentry block has no prelude (`table_nonentry_prelude`);
* the retained emission is not empty (`TableBodySpec.emission_size`), so the entry prelude is the
  prelude of an original entry core (`table_entry_prelude`);
* every selected successor carries its definition carry, which the edge cover relates to the
  block's (`table_carry_successors`, `table_carry_trap_successors`);
* when no successor takes arguments, every outgoing vector of the actual core is empty
  (`TableBodySpec.outgoing_empty`), which the legacy single-vector interface needs. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.TableBranch Backend.Stock.Proof.LoopCarry
  Backend.Stock.Proof.ParameterLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem assemble_nonentry_code {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (nonentry : bi ≠ 0)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.insts = code := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  simp only [show (bi == 0) = false from by simp [nonentry],Bool.false_eq_true,ite_false] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; rfl

/-- A nonentry `br_table` block has no prelude. -/
theorem table_nonentry_prelude {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp) (nonentry : bi ≠ 0) :
    spec.preludeCode.size = 0 := by
  have code := assemble_nonentry_code nonentry spec.assembled
  have sizes := congrArg Array.size (spec.rawCode.symm.trans code)
  simp only [Array.size_append] at sizes
  omega

/-- The retained `br_table` emission of an `i32` index with at most 4096 successors has three
instructions. -/
theorem TableBodySpec.emission_size {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brTable x dc tbl)
    (typeX : result.ctx.valueType? x = some (.int 32))
    (small : result.order.successors[label]!.size ≤ 4096) :
    spec.origin.emission.code.size = 3 := by
  have slot := spec.table_slot block termShape
  have typeHere : {Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
      tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!}.valueType? x = some (.int 32) := typeX
  have labelsSmall : result.order.successors[label]!.toList.length ≤ 4096 := by
    simpa only [Array.length_toList] using small
  obtain ⟨d,ts,r,_,_,_,_,emitted,_⟩ := table_named_code slot typeHere labelsSmall spec.origin.call
  rw [spec.origin.emitted,emitted]
  simp [tableCode]

/-- **The entry prelude of a `br_table` block.** The retained emission is not empty, so the core
code is not empty, and the entry prelude is that of an original entry core. -/
theorem table_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b 0 0 x dc tbl isem MR env cp)
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w',Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨0,0,entrySeed spec.core.scan.ctx fr,w⟩)
      (.run ⟨0,spec.preludeCode.size,ρ',w'⟩) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
        spec.core.scan.output.state (0,fr,cm) ρ' w' ∧
      ValuesHeld (fun _ => True) spec.core.scan.ctx fr
        (fun key => ρ' (aliasNum result.final.alias key)) ∧ SameWorld F w' w := by
  have block : f.blocks[0]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have count := table_successor_count run scope tag block termShape
  have size := spec.emission_size block termShape typeX (by omega)
  have nonempty : 0 < spec.core.code.size := by
    rw [spec.bodyCode]
    simp only [Array.size_append]
    omega
  let entry : Control.EntryCoreSpec f result b := {
    ranges := spec.ranges
    params := spec.params
    core := spec.core
    raw := spec.raw
    preludeCode := spec.preludeCode
    build := spec.build
    sizes := spec.sizes
    assembled := spec.assembled
    events := spec.events
    block := block
    rawCode := spec.rawCode
    placed := spec.placed
    nonempty := nonempty }
  exact Control.original_entry_prelude run scope dominated entry entered driver memorySem stable memory arguments

/-- The successor family of a `br_table` block of the loop class, entry or not, for returns: each
selected successor carries its definition carry, which the edge cover relates to the block's. -/
theorem table_carry_successors {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {vals : List Clif.Val} {cm : Clif.Mem} {bound : Nat}
    (continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
      result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
      next ∈ result.blockScans.toList → next.block = tl →
      CarryReturnsBelow f result targetLabel tl targetBlock next isem MR env cp bound) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state (defCarry f result bi)
        isem MR env cp vals cm bound) := by
  intro index bc selected
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  obtain ⟨tl,targetLabel,targetBlock,lookup,found,source,targetTag,targetNonentry⟩ :=
    selected_loop_target run scope tag block selected
  obtain ⟨next,nextEvent,nextBlock⟩ := original_event run targetTag
  have cover := stock_defCarry_cover run scope dominated.ssa spec.events spec.split
    (by rw [spec.atBlock]; exact tag) nextEvent (by rw [nextBlock]; exact targetTag)
    (by rw [nextBlock]; exact source) (by rw [nextBlock,spec.atBlock]; exact selected_succIdx block selected lookup)
  rw [nextBlock,spec.atBlock] at cover
  exact ⟨{
    index := tl
    targetLabel := targetLabel
    block := targetBlock
    event := next
    carried := defCarry f result tl
    lookup := lookup
    found := found
    tag := targetTag
    member := nextEvent
    atBlock := nextBlock
    available := defCarry_available
    cover := cover
    returns := fun left lower t ρ' w' =>
      continued targetTag source targetNonentry nextEvent nextBlock left lower t vals cm ρ' w' }⟩

/-- The successor family of a `br_table` block of the loop class, entry or not, for first
traps. -/
theorem table_carry_trap_successors {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {code : Clif.TrapCode} {bound : Nat}
    (continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
      result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
      next ∈ result.blockScans.toList → next.block = tl →
      CarryTrapsBelow f result targetLabel tl targetBlock next isem MR env cp bound) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state (defCarry f result bi)
        isem MR env cp code bound) := by
  intro index bc selected
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  obtain ⟨tl,targetLabel,targetBlock,lookup,found,source,targetTag,targetNonentry⟩ :=
    selected_loop_target run scope tag block selected
  obtain ⟨next,nextEvent,nextBlock⟩ := original_event run targetTag
  have cover := stock_defCarry_cover run scope dominated.ssa spec.events spec.split
    (by rw [spec.atBlock]; exact tag) nextEvent (by rw [nextBlock]; exact targetTag)
    (by rw [nextBlock]; exact source) (by rw [nextBlock,spec.atBlock]; exact selected_succIdx block selected lookup)
  rw [nextBlock,spec.atBlock] at cover
  exact ⟨{
    index := tl
    targetLabel := targetLabel
    block := targetBlock
    event := next
    carried := defCarry f result tl
    lookup := lookup
    found := found
    tag := targetTag
    member := nextEvent
    atBlock := nextBlock
    available := defCarry_available
    cover := cover
    traps := fun left lower t ρ' w' =>
      continued targetTag source targetNonentry nextEvent nextBlock left lower t code ρ' w' }⟩

/-- An outgoing collection over successors whose arguments are all empty pushes only empty
vectors. -/
private theorem collect_empty {ctx : Ctx} {f : Clif.Function} (func : ctx.func = f)
    {bi : Nat} {b : Clif.Block} (source : f.blocks[bi]? = some b) {order : Order} :
    ∀ (pairs : List (Nat × Nat)) (input next : State) (acc acc' : Array (Array Reg)),
    (∀ p ∈ pairs,∃ bc,(dests b.term)[p.2]? = some bc ∧ bc.args = []) →
    (∀ v ∈ acc,v = #[]) →
    pairs.foldlM (outgoingStep ctx order bi) (input,acc) = .ok (next,acc') →
    ∀ v ∈ acc',v = #[] := by
  intro pairs
  induction pairs with
  | nil =>
    intro input next acc acc' _ empty run
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨-,rfl⟩ := run
    exact empty
  | cons p rest ih =>
    intro input next acc acc' every empty run
    obtain ⟨label,j⟩ := p
    rw [List.foldlM_cons] at run
    cases step : outgoingStep ctx order bi (input,acc) (label,j) with
    | error message => simp only [step,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨middle,accm⟩ := pair
      simp only [step,bind,Except.bind] at run
      obtain ⟨bc,selected,noArgs⟩ := every (label,j) (List.mem_cons_self ..)
      apply ih middle next accm acc' (fun q member => every q (List.mem_cons_of_mem _ member)) _ run
      unfold outgoingStep at step
      cases node : order.nodes[label]! with
      | edge pred k target =>
        simp only [node,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at step
        obtain ⟨-,rfl⟩ := step
        intro v member
        rcases Array.mem_push.mp member with old | new
        · exact empty v old
        · exact new
      | original t =>
        simp only [node] at step
        cases call : branchArgs ctx input bi j with
        | error message => simp only [call,bind,Except.bind] at step; cases step
        | ok result =>
          obtain ⟨args,state⟩ := result
          simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at step
          obtain ⟨-,rfl⟩ := step
          have mapping := stock_branchArgs_selected_mapping func source selected call
          rw [noArgs] at mapping
          simp only [List.mapM_nil,Option.pure_def,Option.some.injEq] at mapping
          have argsEmpty : args = #[] := Array.toList_inj.mp mapping.symm
          intro v member
          rcases Array.mem_push.mp member with old | new
          · exact empty v old
          · rw [new,argsEmpty]

/-- **The outgoing vectors of a `br_table` block whose successors take no arguments are empty.** -/
theorem TableBodySpec.outgoing_empty {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (emptyArgs : ∀ bc ∈ dc :: tbl,bc.args = []) :
    ∀ v ∈ spec.core.outgoing,v = #[] := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have func := (buildCtx_mappedInv scope spec.build).func
  obtain ⟨emission,afterEdges,_,_,outgoing,_,_,_,_⟩ := table_core_calls termShape spec.coreRun
  unfold collectOutgoing at outgoing
  have count := table_successor_count run scope tag block termShape
  have every : ∀ p ∈ result.order.successors[label]!.zipIdx.toList,
      ∃ bc,(dests b.term)[p.2]? = some bc ∧ bc.args = [] := by
    intro p inside
    rw [Array.toList_zipIdx] at inside
    have found := List.mk_mem_zipIdx_iff_getElem?.mp (show (p.1,p.2) ∈ _ from inside)
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [Array.length_toList,count] at bound
    refine ⟨(dc :: tbl)[p.2]'(by simpa using bound),?_,emptyArgs _ (List.getElem_mem _)⟩
    simp only [termShape,dests]
    exact List.getElem?_eq_getElem _
  exact collect_empty func block _ _ _ _ _ every (fun v member => by simp at member) outgoing

end Backend.Stock.Proof.ConditionalValues

import FV.Backend.Proof.StockLoopCarryBounded

/-! One carry set per block for every loop CFG (#140, T7b-3, for T7b-4 and T7b-5).

`headerCarry` covers the back edges into one header. A composition over all blocks needs one
carry set per block that covers every edge. `defCarry f result bi` holds the values available at
the entry of block `bi`, other than its parameters, that the terminator scan of their defining
block demands: their definitions were emitted and their registers are live there. `defCarry_cover`
shows that it covers every source edge, forward or back, given `DefBefore`: a block that defines
a value inherited by `t` has a smaller label than `t` in Stock's block order. The entry block
carries nothing (`defCarry_entry`), so the composition can start from `GuardedScanRel`. -/

namespace Backend.Stock.Proof.LoopCarry
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The terminator scan of block `d` demands `x`. -/
def TermDemanded (result : Result) (d x : Nat) : Prop :=
  ∀ event ∈ result.blockScans.toList,event.block = d →
    ∀ term ∈ event.output.records.head?,Demanded term.output.state x

/-- The definition carry of block `bi`: the values available at its entry, other than its
parameters, that the terminator scan of each of their defining blocks demands. -/
def defCarry (f : Clif.Function) (result : Result) (bi x : Nat) : Prop :=
  x ∈ availOf f (availIn f result.ctx) bi 0 ∧ x ∉ parsOf f bi ∧
    ∀ d,x ∈ parsOf f d ∨ x ∈ defsOf f d → TermDemanded result d x

/-- Definitions precede the blocks that inherit them in Stock's block order: a block that
defines a value (as a parameter or a body result) inherited by block `t` has a smaller label.
In a reverse postorder such a block dominates `t`, so it comes first (#140, T7b-4). -/
def DefBefore (f : Clif.Function) (result : Result) : Prop :=
  ∀ (d t ld lt x : Nat),result.order.nodes[ld]? = some (.original d) →
    result.order.nodes[lt]? = some (.original t) →
    x ∈ (availIn f result.ctx).getD t [] → x ∈ parsOf f d ∨ x ∈ defsOf f d → ld < lt

theorem defCarry_available {f : Clif.Function} {result : Result} {bi : Nat} :
    ∀ x,defCarry f result bi x → x ∈ availOf f (availIn f result.ctx) bi 0 :=
  fun _ carried => carried.1

/-- No value is inherited by the entry block, so it carries nothing. -/
theorem defCarry_entry {f : Clif.Function} {result : Result} {entry : Clif.Block}
    (block : f.blocks[0]? = some entry) (x : Nat) : ¬ defCarry f result 0 x := by
  rintro ⟨available,notParameter,_⟩
  obtain ⟨present,_⟩ := (mem_av block).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · exact notParameter (by rw [parsOf_of block]; exact parameter)
  · have bound := ((inFix_fixOk (f := f) (ctx := result.ctx) (gn := id)).cand 0 x incoming).1
    omega
  · omega

/-- The entry block's `GuardedScanRel` is its `CarryRel` of the definition carry. -/
theorem defCarry_entry_rel {f : Clif.Function} {result : Result} {entry : Clif.Block}
    (block : f.blocks[0]? = some entry) {event : BlockScanEvent} (atEntry : event.block = 0)
    {MR : MemRelT} {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result event.ctx event.block MR event.output.state (0,fr,cm) ρ w) :
    Inherited.CarryRel f result event.ctx event.block MR (defCarry f result event.block)
      event.output.state (0,fr,cm) ρ w := by
  refine ⟨held,?_⟩
  intro x carried
  rw [atEntry] at carried
  exact absurd carried (defCarry_entry block x)

private theorem event_label {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (member : event ∈ result.blockScans.toList) :
    ∃ label : Nat,result.order.nodes[label]? = some (.original event.block) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,build,ordered,
    initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run member
  have bound := (stock_backward_suffix_split parts).1
  have atBlock : event.block = bi := by rw [eventEq]; exact (stock_lowerBlockCore_scanOrigin coreRun).2.2.1
  refine ⟨label,?_⟩
  rw [getElem!_pos result.order.nodes label bound] at node
  rw [atBlock,Array.getElem?_eq_getElem bound,node]

/-- A block whose labels are all below `lt` demands at its terminator every value that the entry
of the block at `lt` demands. -/
private theorem term_demanded_of_label {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    {lt : Nat} (nextTag : result.order.nodes[lt]? = some (.original next.block))
    {d x : Nat} (earlier : ∀ ld,result.order.nodes[ld]? = some (.original d) → ld < lt)
    (demanded : Demanded next.output.state x) : TermDemanded result d x := by
  intro event member atBlock term head
  obtain ⟨b,term',body,split⟩ := stock_lower_body_scan_split run scope member
  rw [split.records] at head
  have same : term' = term := Option.some.inj head
  subst same
  obtain ⟨ld,tag⟩ := event_label run member
  have lower := earlier ld (by rw [← atBlock]; exact tag)
  have demand := CfgDemand.ordered_scan_demand_of_labels run scope (Array.getElem?_eq_some_iff.mp nextTag).1
    lower (by simp only [getElem!_def,nextTag,Option.getD_some]) (by simp only [getElem!_def,tag,Option.getD_some])
    nextEvent member split
  unfold Demanded at demanded ⊢
  have le := demand x
  omega

/-- The definition carry covers every source edge `P → T`, forward or back: each value that `T`
needs at entry and does not receive as an argument is demanded by `P`'s terminator scan (if `P`
defines it) or carried by `P` (if `P` inherits it). -/
theorem defCarry_cover {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (before : DefBefore f result)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {label : Nat} (tag : result.order.nodes[label]? = some (.original event.block))
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    {targetLabel : Nat} (targetTag : result.order.nodes[targetLabel]? = some (.original next.block))
    {targetBlock : Clif.Block} (destination : f.blocks[next.block]? = some targetBlock)
    (successor : next.block ∈ succIdx f event.block) :
    EdgeCover f result next.block (targetBlock.params.map (·.1)) next.output.state
      (defCarry f result next.block) term.output.state (defCarry f result event.block) := by
  intro x available notParameter needed
  have fixed := inFix_fixOk (f := f) (ctx := result.ctx) (gn := id)
  have incoming : x ∈ (availIn f result.ctx).getD next.block [] := by
    obtain ⟨present,_⟩ := (mem_av destination).mp available
    rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
    · exact False.elim (notParameter parameter)
    · exact incoming
    · omega
  have defsBefore : ∀ d,x ∈ parsOf f d ∨ x ∈ defsOf f d →
      ∀ ld,result.order.nodes[ld]? = some (.original d) → ld < targetLabel :=
    fun d defines ld dTag => before d next.block ld targetLabel x dTag targetTag incoming defines
  have local' : x ∈ parsOf f event.block ∨ x ∈ defsOf f event.block → Demanded term.output.state x := by
    intro defines
    rcases needed with demanded | carried
    · have demand := CfgDemand.ordered_scan_demand_of_labels run scope
        (Array.getElem?_eq_some_iff.mp targetTag).1 (defsBefore event.block defines label tag)
        (by simp only [getElem!_def,targetTag,Option.getD_some])
        (by simp only [getElem!_def,tag,Option.getD_some]) nextEvent events split
      unfold Demanded at demanded ⊢
      have le := demand x
      omega
    · exact carried.2.2 event.block defines event events rfl term (by rw [split.records]; rfl)
  rcases fixed.out next.block x incoming event.block successor with parameter | defined | inherited
  · exact Or.inl (local' (Or.inl parameter))
  · exact Or.inl (local' (Or.inr defined))
  · right
    have notLocal : x ∉ defsOf f event.block := by
      intro defined
      have := before event.block event.block label label x tag tag inherited (Or.inr defined)
      omega
    refine ⟨?_,(fixed.cand event.block x inherited).2.2.2.2.1,?_⟩
    · apply (mem_av split.block).mpr
      refine ⟨Or.inr (Or.inl inherited),?_⟩
      rintro ⟨j,stm,_,statement,results⟩
      exact notLocal (mem_defsOf.mpr ⟨b,j,stm,split.block,statement,results⟩)
    · intro d defines
      rcases needed with demanded | carried
      · exact term_demanded_of_label run scope nextEvent targetTag (defsBefore d defines) demanded
      · exact carried.2.2 d defines

end Backend.Stock.Proof.LoopCarry

import FV.Backend.Proof.StockPerEdgeReturnContract
import FV.Backend.Proof.StockConditionalSourceReturn
import FV.Backend.Proof.StockConditionalSuccessor
import FV.Backend.Proof.StockSelectedRouteExecution
import FV.Backend.Proof.StockSourceOrder

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- An actual selected original successor with a proved return continuation.
This is the induction hypothesis of CFG composition, not an input certificate. -/
structure SuccessorReturn (f : Clif.Function) (result : Result) (label : Nat)
    (bc : Clif.BlockCall) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (vals : List Clif.Val) (cm : Clif.Mem) where
  index : Nat
  targetLabel : Nat
  block : Clif.Block
  event : BlockScanEvent
  lookup : blockIdx? f bc.block = some index
  found : f.block? bc.block = some block
  tag : result.order.nodes[targetLabel]? = some (.original index)
  member : event ∈ result.blockScans.toList
  atBlock : event.block = index
  forward : label < targetLabel
  returns : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = block.body → s.frame.term = block.term →
    SourceDefinedAt f result.ctx index 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
    GuardedScanRel f result event.ctx event.block MR event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨targetLabel,0,ρ,w⟩ (.returned vals cm)

/-- Whole-body conditional return composition, including actual selected
copies and synthetic jumps. Empty outgoing vectors identify the first compatible
class; broader argument-value proofs can reuse the selected-successor API. -/
theorem ConditionalBodySpec.returning_empty_parameter_at
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
    (emptyArgs : yes.args = [] ∧ no.args = [])
    {vals : List Clif.Val} {cm : Clif.Mem}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm))
    {fuel : Nat} {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_parameter_core run scope dominated family refines driver stable
      termShape parameter conditionTy remaining atTerm defined returned held
  let bc := if Clif.Sem.truthy value.bits then yes else no
  let choice := if Clif.Sem.truthy value.bits then 0 else 1
  have selected : (dests b.term)[choice]? = some bc := by
    cases truth : Clif.Sem.truthy value.bits <;> simp [dests,termShape,choice,bc,truth]
  obtain ⟨next⟩ := successors choice bc selected
  have nextBlock : next.event.block = sourceTargetIndex f bc := by
    simpa only [sourceTargetIndex,next.lookup,Option.getD_some] using next.atBlock
  have arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx t.frame
      (fun key => regs (aliasNum result.final.alias key)) := by
    intro x member
    have noArgs : bc.args = [] := by
      dsimp only [bc]
      split <;> simp_all only [emptyArgs.1,emptyArgs.2]
    rw [noArgs] at member
    cases member
  obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
    spec.selected_successor_guarded run scope dominated tag selected next.member nextBlock
      (by simpa only [next.atBlock] using next.tag) next.forward post
      (by simpa only [spec.atBlock] using tDefined) crossed arguments
  have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
  subst tl
  have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
    (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
  subst targetLabel
  obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
  have destinationEq : destination = next.block := by
    rw [post.1] at found
    exact Option.some.inj (found.symm.trans next.found)
  have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
  have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
  have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
  have finished := next.returns left {t with frame := fr} ρnext endWorld
    nextHeld.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have segment : SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs resolve)
      params := spec.raw.params.map resolve
      branchArgs := spec.raw.branchArgs.map resolve}
      spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < spec.core.code.size := by simpa using hk
    simp only [spec.rawCode,Array.map_append]
    rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    simp [bound]
  have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
      (spec.raw.insts.map (·.mapRegs resolve)).size := by
    simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
    omega
  have path := route.execute run scope driver.toDriverSemG spec.placed segment machine endPosition
  have whole := RunOkABIAt.prefix path finished
  simpa only [slotEq] using whole

end Backend.Stock.Proof.ConditionalValues

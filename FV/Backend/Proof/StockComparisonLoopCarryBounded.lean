import FV.Backend.Proof.StockLoopCarryBounded
import FV.Backend.Proof.StockComparisonLoopCarry

/-! Fuel-bounded compositions of comparison branches with carry sets (#140, T7b-7).

`returning/trapping_empty_parameter_carry_below` use the parameter carry core only once; the rest
of the composition (the selected successor, its copies and its continuation below the fuel) does
not depend on the branch condition. `returning/trapping_empty_carry_below_of_core` take the core
conclusion as a premise, and `returning/trapping_empty_comparison_carry_below` apply them to the
comparison carry cores of `StockComparisonLoopCarry`, for all three comparison forms. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `returning_empty_parameter_carry_below` from the conclusion of a carry core: the block's
branch has empty arguments, and each selected successor continues below the block's fuel from
`CarryRel` of its own carry set. -/
theorem ConditionalBodySpec.returning_empty_carry_below_of_core
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop} {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    {ρ : Nat → CV} {world : Arm.ArmState}
    (core : ReturningCarryCore spec carry fuel s vals cm ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ := core
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
  have carriedAvailable : ∀ x,next.carried x →
      x ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
    intro x kept
    rw [next.atBlock]
    exact next.available x kept
  have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
      next.carried spec.term.output.state carry := by
    rw [next.atBlock]
    simp only [sourceTargetParams,next.found,Option.getD_some]
    exact next.cover
  obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
    spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
      carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
  have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
  subst tl
  have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
    (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
  subst targetLabel
  obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
  have destinationEq : destination = next.block := by
    rw [post.1.1] at found
    exact Option.some.inj (found.symm.trans next.found)
  have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
  have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
  have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
  have finished := next.returns left (by omega) {t with frame := fr} ρnext endWorld
    nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
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

/-- `trapping_empty_parameter_carry_below` from the conclusion of a carry core. -/
theorem ConditionalBodySpec.trapping_empty_carry_below_of_core
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop} {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    {ρ : Nat → CV} {world : Arm.ArmState}
    (core : TrappingCarryCore spec carry fuel s trapCode ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) := by
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
  rcases core with failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩
  · obtain ⟨offset,i,ops,regs,prefixWorld,outs,endWorld,execution,coded⟩ := failed
    obtain ⟨path,bound,instruction,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
    exact ⟨label,spec.preludeCode.size+offset,regs,prefixWorld,_,i,ops,outs,endWorld,path,
      spec.placed,instruction,operands,semantics,coded⟩
  · let bc := if Clif.Sem.truthy value.bits then yes else no
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
    have carriedAvailable : ∀ x,next.carried x →
        x ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
      intro x kept
      rw [next.atBlock]
      exact next.available x kept
    have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
        next.carried spec.term.output.state carry := by
      rw [next.atBlock]
      simp only [sourceTargetParams,next.found,Option.getD_some]
      exact next.cover
    obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
      spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
        carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
    have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
    subst tl
    have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
      (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
    subst targetLabel
    obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
    have destinationEq : destination = next.block := by
      rw [post.1.1] at found
      exact Option.some.inj (found.symm.trans next.found)
    have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
    have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
    have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
    have finished := next.traps left (by omega) {t with frame := fr} ρnext endWorld
      nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
    have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
        (spec.raw.insts.map (·.mapRegs resolve)).size := by
      simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
      omega
    have path := route.execute run scope driver.toDriverSemG spec.placed segment machine endPosition
    have whole := RunOkABIAt.prefix path finished
    simpa only [slotEq] using whole

/-- `returning_empty_parameter_carry_below` for a branch on a comparison in any of the three
forms (`ComparisonMetadata`): the block holds `CarryRel` of `carry` at entry, and each selected
successor continuation needs `CarryRel` of its own carry set. -/
theorem ConditionalBodySpec.returning_empty_comparison_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComparisonMetadata result.ctx c)
    (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) :=
  spec.returning_empty_carry_below_of_core run scope dominated driver tag termShape emptyArgs successors callers
    (spec.returning_comparison_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held)

/-- `trapping_empty_parameter_carry_below` for a branch on a comparison in any of the three
forms. -/
theorem ConditionalBodySpec.trapping_empty_comparison_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComparisonMetadata result.ctx c)
    (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped trapCode)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) :=
  spec.trapping_empty_carry_below_of_core run scope dominated driver tag termShape emptyArgs successors callers
    (spec.trapping_comparison_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held)

end Backend.Stock.Proof.ConditionalValues

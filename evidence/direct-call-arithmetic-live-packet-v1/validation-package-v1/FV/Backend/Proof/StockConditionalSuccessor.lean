import FV.Backend.Proof.RegallocFwd
import FV.Backend.Proof.StockConditionalBodyRefines
import FV.Backend.Proof.StockSelectedRoutes
import FV.Backend.Proof.StockSourceEdgeDFG
import FV.Backend.Proof.StockSourceEdges
import FV.Backend.Proof.StockCfgTraversalDemand

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem inherited_predecessor {f : Clif.Function} {ctx : Ctx}
    {bi tl : Nat} {b target : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (destination : f.blocks[tl]? = some target)
    (edge : bc.block ∈ succIds b.term) (index : blockIdx? f bc.block = some tl)
    {x : Nat} (available : x ∈ availOf f (availIn f ctx) tl 0)
    (notParameter : x ∉ target.params.map (·.1)) :
    x ∈ (availIn f ctx).getD tl [] ∧ x ∉ defsOf f tl ∧
      x ∈ availOf f (availIn f ctx) bi b.body.length := by
  obtain ⟨present,later⟩ := (mem_av destination).mp available
  have incoming : x ∈ (availIn f ctx).getD tl [] := by
    rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
    · exact False.elim (notParameter parameter)
    · exact incoming
    · omega
  have noDef : x ∉ defsOf f tl := by
    intro defined
    obtain ⟨original,j,stm,found,statement,result⟩ := mem_defsOf.mp defined
    cases Option.some.inj (found.symm.trans destination)
    exact later ⟨j,stm,Nat.zero_le _,statement,result⟩
  have successor : tl ∈ succIdx f bi := by
    simp only [succIdx,source]
    exact List.mem_filterMap.mpr ⟨bc.block,edge,index⟩
  have fixed := inFix_fixOk (f := f) (ctx := ctx) (gn := id)
  refine ⟨incoming,noDef,(mem_av source).mpr ⟨?_,?_⟩⟩
  · rcases fixed.out tl x incoming bi successor with parameter | defined | inherited
    · exact .inl (by rwa [parsOf_of source] at parameter)
    · obtain ⟨original,j,stm,found,statement,result⟩ := mem_defsOf.mp defined
      cases Option.some.inj (found.symm.trans source)
      exact .inr (.inr ⟨j,stm,lt_of_getElem? statement,statement,result⟩)
    · exact .inr (.inl inherited)
  · rintro ⟨j,stm,later,statement,_⟩
    have bound := lt_of_getElem? statement
    omega

/-- Source-selected copies establish the next actual scan relation, for both
ordinary and synthetic successors. Only demanded inherited values are carried;
outgoing argument values and traversal demand are internal composition facts. -/
theorem ConditionalBodySpec.selected_successor_guarded_of_demand
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    (nextBlock : next.block = sourceTargetIndex f bc)
    (demand : ∀ (x : Nat),next.output.state.demand[x]! ≤ spec.term.output.state.demand[x]!)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
      spec.term.output.state (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ tl targetLabel ρ',blockIdx? f bc.block = some tl ∧
      result.order.nodes[targetLabel]? = some (.original tl) ∧
      SelectedCopyRoute result label index ρ targetLabel ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,fr',cm) ρ' w := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨tl,middle,targetIndex,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope tag source selected
  obtain ⟨targetBlock,args,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
  have target : f.block? bc.block = some targetBlock := by rwa [before.1] at found
  have destination := blockIdx_block targetIndex target
  have nextAt : next.block = tl := by
    simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using nextBlock
  have edge := edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))
  let needed := fun x => Demanded next.output.state x ∧ x ∈ availOf f (availIn f result.ctx) tl 0
  have held : ValuesHeld (fun x => x ∈ bc.args ∨ (needed x ∧ x ∉ sourceTargetParams f bc))
      result.ctx fr (fun key => ρ (aliasNum result.final.alias key)) := by
    intro x required v get
    rcases required with argument | ⟨⟨needed,available⟩,notParameter⟩
    · exact arguments x argument v get
    · have absent : x ∉ targetBlock.params.map (·.1) := by
        simpa only [sourceTargetParams,target,Option.getD_some] using notParameter
      have previous := (inherited_predecessor source destination edge targetIndex available absent).2.2
      have demanded : Demanded spec.term.output.state x := by
        have le := demand x
        unfold Demanded at needed ⊢
        omega
      have previous' : x ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
        simpa only [spec.atBlock] using previous
      obtain ⟨key,mapped,value⟩ := before.2.2.2 x ⟨demanded,previous'⟩ v get
      refine ⟨key,?_,value⟩
      rw [← (stock_lower_record_context run scope spec.events).2.1 x]
      exact mapped
  obtain ⟨tl',targetLabel,ρ',targetIndex',targetTag,route,values⟩ :=
    stock_lower_selected_route_values run scope dominated tag source selected before.1 entered
      (needed := needed) (by
        intro x required
        simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using required.2) held
  have same : tl' = tl := Option.some.inj (targetIndex'.symm.trans targetIndex)
  subst tl'
  have dfg := stock_lower_source_enterBlock_dfg run scope dominated spec.events nextEvent
    source destination edge targetIndex before.1 (by simpa only [spec.atBlock] using before.2.1) entered
  have nextDefined := source_defined_enterBlock dominated.ssa result.ctx source before.1 edge
    targetIndex defined entered
  refine ⟨tl,targetLabel,ρ',targetIndex,targetTag,route,nextDefined,?_,?_,?_,?_⟩
  · rw [frame]
    exact before.1
  · simpa only [nextAt] using dfg
  · simpa only [frame] using before.2.2.1
  · intro x required v get
    obtain ⟨key,mapped,value⟩ := values x ⟨required.1,by simpa only [nextAt] using required.2⟩ v get
    refine ⟨key,?_,value⟩
    rw [(stock_lower_record_context run scope nextEvent).2.1 x]
    exact mapped

/-- For a forward edge the actual descending compiler traversal supplies the
demand inequality; no extra demand certificate is needed at the call site. -/
theorem ConditionalBodySpec.selected_successor_guarded
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    (nextBlock : next.block = sourceTargetIndex f bc)
    {targetLabel : Nat} (targetTag : result.order.nodes[targetLabel]? = some (.original next.block))
    (forward : label < targetLabel)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
      spec.term.output.state (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ tl selectedLabel ρ',blockIdx? f bc.block = some tl ∧
      result.order.nodes[selectedLabel]? = some (.original tl) ∧
      SelectedCopyRoute result label index ρ selectedLabel ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,fr',cm) ρ' w := by
  have demand := CfgDemand.ordered_scan_demand_of_labels run scope
    (Array.getElem?_eq_some_iff.mp targetTag).1 forward
    (by simp only [getElem!_def,targetTag,Option.getD_some])
    (by simp only [getElem!_def,tag,Option.getD_some,spec.atBlock]) nextEvent spec.events spec.split
  exact spec.selected_successor_guarded_of_demand run scope dominated tag selected nextEvent
    nextBlock demand before defined entered arguments

end Backend.Stock.Proof.ConditionalValues

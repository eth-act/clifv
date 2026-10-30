import FV.Backend.Proof.StockJumpDemand

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false

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

/-- A predecessor's demanded guard supplies inherited successor values.
The demand inequality is an internal compiler-state fact, not an extra input
condition or a requirement to materialize every source-available value. -/
theorem jump_successor_values_of_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextBlock : next.block = tl)
    (demand : ∀ (x : Nat),next.output.state.demand[x]! ≤ spec.term.output.state.demand[x]!)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ w) :
    ValuesHeld (fun x => x ∈ bc.args ∨
      ((Demanded next.output.state x ∧ x ∈ availOf f (availIn f result.ctx) tl 0) ∧
        x ∉ targetBlock.params.map (·.1)))
      result.ctx fr (fun k => ρ (aliasNum result.final.alias k)) := by
  have arguments := stock_jump_body_argument_values run scope dominated spec jump targetTag held
  have source := spec.split.block
  rw [spec.atBlock] at source
  have destination := blockIdx_block targetIndex target
  have edge : bc.block ∈ succIds b.term := by simp [jump,succIds,dests]
  intro x needed v read
  rcases needed with argument | ⟨⟨needed,available⟩,notParameter⟩
  · exact arguments x argument v read
  · have previous := (inherited_predecessor source destination edge targetIndex available notParameter).2.2
    have demanded : Demanded spec.term.output.state x := by
      unfold Demanded at needed ⊢
      have le := demand x
      omega
    have previous' : x ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
      simpa only [spec.atBlock] using previous
    obtain ⟨key,mapped,value⟩ := held.2.2.2 x ⟨demanded,previous'⟩ v read
    refine ⟨key,?_,value⟩
    rw [← (stock_lower_record_context run scope spec.events).2.1 x]
    exact mapped

end Backend.Stock.Proof.Control

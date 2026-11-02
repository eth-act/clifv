import FV.Backend.Proof.StockSelectScanRefines
import FV.Backend.Proof.StockSourceEdges
import FV.Backend.Proof.StockPerEdgeValues
import FV.Backend.Proof.StockSourceEdgeDFG

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Transfer only source values the actual successor scan demands. Values that
were omitted or sunk and are not demanded do not become a new machine-value
obligation merely because the source availability set contains them. -/
theorem direct_successor_guarded_of_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {first second : BlockScanEvent} (firstEvent : first ∈ result.blockScans.toList)
    (secondEvent : second ∈ result.blockScans.toList)
    {label bi index targetLabel tl : Nat} {b targetBlock : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (selected : (dests b.term)[index]? = some bc)
    (successor : result.order.successors[label]![index]? = some targetLabel)
    (targetTag : result.order.nodes[targetLabel]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    (firstBlock : first.block = bi) (secondBlock : second.block = tl)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {MR : MemRelT}
    {st : State} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : GuardedScanRel f result first.ctx first.block MR st (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (held : ValuesHeld (fun x => x ∈ bc.args ∨
      ((Demanded second.output.state x ∧ x ∈ availOf f (availIn f result.ctx) tl 0) ∧
        x ∉ targetBlock.params.map (·.1)))
      result.ctx fr (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ ρ',edgeEnvAt result.code result.edgeArgs label targetLabel index ρ = some ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      GuardedScanRel f result second.ctx second.block MR second.output.state (0,fr',cm) ρ' w := by
  obtain ⟨ρ',copied,values⟩ := stock_lower_direct_per_edge_values run scope dominated tag source
    selected successor targetTag targetIndex before.1 target entered
    (needed := fun x => Demanded second.output.state x ∧ x ∈ availOf f (availIn f result.ctx) tl 0)
    (fun _ h => h.2) held
  have edge := edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))
  have targetSource := blockIdx_block targetIndex target
  have dfg := stock_lower_source_enterBlock_dfg run scope dominated firstEvent secondEvent
    source targetSource edge targetIndex before.1 (by simpa only [firstBlock] using before.2.1) entered
  have nextDefined := source_defined_enterBlock dominated.ssa result.ctx source before.1 edge
    targetIndex defined entered
  refine ⟨ρ',copied,nextDefined,?_,?_,?_,?_⟩
  · obtain ⟨_,_,_,_,_,_,_,frame⟩ := enterBlock_spec entered
    rw [frame]
    exact before.1
  · simpa only [secondBlock] using dfg
  · obtain ⟨_,_,_,_,_,_,_,frame⟩ := enterBlock_spec entered
    simpa only [frame] using before.2.2.1
  · intro x needed v read
    obtain ⟨key,mapped,value⟩ := values x ⟨needed.1,by simpa only [secondBlock] using needed.2⟩ v read
    refine ⟨key,?_,value⟩
    rw [(stock_lower_record_context run scope secondEvent).2.1 x]
    exact mapped

end Backend.Stock.Proof.Control

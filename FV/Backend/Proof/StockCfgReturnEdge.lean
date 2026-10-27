import FV.Backend.Proof.StockCfgReturnBlock
import FV.Backend.Proof.StockGuardedSuccessor

namespace Backend.Stock.Proof.CfgReturn
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Compose an actual direct successor transfer with the selected return
block. The result starts at instruction zero, exactly where the real edge
enters; source binding derives the target body, term and definedness. -/
theorem direct_successor_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {first : BlockScanEvent} (firstEvent : first ∈ result.blockScans.toList)
    {label bi index targetLabel tl : Nat} {b targetBlock : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (selected : (dests b.term)[index]? = some bc)
    (successor : result.order.successors[label]![index]? = some targetLabel)
    (targetTag : result.order.nodes[targetLabel]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    (firstBlock : first.block = bi)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ReturnBlockSpec f result targetBlock targetLabel tl isem MR env cp)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {st : State} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : GuardedScanRel f result first.ctx first.block MR st (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (held : ValuesHeld (fun x => x ∈ bc.args ∨
      (x ∈ availOf f (availIn f result.ctx) tl 0 ∧ x ∉ targetBlock.params.map (·.1)))
      result.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr',[],cm⟩ = .returned vals outMem) :
    ∃ ρ',edgeEnvAt result.code result.edgeArgs label targetLabel index ρ = some ρ' ∧
      RunOkABI f result.code isem MR fr.slots ⟨targetLabel,0,ρ',w⟩ (.returned vals outMem) := by
  obtain ⟨ρ',copied,nextDefined,guard⟩ := stock_lower_direct_guarded_successor run scope dominated
    firstEvent spec.events tag source selected successor targetTag targetIndex target firstBlock
    spec.atBlock before defined entered held
  have nonentry : tl ≠ 0 := by
    intro zero
    subst tl
    exact scope.noEntryPred b (List.mem_of_getElem? source) bc.block
      (edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))) targetIndex
  obtain ⟨original,args,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
  rw [before.1] at found
  cases Option.some.inj (found.symm.trans target)
  have finished := spec.returns fuel ⟨fr',[],cm⟩ vals outMem
    (by rw [frame]; exact before.1) rfl (by rw [frame]) (by rw [frame])
    (by simpa only [spec.atBlock] using nextDefined) returned ρ' w guard
  refine ⟨ρ',copied,?_⟩
  simpa only [spec.noPrelude nonentry,frame] using finished

end Backend.Stock.Proof.CfgReturn

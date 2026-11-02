import FV.Backend.Proof.StockMemoryAccessScanTrap
import FV.Backend.Proof.StockMemoryAccessReach
import FV.Backend.Proof.StockFenceBodyRefines

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Source fences need no fault handler. All other record effects remain explicit. -/
theorem stock_body_fences_access_first_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    (ordinary : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {env : Clif.Env} {cp : Clif.Program} {MR : MemRelT} (stable : MRStable F MR)
    (initial : Clif.State) {sb : Nat} {code : Clif.TrapCode}
    (property : BitVec 64 → Nat → Prop)
    (normalOther : ∀ record ∈ body.records, ∀ j stm,b.body[j]? = some stm →
      record.inst = blockStart f event.block+j → stm.inst ≠ .fence →
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (GuardedScanRel f result event.ctx event.block MR) record)
    (trapOther : ∀ record ∈ body.records, ∀ j stm,b.body[j]? = some stm →
      record.inst = blockStart f event.block+j → stm.inst ≠ .fence →
      LocalAccessTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        sb isem result.final.alias
        (ReachedGuardedRel f result event.ctx event.block MR env cp initial) property record code) :
    ∀ s,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s code → ∀ ρ w,
      ReachedGuardedRel f result event.ctx event.block MR env cp initial body.state s ρ w →
      TrapOrAccessRun sb isem (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code property := by
  apply scans_access_trap_refines split.scanned
  · intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    obtain ⟨info,source,original,results⟩ := ArithmeticBody.body_source_info run events split statement current
    have family : ∀ actual inst,event.ctx.insts[record.inst]? = some actual → actual.clif = some inst →
        OrdinaryBody.OrdinaryInst inst := by
      intro actual inst present clif
      cases Option.some.inj (present.symm.trans source)
      cases Option.some.inj (clif.symm.trans original)
      exact ordinary stm (List.mem_of_getElem? statement)
    apply guarded_with_reach initial family
    by_cases fence : stm.inst = .fence
    · rw [fence] at original
      exact (stock_lower_fence_source_contract run scope dominated events
        (split.retained record member) source original).guarded refines env cp MR stable
    · exact normalOther record member j stm statement current fence
  · intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    by_cases fence : stm.inst = .fence
    · obtain ⟨info,source,original,results⟩ := ArithmeticBody.body_source_info run events split statement current
      rw [fence] at original
      intro s failed ρ w held
      obtain ⟨index,actual,inst,rest,present,clif,remaining,outcome⟩ := failed
      cases Option.some.inj (present.symm.trans source)
      cases Option.some.inj (clif.symm.trans original)
      change Clif.Res.ok ([],s.2.2) = Clif.Res.trap code at outcome
      cases outcome
    · exact trapOther record member j stm statement current fence

end Backend.Stock.Proof.MemoryFaults

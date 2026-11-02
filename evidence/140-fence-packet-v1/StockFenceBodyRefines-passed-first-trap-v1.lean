import FV.Backend.Proof.StockFenceSourceContract

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Extend existing internal record proofs with all actual source fences.
The remaining-family obligations stay explicit and do not change source admission. -/
theorem stock_body_fence_records {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {env : Clif.Env} {cp : Clif.Program} {MR : MemRelT} (stable : MRStable F MR)
    (normalOther : ∀ record ∈ body.records, ∀ j stm,b.body[j]? = some stm →
      record.inst = blockStart f event.block+j → stm.inst ≠ .fence →
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (GuardedScanRel f result event.ctx event.block MR) record)
    (trapOther : ∀ record ∈ body.records, ∀ j stm,b.body[j]? = some stm →
      record.inst = blockStart f event.block+j → stm.inst ≠ .fence →
      LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record) :
    (∀ record ∈ body.records,
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (GuardedScanRel f result event.ctx event.block MR) record) ∧
    (∀ record ∈ body.records,
      LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record) := by
  have each : ∀ record ∈ body.records,
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (GuardedScanRel f result event.ctx event.block MR) record ∧
      LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    by_cases fence : stm.inst = .fence
    · obtain ⟨info,source,original,results⟩ := ArithmeticBody.body_source_info run events split statement current
      rw [fence] at original
      have contract := stock_lower_fence_source_contract run scope dominated events (split.retained record member)
        source original
      exact ⟨contract.guarded refines env cp MR stable,contract.trapped isem env cp MR⟩
    · exact ⟨normalOther record member j stm statement current fence,
        trapOther record member j stm statement current fence⟩
  exact ⟨fun r member => (each r member).1,fun r member => (each r member).2⟩

/-- Actual backward records compose in original source order through a first trap.
Both fence cases are discharged internally; all other effects remain proof obligations. -/
theorem stock_body_with_fences_first_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {env : Clif.Env} {cp : Clif.Program} {MR : MemRelT} (stable : MRStable F MR)
    (normalOther : ∀ record ∈ body.records, ∀ j stm,b.body[j]? = some stm →
      record.inst = blockStart f event.block+j → stm.inst ≠ .fence →
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (GuardedScanRel f result event.ctx event.block MR) record)
    (trapOther : ∀ record ∈ body.records, ∀ j stm,b.body[j]? = some stm →
      record.inst = blockStart f event.block+j → stm.inst ≠ .fence →
      LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record) :
    ∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s code → ∀ ρ w,
      GuardedScanRel f result event.ctx event.block MR body.state s ρ w →
      TrapRun isem (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code := by
  have each := stock_body_fence_records run scope dominated events split refines stable normalOther trapOther
  exact split.scanned.local_trap_refines each.1 each.2

end Backend.Stock.Proof

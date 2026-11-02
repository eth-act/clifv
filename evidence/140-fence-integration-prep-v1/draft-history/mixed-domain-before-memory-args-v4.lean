import FV.Backend.Proof.StockFenceMixedBodyTrap
import FV.Backend.Proof.StockMemoryFaultContract
import FV.Backend.Proof.StockMemoryAccessEntryTrap
import FV.Backend.Proof.StockMemoryReturnRefines

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver
open MemoryFaults
set_option autoImplicit false
set_option Elab.async false

private theorem mixed_ordinary : ∀ stm ∈ function.blocks[0]!.body,OrdinaryBody.OrdinaryInst stm.inst := by
  intro stm member
  simp [function] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [OrdinaryBody.OrdinaryInst]

private theorem fixed_split {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body,SourceBodySplit function event function.blocks[0]! term body := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have facts := mixed_actual_body_facts run events
  have lookup : function.blocks[0]? = some b := by simpa only [facts.1] using split.block
  have same : function.blocks[0]! = b := Option.some.inj lookup
  subst b
  exact ⟨term,body,split⟩

/-- The unchanged complete mixed function refines all returns and first traps.
Source arguments, source memory and the divisor remain unrestricted. -/
theorem mixed_domain_with_access_traps : DomainWithAccessTraps function := by
  obtain ⟨actual,event,lowered,scope,dominated,events,witness⟩ := mixed_records
  refine ⟨scope,dominated,rfl,rfl,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    apply OrdinaryBody.actual_ordinary_entry_return_refines_frame run scope dominated rfl rfl mixed_ordinary
      (xs := [128]) rfl entered returned refines driver memorySem stable ?_ memory arguments
    intro event events
    obtain ⟨term,body,split⟩ := fixed_split run scope events
    refine ⟨term,body,split,?_⟩
    intro before after steps ρ world held
    have normal := mixed_record_fall_refines run scope dominated events split refines memorySem stable memoryOk (env := env) (cp := cp)
    apply split.scanned.fall_refines normal before after ?_ ρ world ?_
    · simpa [sourceBodyIndices,function] using steps
    · simpa only [split.state] using held
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments Q allFaults
    apply actual_ordinary_entry_access_trap_refines_frame run scope dominated rfl mixed_ordinary
      (xs := [128]) rfl entered trapped refines driver memorySem stable (property := sourceAddrPred Q)
      ?_ memory arguments
    intro event events
    obtain ⟨term,body,split⟩ := fixed_split run scope events
    refine ⟨term,body,split,?_⟩
    have normal := mixed_record_fall_refines run scope dominated events split refines memorySem stable memoryOk (env := env) (cp := cp)
    have reachedNormal : ∀ record ∈ body.records,
        ScanFallRefines (IndexedSourceInst env cp function event.ctx event.block) isem result.final.alias
          (ReachedGuardedRel function result event.ctx event.block MR env cp ⟨fr,[],cm⟩) record := by
      intro record member
      obtain ⟨j,stm,statement,current⟩ := split.positions record member
      obtain ⟨info,source,original,results⟩ := ArithmeticBody.body_source_info run events split statement current
      apply guarded_with_reach ⟨fr,[],cm⟩ ?_ (normal record member)
      intro actual inst present clif
      cases Option.some.inj (present.symm.trans source)
      cases Option.some.inj (clif.symm.trans original)
      exact mixed_ordinary stm (List.mem_of_getElem? statement)
    have trapping := mixed_record_access_trap run scope dominated events split refines ⟨fr,[],cm⟩ Q allFaults
    intro point failed ρ world held
    exact scans_access_trap_refines split.scanned reachedNormal trapping point
      (by simpa [sourceBodyIndices,function] using failed) ρ world
      (by simpa only [split.state] using held)

end Backend.Stock.Proof.FenceFixture

import FV.Backend.Proof.StockFenceConsumer
import FV.Backend.Proof.StockAcquirePendingValues
import FV.Backend.Proof.StockSourceDFG

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- The actual fence record refines its original indexed source step.
Only source-available demanded values enter the original guarded relation. -/
theorem stock_lower_fence_pending_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some .fence)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (env : Clif.Env) (cp : Clif.Program) (MR : MemRelT) (stable : MRStable F MR)
    (snapshots : List (Acquire810.SunkReadSnapshot event.ctx env cp)) :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (Acquire810.PendingGuardedScanRel f result event.ctx event.block env cp MR snapshots) record := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have inBody : record ∈ body.records := by
    have member := records
    rw [split.records] at member
    rcases List.mem_cons.mp member with same | member
    · have different := stock_fence_source_not_term run events found original
      exact False.elim (different (by rw [same,split.termInst]))
    · exact member
  obtain ⟨j,stm,statement,current⟩ := split.positions record inBody
  obtain ⟨actual,present,source,resultEq⟩ := ArithmeticBody.body_source_info run events split statement current
  have infoEq : actual = info := Option.some.inj (present.symm.trans found)
  subst actual
  have results : info.results = [] := by
    have empty := SinkRules.fence_results_empty (stock_lower_record_context run scope events).1 found original
    simpa only [getElem!_def,found,Option.getD_some] using empty
  have stmtResults : stm.results = [] := resultEq.symm.trans results
  obtain ⟨step,recorded,emitted,resultRegs,last,code,frame⟩ :=
    stock_lower_fence_record_exact run scope events records found original
  intro s s' indexed ρ w related
  obtain ⟨index,position,stepped⟩ := indexed
  have samePosition : j = s.1 := by omega
  rw [samePosition] at statement current
  have dfg := stock_lower_source_step_dfg run scope dominated events split.block statement current
    related.1 related.2.1 stepped
  obtain ⟨actual,inst,vals,regs,rest,present,source,remaining,outcome,written,after⟩ := stepped
  have infoEq : actual = info := Option.some.inj (present.symm.trans found)
  subst actual
  have instEq : inst = .fence := Option.some.inj (source.symm.trans original)
  subst inst
  change Clif.Res.ok ([],s.2.2) = Clif.Res.ok (vals,s'.2.2) at outcome
  have valsEq : vals = [] := (congrArg Prod.fst (Clif.Res.ok.inj outcome)).symm
  have memEq : s'.2.2 = s.2.2 := (congrArg Prod.snd (Clif.Res.ok.inj outcome)).symm
  rw [results,valsEq] at written
  change some s.2.1.regs = some regs at written
  have regsEq : regs = s.2.1.regs := (Option.some.inj written).symm
  obtain ⟨world,executed,sameWorld⟩ := stock_lower_fence_execute run scope events records found original
    refines result.final.alias ρ w
  refine ⟨ρ,world,executed,?_,?_,?_,?_⟩
  · simpa only [after] using related.1
  · rw [position]
    exact dfg
  · rw [after,memEq]
    exact stable s.2.1.slots s.2.2 w world sameWorld.toNF related.2.2.1
  · intro x wanted notSuspended v value
    have before : x ∈ availOf f (availIn f result.ctx) event.block s.1 :=
      available_before_of_after_not_result split.block statement
        (by simpa only [position] using wanted.2) (by rw [stmtResults]; simp)
    have demand : Demanded record.output.state x := by
      simpa only [Demanded,frame,scanState_demands] using wanted.1
    apply related.2.2.2 x ⟨demand,before⟩ notSuspended v
    simpa only [after,regsEq] using value

end Backend.Stock.Proof

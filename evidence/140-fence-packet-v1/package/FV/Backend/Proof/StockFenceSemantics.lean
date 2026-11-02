import FV.Backend.Proof.StockFenceRecordExact
import FV.Backend.Proof.StockScanTrapSemantics

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- An actual fence record executes under the original machine refinement contract.
It retains all demanded source values and the original memory relation. -/
theorem stock_lower_fence_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (aliases : Array (Option Nat)) (env : Clif.Env) (cp : Clif.Program)
    (MR : Clif.Mem → Arm.ArmState → Prop)
    (stable : ∀ cm w w', SameWorldNF F w' w → MR cm w → MR cm w') :
    ScanFallRefines (SourceInstResult env cp event.ctx) isem aliases
      (fun st s ρ w => MR s.2 w ∧ ValuesHeld (Demanded st) event.ctx s.1
        (fun k => ρ (aliasNum aliases k))) record := by
  obtain ⟨step,recorded,emitted,results,last,code,frame⟩ :=
    stock_lower_fence_record_exact run scope events records found source
  have empty := SinkRules.fence_results_empty (stock_lower_record_context run scope events).1 found source
  have noResults : info.results = [] := by
    simpa only [getElem!_def,found,Option.getD_some] using empty
  intro s s' stepped ρ w held
  obtain ⟨actual,inst,vals,regs,rest,present,original,remaining,outcome,written,after⟩ := stepped
  have same : actual = info := Option.some.inj (present.symm.trans found)
  subst actual
  have fence : inst = .fence := Option.some.inj (original.symm.trans source)
  subst inst
  change Clif.Res.ok ([],s.2) = Clif.Res.ok (vals,s'.2) at outcome
  have valsEq : vals = [] := (congrArg Prod.fst (Clif.Res.ok.inj outcome)).symm
  have memEq : s'.2 = s.2 := (congrArg Prod.snd (Clif.Res.ok.inj outcome)).symm
  rw [noResults,valsEq] at written
  change some s.1.regs = some regs at written
  have regsEq : regs = s.1.regs := (Option.some.inj written).symm
  obtain ⟨world,executed,sameWorld⟩ := refines .fence [] w [] w (ctl := .next) rfl
  have machine := seqRun_isem_one (i := .fence) (ops := #[]) (ρ := ρ) rfl executed rfl
  change seqRun isem [.fence] ρ w = some (.fall ρ world) at machine
  refine ⟨ρ,world,?_,?_,?_⟩
  · rw [code]
    exact machine
  · rw [memEq]
    exact stable s.2 w world sameWorld.toNF held.1
  · intro x demanded v value
    have originalDemand : Demanded record.output.state x := by
      simpa only [Demanded,frame,scanState_demands] using demanded
    have old := held.2 x originalDemand v
    apply old
    simpa only [after,regsEq] using value

end Backend.Stock.Proof

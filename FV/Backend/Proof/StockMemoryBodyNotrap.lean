import FV.Backend.Proof.StockLocalSourceTrap

namespace Backend.Stock.Proof.OrdinaryBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

private theorem no_trap_steps {S : Type} {step : Nat → S → S → Prop}
    {trap : Nat → S → Clif.TrapCode → Prop} {indices : List Nat} {s : S} {code : Clif.TrapCode}
    (failed : SourceTrapSteps step trap indices s code) :
    (∀ i ∈ indices,∀ s code,¬ trap i s code) → False := by
  induction failed with
  | here trapped =>
    intro none
    exact none _ (by simp) _ _ trapped
  | next head tail ih =>
    intro none
    apply ih
    intro i member s code
    exact none i (List.mem_cons_of_mem _ member) s code

/-- Original nontrapping source statements exclude a genuine indexed body trap.
No initial-memory permission or caller execution certificate is introduced. -/
theorem source_body_notrap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {env : Clif.Env} {cp : Clif.Program}
    (notrap : ∀ stm ∈ b.body,∀ fr cm code,instOutcome env cp fr cm stm.inst ≠ .trap code) :
    ∀ s code,¬ SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      ((List.range b.body.length).map (blockStart f event.block+·)) s code := by
  have each : ∀ i ∈ (List.range b.body.length).map (blockStart f event.block+·),
      ∀ s code,¬ LocalBody.IndexedSourceTrap env cp f event.ctx event.block i s code := by
    intro i member s code failed
    have indexed : i ∈ sourceBodyIndices f event.block b := by
      exact List.mem_reverse.mpr member
    rw [← split.scanned.order] at indexed
    obtain ⟨record,present,current⟩ := List.mem_map.mp indexed
    obtain ⟨j,stm,statement,position⟩ := split.positions record present
    obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement position
    obtain ⟨index,other,inst,rest,otherSource,otherClif,remaining,trapped⟩ := failed
    have actualSource : event.ctx.insts[i]? = some info := by rw [← current]; exact source
    have same : other = info := Option.some.inj (otherSource.symm.trans actualSource)
    subst other
    have sameInst : inst = stm.inst := Option.some.inj (otherClif.symm.trans clif)
    subst inst
    exact notrap stm (List.mem_of_getElem? statement) s.2.1 s.2.2 code trapped
  intro s code failed
  exact no_trap_steps failed each

end Backend.Stock.Proof.OrdinaryBody

import FV.Backend.Proof.StockExplicitCallSem
namespace Backend.Stock.Proof.ExplicitCallFramesDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ExplicitCallSemDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- Existing scalar instruction refinement carries through the adapter; calls
are covered by the original external contract rather than the scalar specification. -/
theorem stock_explicit_call_sem_refines {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) : Refines F (explicitCallSem isem) := by
  intro i us w outs w' ctl spec
  have actual := refines i us w outs w' spec
  cases i with
  | call info => simp [ispec] at spec
  | _ => exact actual

/-- Register renaming, branch retargeting, entry arguments and jumps all keep
the existing driver semantics under the explicit-result adapter. -/
theorem stock_explicit_call_sem_driver {isem : Backend.Proof.Sem} (base : DriverSem isem) :
    DriverSem (explicitCallSem isem) where
  args := base.args
  jump := base.jump
  rename := by
    intro g gn renamed i
    have same := base.rename g gn renamed i
    funext uses w
    cases i <;> simp only [explicitCallSem,MInst.mapRegs,List.length_map] at *
    all_goals first | exact congrFun (congrFun same uses) w | rw [same]
  retarget := by
    intro i ls i' targets
    have same := base.retarget i ls i' targets
    rcases setTargets_cases targets with ⟨l,l',rfl,rfl⟩ | ⟨t,e,t',e',k,rfl,rfl⟩ |
      ⟨kd,t,e,t',e',rn,bit,rfl,rfl⟩ | ⟨d,ts,d',ts',r,t1,t2,rfl,rfl,hlen⟩ |
      ⟨info,ti,ti',rfl,rfl,hlen,hrets⟩
    all_goals exact same

/-- Every non-call instruction retains its actual semantics, including existing
TryCall normal and exceptional interfaces; this adapter changes regular calls only. -/
theorem stock_explicit_call_sem_other (isem : Backend.Proof.Sem) (i : MInst)
    (other : ∀ info,i ≠ .call info) : explicitCallSem isem i = isem i := by
  cases i with
  | call info => exact False.elim (other info rfl)
  | _ => rfl
end Backend.Stock.Proof.ExplicitCallFramesDraft

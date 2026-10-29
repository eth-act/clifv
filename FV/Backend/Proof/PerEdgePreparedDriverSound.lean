module

public import FV.Backend.Proof.PerEdgePrepareSound
public import FV.Backend.Proof.PerEdgeRegallocFwd
public import FV.Backend.Proof.PerEdgeAllocDriverSound

@[expose] public section

/-! Actual successful preparation and allocation compose to forward realization
of the original indexed VCode. Checking facts are extracted from the actual
runtime wrappers, not supplied as program assumptions. Totality/completeness
under original Stock input conditions remains a separate obligation. -/
namespace Backend.Proof.PerEdge
open Backend Backend.Proof.Driver

theorem prepareCheckedAt_ok {vc : VCode} {edges : Array (Array (Array Reg))} {prepared : EdgeVCode}
    (h : prepareCheckedAt vc edges = .ok prepared) :
    prepareAt vc edges = .ok prepared ∧ PerEdgePrep.prepCheckAt vc edges prepared = true := by
  unfold prepareCheckedAt at h
  obtain ⟨p,run,h⟩ := Except.bind_ok h
  cases checked : PerEdgePrep.prepCheckAt vc edges p with
  | false => simp [checked,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
  | true =>
    simp only [checked,Bool.not_true,ite_false,pure,Except.pure,Except.ok.injEq] at h
    cases h
    exact ⟨run,checked⟩

/-- Every original indexed VCode return is realized by any concrete machine
implementing the allocation actually selected/lowered by the driver. The
returned values/world and callee-saved parts are preserved, as is its trace
invariant. No preparation/allocation checker verdict is a caller premise. -/
theorem prepared_return_forward {W S : Type} {vc : VCode} {edges : Array (Array (Array Reg))}
    {prepared : EdgeVCode} {ra : Except String RFunc} {af : AFunc}
    (preparation : prepareCheckedAt vc edges = .ok prepared)
    (lowering : lowerAllocAt prepared.code prepared.edges ra = .ok af)
    {sem : ISem CV W} (dsem : DriverSemG sem) (keep : Reg → CV → CV)
    {step : S → S} {Q : RFunc → S → MConf CV W → Prop} {T : S → Prop}
    (realizes : ∀ rf,allocResultAt prepared.code prepared.edges ra = .ok rf →
      lowerRFunc prepared.code rf = .ok af → Realizes prepared.code rf sem keep step (Q rf) T)
    {m₀ : Loc → CV} {ρ₀ : Nat → CV} {w₀ : W} {s₀ : S} {vals : List CV} {w : W}
    (initial : ∀ rf,allocResultAt prepared.code prepared.edges ra = .ok rf →
      lowerRFunc prepared.code rf = .ok af → Q rf s₀ (MConf.init rf m₀ w₀))
    (source : Star (VStepAt vc edges sem) (VConf.init ρ₀ w₀) (.ret vals w)) :
    ∃ rf n m,allocResultAt prepared.code prepared.edges ra = .ok rf ∧
      lowerRFunc prepared.code rf = .ok af ∧ Q rf (iterN step n s₀) (.ret vals m w) ∧
      (∀ r ∈ calleeSaved,keep r (m (.reg r)) = keep r (m₀ (.reg r))) ∧
      ∀ i < n,T (iterN step i s₀) := by
  obtain ⟨_,checked⟩ := prepareCheckedAt_ok preparation
  have preparedRun := PerEdgePrep.prep_ret dsem checked source
  obtain ⟨rf,selected,accepted,lowered⟩ := lowerAllocAt_ok lowering
  obtain ⟨R,simulation,related,callee⟩ := checkAlloc_sound prepared.code rf sem keep accepted m₀ ρ₀ w₀
  obtain ⟨n,final,concrete,related',trace⟩ := forward simulation (realizes rf selected lowered)
    preparedRun related (initial rf selected lowered)
  cases final with
  | run state => obtain ⟨_,impossible⟩ := simulation.run related'; cases impossible
  | halt world => have impossible := simulation.halt related'; cases impossible
  | ret values memory world =>
    have same := simulation.ret related'
    cases same
    exact ⟨rf,n,memory,selected,lowered,concrete,callee related',trace⟩

/-- Original indexed VCode halts are realized with the same world and trace
invariant through the actual successful preparation/allocation wrappers. -/
theorem prepared_halt_forward {W S : Type} {vc : VCode} {edges : Array (Array (Array Reg))}
    {prepared : EdgeVCode} {ra : Except String RFunc} {af : AFunc}
    (preparation : prepareCheckedAt vc edges = .ok prepared)
    (lowering : lowerAllocAt prepared.code prepared.edges ra = .ok af)
    {sem : ISem CV W} (dsem : DriverSemG sem) (keep : Reg → CV → CV)
    {step : S → S} {Q : RFunc → S → MConf CV W → Prop} {T : S → Prop}
    (realizes : ∀ rf,allocResultAt prepared.code prepared.edges ra = .ok rf →
      lowerRFunc prepared.code rf = .ok af → Realizes prepared.code rf sem keep step (Q rf) T)
    {m₀ : Loc → CV} {ρ₀ : Nat → CV} {w₀ w : W} {s₀ : S}
    (initial : ∀ rf,allocResultAt prepared.code prepared.edges ra = .ok rf →
      lowerRFunc prepared.code rf = .ok af → Q rf s₀ (MConf.init rf m₀ w₀))
    (source : Star (VStepAt vc edges sem) (VConf.init ρ₀ w₀) (.halt w)) :
    ∃ rf n,allocResultAt prepared.code prepared.edges ra = .ok rf ∧
      lowerRFunc prepared.code rf = .ok af ∧ Q rf (iterN step n s₀) (.halt w) ∧
      ∀ i < n,T (iterN step i s₀) := by
  obtain ⟨_,checked⟩ := prepareCheckedAt_ok preparation
  have preparedRun := PerEdgePrep.prep_halt dsem checked source
  obtain ⟨rf,selected,accepted,lowered⟩ := lowerAllocAt_ok lowering
  obtain ⟨R,simulation,related,_⟩ := checkAlloc_sound prepared.code rf sem keep accepted m₀ ρ₀ w₀
  obtain ⟨n,final,concrete,related',trace⟩ := forward simulation (realizes rf selected lowered)
    preparedRun related (initial rf selected lowered)
  cases final with
  | run state => obtain ⟨_,impossible⟩ := simulation.run related'; cases impossible
  | ret values memory world => have impossible := simulation.ret related'; cases impossible
  | halt world =>
    have same := simulation.halt related'
    cases same
    exact ⟨rf,n,selected,lowered,concrete,trace⟩
end Backend.Proof.PerEdge

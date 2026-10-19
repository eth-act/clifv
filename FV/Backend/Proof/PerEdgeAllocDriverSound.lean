import FV.Backend.RegallocPerEdgeDriver
import FV.Backend.Proof.PerEdgeRegallocSound
namespace Backend.Proof.PerEdge

private theorem checkedSpillAt_ok {vc : VCode} {edges : Array (Array (Array Reg))} {rf : RFunc}
    (h : checkedSpillAt vc edges = .ok rf) : checkAllocAt vc edges rf = .ok () := by
  unfold checkedSpillAt at h
  obtain ⟨answer,accepted,result⟩ := Except.bind_ok h
  cases answer
  cases result
  exact accepted

/-- Every selected allocation, including the fallback, passes the indexed
checker; failure of the external allocator is not a trusted assumption. -/
theorem allocResultAt_checked {vc : VCode} {edges : Array (Array (Array Reg))}
    {ra : Except String RFunc} {rf : RFunc} (h : allocResultAt vc edges ra = .ok rf) :
    checkAllocAt vc edges rf = .ok () := by
  unfold allocResultAt at h
  split at h
  · exact checkedSpillAt_ok h
  · split at h
    · rename_i accepted
      split at h
      · split at h
        · cases h
          cases check : checkAllocAt vc edges _ with
          | ok answer => cases answer; rfl
          | error err => simp [check,Except.isOk,Except.toBool] at accepted
        · exact checkedSpillAt_ok h
      · exact checkedSpillAt_ok h
    · exact checkedSpillAt_ok h

/-- Successful actual lowering exposes the checked allocation it lowered. -/
theorem lowerAllocAt_ok {vc : VCode} {edges : Array (Array (Array Reg))}
    {ra : Except String RFunc} {af : AFunc} (h : lowerAllocAt vc edges ra = .ok af) :
    ∃ rf,allocResultAt vc edges ra = .ok rf ∧ checkAllocAt vc edges rf = .ok () ∧
      lowerRFunc vc rf = .ok af := by
  unfold lowerAllocAt at h
  obtain ⟨rf,selected,lowered⟩ := Except.bind_ok h
  exact ⟨rf,selected,allocResultAt_checked selected,lowered⟩

/-- Actual driver success supplies complete indexed M6 simulation for its
selected allocation, including the checked spill fallback. Preparation/source
and instruction/bytes composition remain separate obligations. -/
theorem lowerAllocAt_sound {vc : VCode} {edges : Array (Array (Array Reg))}
    {ra : Except String RFunc} {af : AFunc} (h : lowerAllocAt vc edges ra = .ok af)
    {V W : Type} (sem : ISem V W) (keep : Reg → V → V) :
    ∃ rf,allocResultAt vc edges ra = .ok rf ∧ lowerRFunc vc rf = .ok af ∧
      ∀ (m : Loc → V) (ρ : Nat → V) (w : W),
        ∃ R,IsSimulation vc rf sem keep edges R ∧ R (MConf.init rf m w) (VConf.init ρ w) ∧
          ∀ {vals m' w' v},R (.ret vals m' w') v →
            ∀ r ∈ calleeSaved,keep r (m' (.reg r)) = keep r (m (.reg r)) := by
  obtain ⟨rf,selected,accepted,lowered⟩ := lowerAllocAt_ok h
  exact ⟨rf,selected,lowered,fun m ρ w => checkAlloc_sound vc rf sem keep accepted m ρ w⟩
end Backend.Proof.PerEdge

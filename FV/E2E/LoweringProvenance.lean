import FV.E2E.LinkCheck

set_option autoImplicit false

namespace E2E.LinkCheck
open Backend

/-- Data provenance for the actual lowering callback and stage. This theorem
supplies no source-correctness assumption or certificate for an arbitrary callback. -/
theorem pipeTWithLowering_spec {lower : Clif.Function → Except String VCode}
    {stage : Clif.Function → VCode → VCode} {f : Clif.Function} {k : Nat} {base : BitVec 64}
    {o : Lean.Json} {a : Art}
    (h : pipeTWithLowering lower stage f k base o = .ok a) :
    lower f = .ok a.vc ∧ prepare (stage f a.vc) = .ok a.vcp ∧
      a.rf = allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o)) ∧
      lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧
      a.fa.layout = .ok a.fb ∧ a.k = k ∧ a.base = base := by
  unfold pipeTWithLowering at h
  rcases h1 : lower f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare (stage f vc) with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h3] at h
  · cases h
  rcases h4 : emitFunc k af with _ | fa <;> simp only [h4] at h
  · cases h
  rcases h5 : fa.layout with _ | fb <;> simp only [h5] at h
  · cases h
  cases h
  exact ⟨rfl, h2, rfl, lowerAlloc_eq ((lowerAllocReady_eq _ _).symm.trans h3),
    h4, h5, rfl, rfl⟩


end E2E.LinkCheck

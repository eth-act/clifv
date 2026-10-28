import FV.E2E.IselSimIPrefix
import FV.E2E.IselSimIWitness

/-!
# Witness for the counted prefix simulation (`FV/E2E/IselSimIPrefix.lean`)

`iselSim_prefixWI` applies to `LinkWitness`'s compiled function `a2` (the entry premises remain).
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

theorem a2_prefixWI {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV) (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) :
    ∀ t n, ReachN Clif.Rust.env (L F).P.bare cs t n → callNum t = 1 →
      ∃ b k ρ w, Star (VStep (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩
          (ExtSemI.const Xb))) (.run ⟨0, 0, ρ₀, (w₀, 0)⟩) (.run ⟨b, k, ρ, (w, n)⟩) ∧
        RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
          (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c t.frame.slots t.mem w := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact iselSim_prefixWI (hL.subset fA2 hA2) a2_compiled a2_callsOne.1 a2_callsOne.2
    (fun _ n _ => a2_xcalls _ _ _ n) (fun n b h => by cases h) rfl ρ₀ hce hrel hargs htr

end E2E.LinkWitness

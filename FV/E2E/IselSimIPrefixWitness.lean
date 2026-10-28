import FV.E2E.IselSimIPrefix
import FV.E2E.IselSimIWitness
import FV.E2E.IselSimIPrefixCleanup
import FV.E2E.BackendWorldCleanupIWitness

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


namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`iselSim_prefixWI_cleanup` applies** to the closed cleanup compilation of `source`. -/
theorem prefix_cleanup_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (XI : ExtSemI) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (ρ₀ : Nat → CV) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs →
        ∀ t n, ReachN env { funcs := [] } cs t n → callNum t = 1 →
          ∃ b k ρ w, Star (VStep vc (valueSemI F ⟨fa.k, af.slotBase⟩ XI))
            (.run ⟨0, 0, ρ₀, (w₀, 0)⟩) (.run ⟨b, k, ρ, (w, n)⟩) ∧
            RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
              source c t.frame.slots t.mem w := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, -, -⟩ := compiled_covered_exists
  exact ⟨vc, vcp, af, fa, fb, hc, fun env XI F c w₀ ρ₀ args cs hce hrel hargs htr =>
    iselSim_prefixWI_cleanup hsub hc source_callsOne.1 source_callsOne.2
      (fun _ n _ => source_xcalls _ _ _ n) (fun n b h => by cases h) rfl ρ₀ hce hrel hargs htr⟩

end E2E.DeadCleanupWitness
import FV.Opt.Proof.GvnEdit
import FV.Opt.Proof.Unreachable
import FV.Opt.Optimize

/-!
# The pipeline refines (`Opt.optimize_sim`)

`Opt.optimizeReport` runs `removeUnreachable` (self-validating, `Opt.removeUnreachable_sim`),
then `check`, then each stage followed by `check` and — for GVN, DCE and LICM — the edit
validator (`Opt.editOk_sim`), keeping the last accepted function. The loop invariant is
`FunSim f0 g ∧ check g = .ok info`; FunSim composes (`FunSim.trans`).

The simplify stage is covered by the hypothesis `SimplifyPassSim`: the pass (for any rule
sets satisfying the rule obligations, `FV/Opt/Proof/Simplify*.lean`) refines on checked inputs.
-/

namespace Opt

open Clif

/-- Invariants of `forIn` over a list in `Id`, followed by a continuation. -/
theorem forIn_bind_inv {α σ β : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (k : σ → Id β) (P : σ → Prop) (Q : β → Prop) (h0 : P init)
    (hf : ∀ a s, P s → P (f a s).run.value) (hk : ∀ s, P s → Q (k s).run) :
    Q ((forIn l init f >>= k).run) := by
  induction l generalizing init with
  | nil => simpa using hk init h0
  | cons a as ih =>
    rw [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b =>
      rw [hfa] at this
      simp only [bind_assoc, Id.run_bind, hfa]
      exact hk b this
    | yield b =>
      rw [hfa] at this
      simp only [bind_assoc, Id.run_bind, hfa]
      exact ih b this

/-- The simplify stage refines on checked inputs (for the given rule sets). -/
def SimplifyPassSim (rules : SimplifyFn) (skel : SkeletonFn) : Prop :=
  ∀ allowed skelOk remat g info, check g = .ok info →
    FunSim g (simplify rules skel allowed skelOk remat g info).1

/-- **The mid-end pipeline refines**, for every function (ill-formed inputs are returned with
only unreachable blocks removed, validated). -/
theorem optimizeReport_sim (cfg : Config)
    (hS : SimplifyPassSim cfg.rules.fn cfg.rules.skeletonFn) (f0 : Function) :
    FunSim f0 (optimizeReport cfg f0).1 := by
  have hU := removeUnreachable_sim f0
  unfold optimizeReport
  simp only [Id.run]
  split
  · rename_i i hc
    simp only [pure_bind]
    apply forIn_bind_inv (P := fun s : Report × Function × Info × Bool =>
      FunSim f0 s.2.1 ∧ check s.2.1 = .ok s.2.2.1)
      (Q := fun x : Function × Report => FunSim f0 x.1)
    · exact ⟨hU, hc⟩
    · intro stage s hs
      obtain ⟨hsim, hchk⟩ := hs
      obtain ⟨r, g, info, stop⟩ := s
      simp only at hsim hchk
      simp only [Id.run]
      repeat' split
      all_goals simp only [pure, ForInStep.value]
      all_goals first
        | exact ⟨hsim, hchk⟩
        | exact ⟨hsim.trans ((hS _ _ _ _ _ hchk).trans (removeUnreachable_sim _)), ‹_›⟩
        | (rename_i hchk' hcond
           simp only [Bool.or_eq_true, beq_iff_eq] at hcond
           rcases hcond with hcond | hcond
           · first | (simp at hcond; done) | exact absurd hcond ‹_›
           · exact ⟨hsim.trans (editOk_sim hchk hchk' hcond), hchk'⟩)
    · intro s hs; exact hs.1
  · exact hU

end Opt

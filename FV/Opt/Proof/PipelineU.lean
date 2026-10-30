import FV.Opt.Proof.PipelineX
import FV.Opt.Proof.GvnEditU
import FV.Opt.Proof.SimpSimU
import FV.Opt.Proof.UnreachableU

/-!
# The pipeline refines with handler edges (`Opt.optimizeExe_simU`, S10f #233)

`FV/Opt/Proof/PipelineX.lean` for `FunSimU`: the stages simulate with the handler edges of
their `try_call`s (`removeUnreachable_simU`, `editOk_simU`, `simpOk_simU`) and `FunSimU`
composes, so the mid-end of the executable compiler `Opt.optimizeExe` refines every function
with its handler edges, and every program's runs with unwinding
(`Opt.optimizeProgramExe_refinesU`, from `Opt.runLoopX_refinesU`).
-/

namespace Opt

open Clif

/-! ## The simplify stage -/

/-- `SimplifyPassSimX` for `FunSimU`. -/
def SimplifyPassSimU (rules : SimplifyFn) (skel : SkeletonFn) : Prop :=
  ∀ allowed skelOk remat g info, check g = .ok info →
    simpOk g (simplify rules skel allowed skelOk remat g info).1 info
      (simplify rules skel allowed skelOk remat g info).2.2 = true →
    FunSimU g (simplify rules skel allowed skelOk remat g info).1

/-- **The simplify stage refines with handler edges** for sound rule sets. -/
theorem simplifyPassSimU {rules : SimplifyFn} {skel : SkeletonFn} (hS : SimplifySound rules)
    (hK : SkeletonSound skel) : SimplifyPassSimU rules skel := by
  intro allowed skelOk remat g info hg hok
  exact simpOk_simU hg hok (simplify_facts hS hK hg) (simplify_sigDecls _ _ _ _ _ _ _)

/-- The proven rule sets satisfy the simplify stage's hypothesis. -/
theorem simplifyPassSimU_proven {cfg : Config} (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) : SimplifyPassSimU cfg.simplifyFn cfg.skeletonFn := by
  cases cfg
  simp only at hr ha
  subst hr ha
  exact simplifyPassSimU Proof.simplifySound_proven Proof.skeletonSound_proven

/-! ## The pipeline -/

set_option maxHeartbeats 1000000 in
/-- **The mid-end pipeline refines with handler edges**, for inputs passing the fresh-value
guard (`optimizeReport_simX`). -/
theorem optimizeReport_simU (cfg : Config)
    (hS : SimplifyPassSimU cfg.simplifyFn cfg.skeletonFn) (f0 : Function)
    (hok : freshOkB f0 = true) :
    FunSimU f0 (optimizeReport cfg f0).1 ∧ (optimizeReport cfg f0).1.sigDecls = f0.sigDecls := by
  have hU := removeUnreachable_simU f0 hok
  have hsdU := removeUnreachable_sigDecls f0
  unfold optimizeReport
  simp only [Id.run]
  split
  · rename_i i hc
    simp only [pure_bind]
    apply forIn_bind_inv (P := fun s : Report × Function × Info × Bool =>
      FunSimU f0 s.2.1 ∧ check s.2.1 = .ok s.2.2.1 ∧ s.2.1.sigDecls = f0.sigDecls)
      (Q := fun x : Function × Report => FunSimU f0 x.1 ∧ x.1.sigDecls = f0.sigDecls)
    · exact ⟨hU, hc, hsdU⟩
    · intro stage s hs
      obtain ⟨hsim, hchk, hsd⟩ := hs
      obtain ⟨r, g, info, stop⟩ := s
      simp only at hsim hchk hsd
      simp only [Id.run]
      repeat' split
      all_goals simp only [pure, ForInStep.value]
      all_goals first
        | with_reducible exact ⟨hsim, hchk, hsd⟩
        | (exfalso; rename_i h _; simp at h; done)
        | (exfalso; rename_i h _; exact absurd (beq_iff_eq.1 h) ‹_›)
        | (rename_i hck' _ hv
           have h1 := hS (allowedIn (removeUnreachable f0)) (skelAllowedIn (removeUnreachable f0))
             cfg.rematConst g info hchk hv
           exact ⟨hsim.trans (h1.trans (removeUnreachable_simU _ (freshOkB_of_check hck'))), hck',
             by rw [removeUnreachable_sigDecls, simplify_sigDecls, hsd]⟩)
        | (rename_i hck' _ hv
           exact ⟨hsim.trans (editOk_simU hchk hck' hv (by
             first
             | rw [gvnFull_sigDecls]
             | rw [dce_sigDecls]
             | rw [licm_sigDecls])), hck', by
             first
             | rw [gvnFull_sigDecls, hsd]
             | rw [dce_sigDecls, hsd]
             | rw [licm_sigDecls, hsd]⟩)
    · intro s hs
      simp only [Id.run, pure]
      split
      · exact ⟨hs.1, hs.2.2⟩
      · exact ⟨FunSimU.refl f0, rfl⟩
  · exact ⟨hU, hsdU⟩

/-- **The mid-end with the fresh-value guard refines with handler edges**, every function. -/
theorem optimizeX_simU (cfg : Config) (hS : SimplifyPassSimU cfg.simplifyFn cfg.skeletonFn)
    (f : Function) : FunSimU f (optimizeX f cfg) := by
  unfold optimizeX
  split
  · exact (optimizeReport_simU cfg hS f ‹_›).1
  · exact FunSimU.refl f

/-- **The mid-end of the executable compiler refines with handler edges**, every function. -/
theorem optimizeExe_simU (cfg : Config) (hS : SimplifyPassSimU cfg.simplifyFn cfg.skeletonFn)
    (f : Function) : FunSimU f (optimizeExe f cfg) := by
  unfold optimizeExe
  dsimp only
  split
  · exact optimizeX_simU cfg hS f
  · exact FunSimU.refl f


/-! ## Programs -/

/-- **The executable compiler's mid-end refines the runs with unwinding**: for related states
(`SRU`; e.g. a program's entry states) the run with unwinding of `optimizeProgramExe p cfg`
matches every return, trap and exception leaving the run of `p` (`XOutcomeRefines`). -/
theorem optimizeProgramExe_refinesU (cfg : Config)
    (hS : SimplifyPassSimU cfg.simplifyFn cfg.skeletonFn) {env : XEnv} (hE : EnvKeepsSymbolsX env)
    (p : Program) {syms : String → Option Nat} (n : Nat) (xs xs' : XState)
    (h : SRU syms xs xs') :
    ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs)
      (Clif.runLoopX env (optimizeProgramExe p cfg) n' xs') :=
  runLoopX_refinesU hE (FunsSimU.map (T := (optimizeExe · cfg)) (optimizeExe_simU cfg hS)) n xs xs' h

end Opt

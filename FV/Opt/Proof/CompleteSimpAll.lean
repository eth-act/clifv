module

public import FV.Opt.Proof.CompleteSimp
public import FV.Opt.Proof.IsleProv
public import FV.Opt.OptimizeX

@[expose] public section

/-!
# Completeness of the mid-end for every configuration (M1, #24)

Every rule set the mid-end runs passes values on: the exported Cranelift rules with any rule
allow-list (`Opt.simpRulesProv_isle`, `Opt.skelRulesProv_isle`, `FV/Opt/Proof/IsleProv.lean`) and
the hand rules (`Opt.simpRulesProv_hand`, `Opt.skelRulesProv_hand`). So the simplify stage is
complete for every `Opt.Config` (`Opt.simpStageOk_cfg`), and so is the whole mid-end
(`Opt.optimize_complete_cfg`): on an input that is well formed once its unreachable blocks are
removed, no stage of `optimizeReport` stops and the result is the unvalidated pipeline
`runStages`. In particular for the configurations actually used: `Opt.exeConfig` (the verified
executables, `--opt-proven-only`; `Opt.optimize_complete_exe`, and for the executable compiler's
entry point `Opt.optimizeExe`, on shape-safe inputs, `Opt.optimizeExe_complete_exe`) and the
default configuration (`cargo fv`'s `--opt`; `Opt.optimize_complete_default`).

`Opt.CompleteSimpAll.witness_exe`: on `v2 = v0 + 0` the Cranelift rules with `exeConfig` rewrite
the result to `v0`, and the theorem applies.
-/

namespace Opt

open Clif

/-- The simplify rules of every configuration pass values on. -/
theorem simpRulesProv_cfg (cfg : Config) : SimpRulesProv cfg.simplifyFn := by
  simp only [Config.simplifyFn]
  cases cfg.rules
  · exact simpRulesProv_isle cfg.ruleAllow.pred
  · exact simpRulesProv_hand

/-- The skeleton rules of every configuration pass values on. -/
theorem skelRulesProv_cfg (cfg : Config) : SkelRulesProv cfg.skeletonFn := by
  simp only [Config.skeletonFn]
  cases cfg.rules
  · exact skelRulesProv_isle cfg.ruleAllow.pred
  · exact skelRulesProv_hand

/-- **Completeness of the simplify stage**, for every configuration. -/
theorem simpStageOk_cfg (cfg : Config) : SimpStageOk cfg :=
  simpStageOk_of (simpRulesProv_cfg cfg) (skelRulesProv_cfg cfg)

/-- **Completeness of the mid-end**, for every configuration: on an input that is well formed
once its unreachable blocks are removed, no stage of `optimizeReport` stops and the result is the
unvalidated pipeline `runStages`. -/
theorem optimize_complete_cfg (cfg : Config) (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) :
    (optimizeReport cfg f0).2.passError = none ∧
      (optimizeReport cfg f0).1 = runStages cfg (removeUnreachable f0) :=
  optimize_complete_of_rules (simpRulesProv_cfg cfg) (skelRulesProv_cfg cfg) f0 h

/-- **Completeness of the mid-end of the verified executables** (`exeConfig`: the Cranelift
rules, proven ones only). -/
theorem optimize_complete_exe (f0 : Function) (h : ∃ i, check (removeUnreachable f0) = .ok i) :
    (optimizeReport exeConfig f0).2.passError = none ∧
      (optimizeReport exeConfig f0).1 = runStages exeConfig (removeUnreachable f0) :=
  optimize_complete_cfg exeConfig f0 h

/-- **Completeness of the mid-end with the default configuration** (the Cranelift rules, all of
them). -/
theorem optimize_complete_default (f0 : Function) (h : ∃ i, check (removeUnreachable f0) = .ok i) :
    (optimizeReport {} f0).2.passError = none ∧
      (optimizeReport {} f0).1 = runStages {} (removeUnreachable f0) :=
  optimize_complete_cfg {} f0 h

/-- **Completeness of the executable compiler's mid-end** `optimizeExe`, for every configuration:
on a shape-safe input that is well formed once its unreachable blocks are removed, it is the
unvalidated pipeline `runStages` (`optimizeExe_complete` with `simpStageOk_cfg`). -/
theorem optimizeExe_complete_cfg (cfg : Config) (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) (hsafe : shapeSafeB f0 = true) :
    optimizeExe f0 cfg = runStages cfg (removeUnreachable f0) :=
  optimizeExe_complete cfg f0 h (.inr (simpStageOk_cfg cfg)) hsafe

/-- **Completeness of the mid-end of the verified executables** at their entry point
(`optimizeExe` with `exeConfig`, as `lean-link`/`Link.compileExeOpt` call it). -/
theorem optimizeExe_complete_exe (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) (hsafe : shapeSafeB f0 = true) :
    optimizeExe f0 exeConfig = runStages exeConfig (removeUnreachable f0) :=
  optimizeExe_complete_cfg exeConfig f0 h hsafe

end Opt

namespace Opt.CompleteSimpAll

open Clif Opt.CompleteSimpWitness

/-- **Non-vacuity of `optimize_complete_exe`**: `fnHand` (`v2 = v0 + 0`) is well formed once its
unreachable blocks are removed, so the theorem applies (no stage stops, the result is the
unvalidated pipeline), and the Cranelift rules of `exeConfig` rewrite the result to `v0`. -/
theorem witness_exe :
    (∃ i, check (removeUnreachable fnHand) = .ok i) ∧
      (optimizeReport exeConfig fnHand).2.passError = none ∧
      (optimizeReport exeConfig fnHand).1 = runStages exeConfig (removeUnreachable fnHand) ∧
      (optimizeReport exeConfig fnHand).1.blocks.map (·.term) = [.ret [0]] := by
  have hc : ∃ i, check (removeUnreachable fnHand) = .ok i := by
    have h0 : (match check (removeUnreachable fnHand) with
        | .ok _ => true | .error _ => false) = true := by native_decide
    split at h0
    · rename_i i hi; exact ⟨i, hi⟩
    · cases h0
  exact ⟨hc, optimize_complete_exe fnHand hc |>.1, optimize_complete_exe fnHand hc |>.2,
    by native_decide⟩

/-- **Non-vacuity of `optimizeExe_complete_exe`**: `fnHand` is also shape-safe, so the executable
compiler's `optimizeExe` with `exeConfig` is the unvalidated pipeline on it, which returns `v0`. -/
theorem witness_exe_entry :
    shapeSafeB fnHand = true ∧
      optimizeExe fnHand exeConfig = runStages exeConfig (removeUnreachable fnHand) ∧
      (optimizeExe fnHand exeConfig).blocks.map (·.term) = [.ret [0]] := by
  have hs : shapeSafeB fnHand = true := by native_decide
  exact ⟨hs, optimizeExe_complete_exe fnHand witness_exe.1 hs, by native_decide⟩

end Opt.CompleteSimpAll

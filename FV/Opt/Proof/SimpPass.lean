import FV.Opt.Proof.SimpLoop
import FV.Opt.Proof.Pipeline
import FV.Opt.Proof.RuleAll

/-!
# The simplify stage refines (`Opt.simplifyPassSim`)

The hypothesis `Opt.SimplifyPassSim` of the pipeline theorems (`FV/Opt/Proof/Pipeline.lean`),
proven for sound rule sets: every run of the pass has its semantic facts
(`Opt.simplify_facts`, `FV/Opt/Proof/SimpLoop.lean`), and the validator `simpOk` together with
the facts gives the simulation (`Opt.simpOk_sim`, `FV/Opt/Proof/SimpSim.lean`).

With the proven rule sets (`Config.ruleAllow := .proven`, the Cranelift rules:
`Opt.Proof.simplifySound_proven`, `Opt.Proof.skeletonSound_proven`) the whole pipeline refines
unconditionally (`Opt.optimize_sim_proven`).
-/

namespace Opt

open Clif

/-- **The simplify stage refines** for sound rule sets. -/
theorem simplifyPassSim {rules : SimplifyFn} {skel : SkeletonFn} (hS : SimplifySound rules)
    (hK : SkeletonSound skel) : SimplifyPassSim rules skel := by
  intro allowed skelOk remat g info hg hok
  exact simpOk_sim hg hok (simplify_facts hS hK hg)

/-- The proven rule sets satisfy the simplify stage's hypothesis. -/
theorem simplifyPassSim_proven {cfg : Config} (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) : SimplifyPassSim cfg.simplifyFn cfg.skeletonFn := by
  cases cfg
  simp only at hr ha
  subst hr ha
  exact simplifyPassSim Proof.simplifySound_proven Proof.skeletonSound_proven

/-- **The mid-end refines with the proven rule sets**: `FunSim f (optimize f cfg)` for every `f`. -/
theorem optimize_sim_proven {cfg : Config} (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) (f : Function) : FunSim f (optimize f cfg) :=
  optimize_sim cfg (simplifyPassSim_proven hr ha) f

end Opt

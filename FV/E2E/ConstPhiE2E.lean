import FV.E2E.PassX
import FV.E2E.ConstPhiShape

/-! # Constant-phi removal in the end-to-end theorems (#990)

`lean-backend` runs constant-phi removal (`Opt.ConstPhi.run`) on every function after the `i128`
legalisation and before the mid-end and the backend, as Cranelift runs `remove_constant_phis`
before its egraph pass. The theorems of `FV/E2E/PassX.lean` are stated for any pass `T` whose
output simulates its input (`Opt.FunSimX`, with the handler edges `Opt.FunSimU`) and keeps its
shape (`ShapeFacts`). Here are the two passes `lean-backend` runs:

* `Opt.ConstPhi.run` (`run_simX`, `run_simU`, `run_shape`): without `--opt`;
* `Opt.ConstPhi.runOpt cfg`, the pass followed by the mid-end of the executable compiler
  `Opt.optimizeExe · cfg` (`runOpt_simX`, `runOpt_simU`, `runOpt_shape`, for the proven rule
  sets): with `--opt --opt-proven-only`.

For example, `E2E.backend_correct_pass_cleanup (T := Opt.ConstPhi.run) Opt.ConstPhi.run_simX
Opt.ConstPhi.run_shape` is the per-function theorem of `lean-backend`'s default compiler
(`backend_correct_final_cleanup` composed with the pass). Non-vacuity: `FV/E2E/ConstPhiE2EWitness.lean`.
-/

namespace Opt.ConstPhi

/-- **Constant-phi removal followed by the mid-end** (`lean-backend --opt`). -/
def runOpt (cfg : Opt.Config) (f : Clif.Function) : Clif.Function :=
  Opt.optimizeExe (run f) cfg

theorem runOpt_simX (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) (f : Clif.Function) : Opt.FunSimX f (runOpt cfg f) :=
  (run_simX f).trans (Opt.optimizeExe_simX cfg (Opt.simplifyPassSimX_proven hr ha) (run f))

theorem runOpt_simU (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) (f : Clif.Function) : Opt.FunSimU f (runOpt cfg f) :=
  (run_simU f).trans (Opt.optimizeExe_simU cfg (Opt.simplifyPassSimU_proven hr ha) (run f))

theorem runOpt_shape (cfg : Opt.Config) (f : Clif.Function) : E2E.ShapeFacts f (runOpt cfg f) :=
  (run_shape f).trans (E2E.optimizeExe_shape cfg (run f))

end Opt.ConstPhi

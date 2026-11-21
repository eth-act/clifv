import FV.E2E.NotrapDropShape
import FV.E2E.ConstPhiE2E
import FV.Link.ConstPhiPair

/-!
# The end-to-end theorems over constant-phi removal and the drop of unused `notrap` loads
(option D, #1017)

`lean-backend` (option D) compiles every function after the `i128` legalisation, constant-phi
removal and, last before lowering, the drop of unused `notrap` loads (`Opt.NotrapDrop.run`,
Cranelift 0.136.1's `must_lower_even_if_unused`). The theorems of `FV/E2E/PassX.lean` hold for
any pass `T` whose output simulates its input and keeps its shape; here are the instances:

* `runCp f = NotrapDrop.run (ConstPhi.run f)` (`runCp_simX`, `runCp_simU`, `runCp_shape`), without
  `--opt`;
* `runCpOpt cfg f = NotrapDrop.run (ConstPhi.runOpt cfg f)`, with `--opt --opt-proven-only`;
* the linked compiler's pairs `run_pair`, `runCp_pair` (`Link.OptPair`).

For example `E2E.backend_correct_pass_cleanup (T := Opt.NotrapDrop.runCp)
Opt.NotrapDrop.runCp_simX Opt.NotrapDrop.runCp_shape` is the per-function theorem of the default
compiler with the drop (`FVTest/Opt/NotrapDropWitness.lean`).
-/

namespace Opt.NotrapDrop

/-- **Constant-phi removal, then the drop.** -/
def runCp (f : Clif.Function) : Clif.Function := run (ConstPhi.run f)

theorem runCp_simX (f : Clif.Function) : Opt.FunSimX f (runCp f) :=
  (ConstPhi.run_simX f).trans (run_simX _)

theorem runCp_simU (f : Clif.Function) : Opt.FunSimU f (runCp f) :=
  (ConstPhi.run_simU f).trans (run_simU _)

theorem runCp_shape (f : Clif.Function) : E2E.ShapeFacts f (runCp f) :=
  (ConstPhi.run_shape f).trans (run_shape _)

/-- **Constant-phi removal, the mid-end, then the drop** (`lean-backend --opt`). -/
def runCpOpt (cfg : Opt.Config) (f : Clif.Function) : Clif.Function := run (ConstPhi.runOpt cfg f)

theorem runCpOpt_simX (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) (f : Clif.Function) : Opt.FunSimX f (runCpOpt cfg f) :=
  (ConstPhi.runOpt_simX cfg hr ha f).trans (run_simX _)

theorem runCpOpt_simU (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) (f : Clif.Function) : Opt.FunSimU f (runCpOpt cfg f) :=
  (ConstPhi.runOpt_simU cfg hr ha f).trans (run_simU _)

theorem runCpOpt_shape (cfg : Opt.Config) (f : Clif.Function) :
    E2E.ShapeFacts f (runCpOpt cfg f) :=
  (ConstPhi.runOpt_shape cfg f).trans (run_shape _)

/-- **The drop's output and input are an `OptPair`** (the linked compiler's composition). -/
theorem run_pair (f : Clif.Function) : Link.OptPair f (run f) :=
  ⟨run_simX f, run_shape f⟩

theorem runCp_pair (f : Clif.Function) : Link.OptPair f (runCp f) :=
  ⟨runCp_simX f, runCp_shape f⟩

end Opt.NotrapDrop

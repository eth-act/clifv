import FV.Opt.Proof.MidValSim
import FV.Opt.Proof.ConstPhiSimU

/-!
# Programs through the mid-end validator (#1119, module (5))

`Validated fs gs`: each function of `gs` is the corresponding function of `fs`, or Cranelift's
optimised function `g` accepted by the re-check against `f` after constant-phi removal
(`checkCert (ConstPhi.run f) g cert = true`, the pair `midval-check` measures). Then
`validated_refines`: the runs with unwinding of the two programs refine, with exactly the
conclusion of `Opt.runLoopX_refinesU` (`XOutcomeRefines`: a source run that returns, traps or
unwinds within `n` steps is matched by a target run with the same outcome), via
`ConstPhi.run_simU` (`FunSimU f (ConstPhi.run f)`), `FunSimU.toMU`, `check_sound` and
`FunSimMU.trans`.
-/

namespace Opt.MidVal

open Clif

/-- `g` stands for `f` through the validator (module doc). -/
theorem checked_simMU {f g : Function} {cert : Cert}
    (h : checkCert (ConstPhi.run f) g cert = true) : FunSimMU f g :=
  (ConstPhi.run_simU f).toMU.trans (check_sound h)

/-- Pointwise: the same function, or a validated optimised one (module doc). -/
inductive Validated : List Function → List Function → Prop
  | nil : Validated [] []
  | same {f : Function} {fs gs : List Function} : Validated fs gs → Validated (f :: fs) (f :: gs)
  | checked {f g : Function} {fs gs : List Function} (cert : Cert) :
      checkCert (ConstPhi.run f) g cert = true → Validated fs gs → Validated (f :: fs) (g :: gs)

theorem Validated.funsSimMU {fs gs : List Function} (h : Validated fs gs) : FunsSimMU fs gs := by
  induction h with
  | nil => exact .nil
  | same _ ih => exact .cons (FunSimMU.refl _) ih
  | checked _ hc _ ih => exact .cons (checked_simMU hc) ih

/-- **Program refinement through the mid-end validator.** -/
theorem validated_refines {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hv : Validated p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') :=
  runLoopX_refinesMU hE hv.funsSimMU

end Opt.MidVal

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

The hoisting mode: `ValidatedSyms syms fs gs` also allows a `g` accepted by `checkCertSyms`
against `ConstPhi.run f` whose global values resolve in `syms` (`globalsResolve`); then
`validated_refines_syms` gives the same conclusion for the runs at `syms`, through
`check_soundSyms` and `Opt.runLoopX_refinesMUAt`.
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

/-- `g` stands for `f` through the hoisting mode, at a symbol table where the global values of
`f` (after constant-phi removal) resolve. -/
theorem checkedSyms_simMUAt {f g : Function} {cert : Cert} {syms : String → Option Nat}
    (h : checkCertSyms (ConstPhi.run f) g cert = true)
    (hres : globalsResolve (ConstPhi.run f) syms = true) : FunSimMUAt syms f g :=
  ((ConstPhi.run_simU f).toMU.at syms).trans (check_soundSyms h hres)

/-- Pointwise at the symbol table `syms`: the same function, a validated optimised one, or one
validated in the hoisting mode whose global values resolve in `syms`. -/
inductive ValidatedSyms (syms : String → Option Nat) : List Function → List Function → Prop
  | nil : ValidatedSyms syms [] []
  | same {f : Function} {fs gs : List Function} : ValidatedSyms syms fs gs →
      ValidatedSyms syms (f :: fs) (f :: gs)
  | checked {f g : Function} {fs gs : List Function} (cert : Cert) :
      checkCert (ConstPhi.run f) g cert = true → ValidatedSyms syms fs gs →
      ValidatedSyms syms (f :: fs) (g :: gs)
  | checkedSyms {f g : Function} {fs gs : List Function} (cert : Cert) :
      checkCertSyms (ConstPhi.run f) g cert = true →
      globalsResolve (ConstPhi.run f) syms = true → ValidatedSyms syms fs gs →
      ValidatedSyms syms (f :: fs) (g :: gs)

theorem ValidatedSyms.funsSimMUAt {syms : String → Option Nat} {fs gs : List Function}
    (h : ValidatedSyms syms fs gs) : FunsSimMUAt syms fs gs := by
  induction h with
  | nil => exact .nil
  | same _ ih => exact .cons ((FunSimMU.refl _).at syms) ih
  | checked _ hc _ ih => exact .cons ((checked_simMU hc).at syms) ih
  | checkedSyms _ hc hres _ ih => exact .cons (checkedSyms_simMUAt hc hres) ih

/-- **Program refinement through the mid-end validator with the hoisting mode**, for the runs
at a symbol table `syms` in which the global values of every function validated in that mode
resolve. -/
theorem validated_refines_syms {syms : String → Option Nat} {env : XEnv}
    (hE : EnvKeepsSymbolsX env) {p q : Program} (hv : ValidatedSyms syms p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') :=
  runLoopX_refinesMUAt hE hv.funsSimMUAt

end Opt.MidVal

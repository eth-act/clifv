import FV.Opt.Proof.MidValProg
import FV.Opt.Proof.MidValCondSim
import FV.Opt.Proof.MidValDiv

/-!
# The re-check with branch-condition hints is sound (#1119 family 3, route D)

`checkCertC f g cert hints` (`FV/Opt/MidValCond.lean`) is `checkCert f g cert` without hints,
and otherwise `refsOk g` and `checkCert f (condPrep g hints) cert`, or, with fold requests `bs`
(`foldBlocks hints`), `checkCert (foldPre f bs) (condPrep g hints) cert`. Its soundness composes
the re-check's (`check_sound_norm`: `FunSimMU f (condPrep g hints)`, or `check_sound`:
`FunSimMU (foldPre f bs) (condPrep g hints)`) with `condPrep_simU` (`FunSimU (condPrep g hints)
g`) by `FunSimMU.trans`, and with fold requests first with `foldPre_simU` (`FunSimU f (foldPre f
bs)`, `FV/Opt/Proof/MidValFold.lean`); the compiled function is `g` itself.

* **`check_soundC_norm`**, **`check_soundC_normT`** (a normaliser sound under typing),
  **`check_soundC`** (default normaliser `Norm.stdT f`), **`check_soundSymsC`**
  (hoisting mode, at a symbol table where `f`'s global values resolve);
* **`checkedC_simMU`**: through constant-phi removal, as `checked_simMU`;
* `ValidatedC`, `ValidatedSymsC`: `Validated`/`ValidatedSyms` with `checkCertC`/`checkCertSymsC`
  (every `Validated` pair list is a `ValidatedC` one: `Validated.toC`), and
  **`validatedC_refines`**, **`validatedC_refines_syms`**: the program refinements, with the
  conclusions of `validated_refines`/`validated_refines_syms`.

The theorems on main (`check_sound`, `validated_refines`, …) are unchanged.
-/

namespace Opt.MidVal

open Clif

theorem check_soundC_norm {f g : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    {norm : Norm} (h : checkCertC f g cert hints norm = true) (hN : NormSound norm) :
    FunSimMU f g := by
  unfold checkCertC at h
  split at h
  · exact check_sound_norm h hN
  · split at h
    · simp only [Bool.and_eq_true] at h
      exact (check_sound_norm h.2 hN).trans (condPrep_simU h.1).toMU
    · simp only [Bool.and_eq_true] at h
      exact (foldPre_simU f _).toMU.trans ((check_sound h.2).trans (condPrep_simU h.1).toMU)

theorem check_soundC_normT {f g : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    {norm : Norm} (h : checkCertC f g cert hints norm = true) (hN : NormSoundT f norm) :
    FunSimMU f g := by
  unfold checkCertC at h
  split at h
  · exact check_sound_normT h hN
  · split at h
    · simp only [Bool.and_eq_true] at h
      exact (check_sound_normT h.2 hN).trans (condPrep_simU h.1).toMU
    · simp only [Bool.and_eq_true] at h
      exact (foldPre_simU f _).toMU.trans ((check_sound h.2).trans (condPrep_simU h.1).toMU)

/-- **Soundness of the re-check with branch-condition hints** (default normaliser). -/
theorem check_soundC {f g : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    (h : checkCertC f g cert hints = true) : FunSimMU f g :=
  check_soundC_normT h normSoundT_stdT

/-- **Soundness of the hoisting mode with branch-condition hints.** -/
theorem check_soundSymsC {f g : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    (h : checkCertSymsC f g cert hints = true) {syms : String → Option Nat}
    (hres : globalsResolve f syms = true) : FunSimMUAt syms f g := by
  unfold checkCertSymsC at h
  split at h
  · exact check_soundSyms h hres
  · simp only [Bool.and_eq_true] at h
    exact (check_soundSyms h.2 hres).trans ((condPrep_simU h.1).toMU.at syms)

theorem checkCertC_nil {f g : Function} {cert : Cert} {norm : Norm} :
    checkCertC f g cert [] norm = checkCert f g cert norm := rfl

/-- `g` stands for `f` through constant-phi removal and the re-check with hints. -/
theorem checkedC_simMU {f g : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    (h : checkCertC (ConstPhi.run f) g cert hints = true) : FunSimMU f g :=
  (ConstPhi.run_simU f).toMU.trans (check_soundC h)

/-- `g` stands for `f` at `syms` through the hoisting mode with hints. -/
theorem checkedSymsC_simMUAt {f g : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    {syms : String → Option Nat} (h : checkCertSymsC (ConstPhi.run f) g cert hints = true)
    (hres : globalsResolve (ConstPhi.run f) syms = true) : FunSimMUAt syms f g :=
  ((ConstPhi.run_simU f).toMU.at syms).trans (check_soundSymsC h hres)

/-- Pointwise: the same function, or an optimised one accepted by the re-check with hints. -/
inductive ValidatedC : List Function → List Function → Prop
  | nil : ValidatedC [] []
  | same {f : Function} {fs gs : List Function} : ValidatedC fs gs → ValidatedC (f :: fs) (f :: gs)
  | checked {f g : Function} {fs gs : List Function} (cert : Cert)
      (hints : List (BlockId × List Wrap)) :
      checkCertC (ConstPhi.run f) g cert hints = true → ValidatedC fs gs →
        ValidatedC (f :: fs) (g :: gs)

theorem Validated.toC {fs gs : List Function} (h : Validated fs gs) : ValidatedC fs gs := by
  induction h with
  | nil => exact .nil
  | same _ ih => exact .same ih
  | checked cert hc _ ih => exact .checked cert [] hc ih

theorem ValidatedC.funsSimMU {fs gs : List Function} (h : ValidatedC fs gs) : FunsSimMU fs gs := by
  induction h with
  | nil => exact .nil
  | same _ ih => exact .cons (FunSimMU.refl _) ih
  | checked _ _ hc _ ih => exact .cons (checkedC_simMU hc) ih

/-- **Program refinement through the mid-end validator with branch-condition hints.** -/
theorem validatedC_refines {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hv : ValidatedC p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') :=
  runLoopX_refinesMU hE hv.funsSimMU

/-- Pointwise at `syms`: `ValidatedSyms` with the re-checks with hints. -/
inductive ValidatedSymsC (syms : String → Option Nat) : List Function → List Function → Prop
  | nil : ValidatedSymsC syms [] []
  | same {f : Function} {fs gs : List Function} : ValidatedSymsC syms fs gs →
      ValidatedSymsC syms (f :: fs) (f :: gs)
  | checked {f g : Function} {fs gs : List Function} (cert : Cert)
      (hints : List (BlockId × List Wrap)) :
      checkCertC (ConstPhi.run f) g cert hints = true → ValidatedSymsC syms fs gs →
      ValidatedSymsC syms (f :: fs) (g :: gs)
  | checkedSyms {f g : Function} {fs gs : List Function} (cert : Cert)
      (hints : List (BlockId × List Wrap)) :
      checkCertSymsC (ConstPhi.run f) g cert hints = true →
      globalsResolve (ConstPhi.run f) syms = true → ValidatedSymsC syms fs gs →
      ValidatedSymsC syms (f :: fs) (g :: gs)

theorem ValidatedSyms.toC {syms : String → Option Nat} {fs gs : List Function}
    (h : ValidatedSyms syms fs gs) : ValidatedSymsC syms fs gs := by
  induction h with
  | nil => exact .nil
  | same _ ih => exact .same ih
  | checked cert hc _ ih => exact .checked cert [] hc ih
  | checkedSyms cert hc hres _ ih => exact .checkedSyms cert [] hc hres ih

theorem ValidatedSymsC.funsSimMUAt {syms : String → Option Nat} {fs gs : List Function}
    (h : ValidatedSymsC syms fs gs) : FunsSimMUAt syms fs gs := by
  induction h with
  | nil => exact .nil
  | same _ ih => exact .cons ((FunSimMU.refl _).at syms) ih
  | checked _ _ hc _ ih => exact .cons ((checkedC_simMU hc).at syms) ih
  | checkedSyms _ _ hc hres _ ih => exact .cons (checkedSymsC_simMUAt hc hres) ih

/-- **Program refinement through the hoisting mode with branch-condition hints**, at a symbol
table in which the global values of every function validated in that mode resolve. -/
theorem validatedC_refines_syms {syms : String → Option Nat} {env : XEnv}
    (hE : EnvKeepsSymbolsX env) {p q : Program} (hv : ValidatedSymsC syms p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') :=
  runLoopX_refinesMUAt hE hv.funsSimMUAt

end Opt.MidVal

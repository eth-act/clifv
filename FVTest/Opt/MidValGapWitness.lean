import FVTest.Opt.MidValWitness

/-! # The validator's closed gaps on real pairs (#1119 follow-up)

Three pairs of the measured release crates (crypto-bigint 0.7.11's test build; cg_clif's
unoptimised dump and Cranelift's optimised function, `FVTest/Opt/midval/real_*.{unopt,opt}.clif`,
the dumps as written), each accepted only since the gap it shows was closed; the certificates are
the ones `Opt.MidVal.emit` produces, the re-checks are decided (`native_decide`, witness) and the
soundness theorems instantiated, no premise assumed except the hoisting mode's own:

* `callind` (`_RNxC8proptest12H7K1hCCcMXYD`, `FnOnce::call_once` shim of a `fn()` pointer): a
  `call_indirect`; `Opt.check` rejects the function (no result types for it), `wfCheck` types it
  from the signature declarations, and `check_sound` gives `FunSimMU`;
* `bitcast` (`core::intrinsics::bounds::…::to_bits`): an `f64 → i64` `bitcast`, ill-typed for
  `Opt.pureTyped`, typed by width (`pureTypedM`);
* `hoist` (`_RNxC10rayon_core12HlO039y8Reib`): `g` evaluates a `symbol_value` before `f` does; the
  plain re-check rejects it, the hoisting mode (`checkCertSyms`) accepts it, and `check_soundSyms`
  gives `FunSimMUAt syms` at every symbol table where the function's global values resolve,
  e.g. one that maps every name to `0` (`hoist_resolves`, so the premise is satisfiable). -/

namespace Opt.MidVal.GapWitness

open Clif

def callindF : String := include_str "midval/real_callind.unopt.clif"
def callindG : String := include_str "midval/real_callind.opt.clif"
def bitcastF : String := include_str "midval/real_bitcast.unopt.clif"
def bitcastG : String := include_str "midval/real_bitcast.opt.clif"
def hoistF : String := include_str "midval/real_hoist.unopt.clif"
def hoistG : String := include_str "midval/real_hoist.opt.clif"

/-- A decoded pair and the certificate `emit` gives for it (after constant-phi removal of `f`). -/
def pairOf (fT gT : String) (hoist : Bool) : Option (Function × Function × Cert) := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  let cert ← (emit (ConstPhi.run f) g Norm.id hoist).toOption
  pure (f, g, cert)

theorem pair_of {fT gT : String} {hoist : Bool}
    (h : ((pairOf fT gT hoist).map fun p =>
      checkCertWith hoist (ConstPhi.run p.1) p.2.1 p.2.2 Norm.id) = some true) :
    ∃ f g cert, pairOf fT gT hoist = some (f, g, cert) ∧
      checkCertWith hoist (ConstPhi.run f) g cert Norm.id = true := by
  cases hp : pairOf fT gT hoist with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨f, g, cert⟩ := p
    rw [hp] at h
    exact ⟨f, g, cert, rfl, by simpa using h⟩

/-! ## `call_indirect` -/

/-- `Opt.check` rejects the unoptimised function (the gap). -/
theorem callind_check_rejects :
    ((pairOf callindF callindG false).map fun p => (Opt.check (ConstPhi.run p.1)).isOk) =
      some false := by
  native_decide

/-- The re-check accepts (decided). -/
theorem callind_checked :
    ((pairOf callindF callindG false).map fun p =>
      checkCertWith false (ConstPhi.run p.1) p.2.1 p.2.2 Norm.id) = some true := by
  native_decide

/-- **Soundness on the `call_indirect` pair.** -/
theorem callind_simMU : ∃ f g, ((pairOf callindF callindG false).map fun p => (p.1, p.2.1)) =
    some (f, g) ∧ FunSimMU f g := by
  obtain ⟨f, g, cert, hp, hc⟩ := pair_of callind_checked
  exact ⟨f, g, by rw [hp]; rfl, checked_simMU hc⟩

/-! ## `bitcast` -/

/-- `Opt.check` rejects the unoptimised function (the gap). -/
theorem bitcast_check_rejects :
    ((pairOf bitcastF bitcastG false).map fun p => (Opt.check (ConstPhi.run p.1)).isOk) =
      some false := by
  native_decide

/-- The re-check accepts (decided). -/
theorem bitcast_checked :
    ((pairOf bitcastF bitcastG false).map fun p =>
      checkCertWith false (ConstPhi.run p.1) p.2.1 p.2.2 Norm.id) = some true := by
  native_decide

/-- **Soundness on the `bitcast` pair.** -/
theorem bitcast_simMU : ∃ f g, ((pairOf bitcastF bitcastG false).map fun p => (p.1, p.2.1)) =
    some (f, g) ∧ FunSimMU f g := by
  obtain ⟨f, g, cert, hp, hc⟩ := pair_of bitcast_checked
  exact ⟨f, g, by rw [hp]; rfl, checked_simMU hc⟩

/-! ## A hoisted `symbol_value` -/

/-- The plain check rejects the pair (`g` evaluates the `symbol_value` before `f` does). -/
theorem hoist_plain_rejects :
    ((RealWitness.decode hoistF).bind fun f => (RealWitness.decode hoistG).map fun g =>
      (check (ConstPhi.run f) g).isOk) = some false := by
  native_decide

/-- The re-check in the hoisting mode accepts (decided). -/
theorem hoist_checked :
    ((pairOf hoistF hoistG true).map fun p =>
      checkCertWith true (ConstPhi.run p.1) p.2.1 p.2.2 Norm.id) = some true := by
  native_decide

/-- The premise is satisfiable: the function's global values resolve in a symbol table that maps
every name to `0` (decided). -/
theorem hoist_resolves :
    ((pairOf hoistF hoistG true).map fun p =>
      globalsResolve (ConstPhi.run p.1) (fun _ => some 0)) = some true := by
  native_decide

/-- **Soundness of the hoisting mode on the pair**: the simulation at every symbol table where the
function's global values resolve, and the program corollary at one such table. -/
theorem hoist_sim : ∃ f g, ((pairOf hoistF hoistG true).map fun p => (p.1, p.2.1)) =
    some (f, g) ∧ globalsResolve (ConstPhi.run f) (fun _ => some 0) = true ∧
    (∀ syms, globalsResolve (ConstPhi.run f) syms = true → FunSimMUAt syms f g) ∧
    ∀ (env : XEnv), EnvKeepsSymbolsX env →
      ∀ n (xs xs' : XState), SRU (fun _ => some 0) xs xs' →
        ∃ n', XOutcomeRefines (Clif.runLoopX env { funcs := [f] } n xs)
          (Clif.runLoopX env { funcs := [g] } n' xs') := by
  obtain ⟨f, g, cert, hp, hc⟩ := pair_of hoist_checked
  have hres := hoist_resolves
  rw [hp] at hres
  simp only [Option.map_some, Option.some.injEq] at hres
  exact ⟨f, g, by rw [hp]; rfl, hres, fun syms h => checkedSyms_simMUAt hc h, fun env hE =>
    validated_refines_syms (p := { funcs := [f] }) (q := { funcs := [g] }) hE
      (.checkedSyms cert hc hres .nil)⟩

end Opt.MidVal.GapWitness

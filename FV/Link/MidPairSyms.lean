import FV.Link.MidPair
import FV.Opt.Proof.MidValSymsSim

/-! # The mid-end validator's decision at the executable's symbol table (#1119, hoisting)

Cranelift's loop-invariant code motion hoists a `symbol_value` (`tls_value`, `func_addr`) out of a
loop, so `g` evaluates it where `f` may have left the loop; no simulation at every symbol table
relates such a pair (`neg_symhoist`), so `midPairB` rejects it. At the symbol table `syms` of an
executable where the global values of the compared copy of `f` resolve, the hoisting mode relates
them (`Opt.MidVal.checkCertSymsAt_sound`). `link-check` and `lean-link` hold that table and decide:

* `hoistCopy f g`: the copy of `f` (after constant-phi removal) that the hoisting-mode re-check
  `Opt.MidVal.symsCopy` accepts `g` against, with the certificate and hints `Opt.MidVal.emitC`
  computes in the hoisting mode (`hoist := true`); `none` if it rejects. No symbol table:
  `lean-backend` decides `(hoistCopy f g).isSome` per function;
* `midPairSymsB syms f g`: `midPairB f g`, or `hoistCopy f g = some f'` with
  `Opt.MidVal.globalsResolve f' syms` (`syms`: the executable's symbol table);
* `midValidatedSymsB syms fs gs`: equal lengths and pointwise `midPairSymsB syms`;
* **`midPairSymsB_sound`**, **`midValidatedSymsB_sound`**: then `Opt.FunSimMUAt syms f g`,
  `Opt.FunsSimMUAt syms fs gs`, the premise of `Link.midProgAt` and of the `…MidS` / `…_midS`
  theorems.

`emitC` is untrusted: only `symsCopy`'s verdict on its output is used.
-/

namespace Link

/-- **The copy of `f` the hoisting mode accepts `g` against** (module doc), or `none`. -/
def hoistCopy (f g : Clif.Function) : Option Clif.Function :=
  match Opt.MidVal.emitC (Opt.ConstPhi.run f) g (hoist := true) with
  | .ok (c, h) => Opt.MidVal.symsCopy (Opt.ConstPhi.run f) g c h
  | .error _ => none

/-- **The per-function decision at the symbol table `syms`** (module doc). -/
def midPairSymsB (syms : String → Option Nat) (f g : Clif.Function) : Bool :=
  midPairB f g || match hoistCopy f g with
    | some f' => Opt.MidVal.globalsResolve f' syms
    | none => false

/-- **The decision on two programs' function lists at `syms`**: pointwise `midPairSymsB`, equal
lengths. -/
def midValidatedSymsB (syms : String → Option Nat) :
    List Clif.Function → List Clif.Function → Bool
  | [], [] => true
  | f :: fs, g :: gs => midPairSymsB syms f g && midValidatedSymsB syms fs gs
  | _, _ => false

/-- What `hoistCopy` decides: `g` simulates `f` at every symbol table where the copy's global
values resolve. -/
theorem hoistCopy_sound {f g f' : Clif.Function} (h : hoistCopy f g = some f')
    {syms : String → Option Nat} (hres : Opt.MidVal.globalsResolve f' syms = true) :
    Opt.FunSimMUAt syms f g := by
  unfold hoistCopy at h
  split at h
  · exact ((Opt.ConstPhi.run_simU f).toMU.at syms).trans
      (Opt.MidVal.symsCopy_soundD h Opt.MidVal.normSoundD_stdD hres)
  · cases h

/-- **Soundness of the per-function decision at `syms`.** -/
theorem midPairSymsB_sound {syms : String → Option Nat} {f g : Clif.Function}
    (h : midPairSymsB syms f g = true) : Opt.FunSimMUAt syms f g := by
  unfold midPairSymsB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases midPairB_sound h with rfl | ⟨cert, hints, hc⟩
    · exact (Opt.FunSimMU.refl f).at syms
    · exact (Opt.MidVal.checkedC_simMU hc).at syms
  · split at h
    · rename_i f' hc
      exact hoistCopy_sound hc h
    · cases h

/-- **Soundness of the decision**: `midValidatedSymsB syms fs gs = true` gives
`Opt.FunsSimMUAt syms fs gs`. -/
theorem midValidatedSymsB_sound {syms : String → Option Nat} : ∀ {fs gs : List Clif.Function},
    midValidatedSymsB syms fs gs = true → Opt.FunsSimMUAt syms fs gs
  | [], [], _ => .nil
  | f :: fs, g :: gs, h => by
    simp only [midValidatedSymsB, Bool.and_eq_true] at h
    exact .cons (midPairSymsB_sound h.1) (midValidatedSymsB_sound h.2)
  | [], _ :: _, h => by simp [midValidatedSymsB] at h
  | _ :: _, [], h => by simp [midValidatedSymsB] at h

/-- Every pair `midValidatedB` accepts, `midValidatedSymsB` accepts at every symbol table. -/
theorem midValidatedSymsB_of : ∀ {fs gs : List Clif.Function} (syms : String → Option Nat),
    midValidatedB fs gs = true → midValidatedSymsB syms fs gs = true
  | [], [], _, _ => rfl
  | f :: fs, g :: gs, syms, h => by
    simp only [midValidatedB, Bool.and_eq_true] at h
    simp only [midValidatedSymsB, midPairSymsB, h.1, Bool.true_or, Bool.true_and]
    exact midValidatedSymsB_of syms h.2
  | [], _ :: _, _, h => by simp [midValidatedB] at h
  | _ :: _, [], _, h => by simp [midValidatedB] at h

end Link

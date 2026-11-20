import FV.Opt.MidValCond
import FV.Opt.Proof.MidValCondProg

/-! # The mid-end validator's decision on a bundle (#1119, plumbing layer 2)

With `--midval`, a bundle entry carries cg_clif's source function `f` (`.unopt.clif`) and the
function that is compiled, `g` (Cranelift's `.opt.clif` where the validator accepted it, else `f`
itself). `lean-link` and `link-check` re-decide every pair on the bundle's own texts:

* `midPairB f g`: `g` is `f`, or the certificate and branch-condition hints `Opt.MidVal.emitC`
  computes for `(ConstPhi.run f, g)` pass the re-check `Opt.MidVal.checkCertC` (without the
  hoisting mode: `emitC`'s default `hoist := false`);
* `midValidatedB fs gs`: the lists have the same length and every pair passes `midPairB`;
* **`midValidatedB_sound`**: then `Opt.MidVal.ValidatedC fs gs`, the premise of `Link.midProg`
  and of the `…Mid` / `…_mid` theorems.

`emitC` is untrusted: only `checkCertC`'s verdict on its output is used.
-/

namespace Link

/-- **The per-function decision** (module doc): `g` is `f`, or the certificate and hints `emitC`
computes for the pair pass the re-check `checkCertC` against `f` after constant-phi removal. -/
def midPairB (f g : Clif.Function) : Bool :=
  decide (f = g) ||
    match Opt.MidVal.emitC (Opt.ConstPhi.run f) g with
    | .ok (c, h) => Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g c h
    | .error _ => false

/-- **The decision on two programs' function lists**: pointwise `midPairB`, equal lengths. -/
def midValidatedB : List Clif.Function → List Clif.Function → Bool
  | [], [] => true
  | f :: fs, g :: gs => midPairB f g && midValidatedB fs gs
  | _, _ => false

/-- What `midPairB` decides: the same function, or a certificate and hints passing the re-check. -/
theorem midPairB_sound {f g : Clif.Function} (h : midPairB f g = true) :
    f = g ∨ ∃ cert hints, Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true := by
  unfold midPairB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact .inl (of_decide_eq_true h)
  · refine .inr ?_
    split at h
    · exact ⟨_, _, h⟩
    · cases h

/-- **Soundness of the decision**: `midValidatedB fs gs = true` gives `Opt.MidVal.ValidatedC fs gs`. -/
theorem midValidatedB_sound : ∀ {fs gs : List Clif.Function},
    midValidatedB fs gs = true → Opt.MidVal.ValidatedC fs gs
  | [], [], _ => .nil
  | f :: fs, g :: gs, h => by
    simp only [midValidatedB, Bool.and_eq_true] at h
    rcases midPairB_sound h.1 with rfl | ⟨cert, hints, hc⟩
    · exact .same (midValidatedB_sound h.2)
    · exact .checked cert hints hc (midValidatedB_sound h.2)
  | [], _ :: _, h => by simp [midValidatedB] at h
  | _ :: _, [], h => by simp [midValidatedB] at h

end Link

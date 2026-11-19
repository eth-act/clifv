import FV.Opt.MidValCert
import FV.Opt.Proof.MidValProg

/-! # The mid-end validator's decision on a bundle (#1119, plumbing layer 2)

With `--midval`, a bundle entry carries cg_clif's source function `f` (`.unopt.clif`) and the
function that is compiled, `g` (Cranelift's `.opt.clif` where the validator accepted it, else `f`
itself). `lean-link` and `link-check` re-decide every pair on the bundle's own texts:

* `midPairB f g`: `g` is `f`, or the certificate `Opt.MidVal.emit` computes for
  `(ConstPhi.run f, g)` passes the re-check `Opt.MidVal.checkCert` (without the hoisting mode:
  `emit`'s default `hoist := false`);
* `midValidatedB fs gs`: the lists have the same length and every pair passes `midPairB`;
* **`midValidatedB_sound`**: then `Opt.MidVal.Validated fs gs`, the premise of `Link.midProg`
  and of the `…Mid` / `…_mid` theorems.

`emit` is untrusted: only `checkCert`'s verdict on its output is used.
-/

namespace Link

/-- **The per-function decision** (module doc): `g` is `f`, or the certificate `emit` computes
for the pair passes the re-check `checkCert` against `f` after constant-phi removal. -/
def midPairB (f g : Clif.Function) : Bool :=
  decide (f = g) ||
    match Opt.MidVal.emit (Opt.ConstPhi.run f) g with
    | .ok c => Opt.MidVal.checkCert (Opt.ConstPhi.run f) g c
    | .error _ => false

/-- **The decision on two programs' function lists**: pointwise `midPairB`, equal lengths. -/
def midValidatedB : List Clif.Function → List Clif.Function → Bool
  | [], [] => true
  | f :: fs, g :: gs => midPairB f g && midValidatedB fs gs
  | _, _ => false

/-- What `midPairB` decides: the same function, or a certificate passing the re-check. -/
theorem midPairB_sound {f g : Clif.Function} (h : midPairB f g = true) :
    f = g ∨ ∃ cert, Opt.MidVal.checkCert (Opt.ConstPhi.run f) g cert = true := by
  unfold midPairB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact .inl (of_decide_eq_true h)
  · refine .inr ?_
    split at h
    · exact ⟨_, h⟩
    · cases h

/-- **Soundness of the decision**: `midValidatedB fs gs = true` gives `Opt.MidVal.Validated fs gs`. -/
theorem midValidatedB_sound : ∀ {fs gs : List Clif.Function},
    midValidatedB fs gs = true → Opt.MidVal.Validated fs gs
  | [], [], _ => .nil
  | f :: fs, g :: gs, h => by
    simp only [midValidatedB, Bool.and_eq_true] at h
    rcases midPairB_sound h.1 with rfl | ⟨cert, hc⟩
    · exact .same (midValidatedB_sound h.2)
    · exact .checked cert hc (midValidatedB_sound h.2)
  | [], _ :: _, h => by simp [midValidatedB] at h
  | _ :: _, [], h => by simp [midValidatedB] at h

end Link

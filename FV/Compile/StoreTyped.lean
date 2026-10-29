module

public import FV.Compile.SubsetT

public section

/-!
# Float stores store float values (S11e5 Stage C, slice 7)

`Compile.storeTypedB f`: the value a `store` of a float type stores is a float-defined value
(every definition of it in `defFloats f` is a float), the CLIF verifier's typing of `store`. The
integer `store` roots of the backend dispatch on the stored value's type, not on the store's, so
the typed statement dispatcher needs this fact (`Backend.Proof.StoreTyped`; soundness against
`buildCtx`'s value types: `Backend.Proof.storesTyped_of_buildCtx`).

`storeTypedB_sound` states it as a proposition; `storeTypedB_of_functionE`: every function of
subset E passes it (it has no float store).
-/

namespace Compile

open Clif

/-- **Float stores store float-defined values** (decided). -/
def storeTypedB (f : Function) : Bool :=
  let df := defFloats f
  f.blocks.all fun b => b.body.all fun s => match s.inst with
    | .store _ ty _ x _ _ => !ty.isFloat || argClassOk df x ty
    | _ => true

/-- **Soundness of `storeTypedB`.** -/
theorem storeTypedB_sound {f : Function} (h : storeTypedB f = true) :
    ∀ b ∈ f.blocks, ∀ s ∈ b.body, ∀ op ty fl x q off, s.inst = .store op ty fl x q off →
      ty.isFloat = true → argClassOk (defFloats f) x ty = true := by
  intro b hb s hs op ty fl x q off hi hf
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h b hb) s hs
  rw [hi] at h1
  simp only [hf, Bool.not_true, Bool.false_or] at h1
  exact h1

/-- **Subset E passes `storeTypedB`** (its stores are of integer types). -/
theorem storeTypedB_of_functionE {f : Function} (hE : functionE f = true) :
    storeTypedB f = true := by
  simp only [functionE, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨-, hb⟩ := hE
  refine List.all_eq_true.mpr fun b hbm => List.all_eq_true.mpr fun s hs => ?_
  have hi := (hb b hbm).1.2 s hs
  clear hb
  generalize s.inst = i at hi ⊢
  cases i with
  | store op ty fl x q off =>
    simp only [instE, Bool.and_eq_true] at hi
    simp only [isFloat_of_tyE hi.1, Bool.not_false, Bool.true_or]
  | _ => rfl

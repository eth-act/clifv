module

public import FV.Compile.SubsetT

@[expose] public section

/-!
# Float selects select float values (S11 slice 8)

`Compile.selectTypedB f`: the two selected values of a `select` of a float type are
float-defined values (every definition of each in `defFloats f` is a float), the CLIF verifier's
typing of `select` (`x`, `y` and the result have the controlling type). The typed movement scope
`functionET` types only the integer positions (`opsTypedT`: the condition of a float `select`), so
it admits `select.f64 c, x, y` with an integer `x`; the backend's float `select` root then puts
`x` into an int vreg and emits an `fcsel` of an int vreg, which no covered form describes
(`formsCoveredB` fails; witness `FVTest/E2E/FloatScopeT2.lean`).

`selectTypedB_sound` states it as a proposition; `selectTypedB_of_functionE`: every function of
subset E passes it (it has no float `select`).
-/

namespace Compile

open Clif

/-- **Float selects select float-defined values** (decided). -/
def selectTypedB (f : Function) : Bool :=
  let df := defFloats f
  f.blocks.all fun b => b.body.all fun s => match s.inst with
    | .select ty _ x y => !ty.isFloat || (argClassOk df x ty && argClassOk df y ty)
    | _ => true

/-- **Soundness of `selectTypedB`.** -/
theorem selectTypedB_sound {f : Function} (h : selectTypedB f = true) :
    ∀ b ∈ f.blocks, ∀ s ∈ b.body, ∀ ty c x y, s.inst = .select ty c x y → ty.isFloat = true →
      argClassOk (defFloats f) x ty = true ∧ argClassOk (defFloats f) y ty = true := by
  intro b hb s hs ty c x y hi hf
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h b hb) s hs
  rw [hi] at h1
  simp only [hf, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
  exact h1

/-- **Subset E passes `selectTypedB`** (its selects are of integer types). -/
theorem selectTypedB_of_functionE {f : Function} (hE : functionE f = true) :
    selectTypedB f = true := by
  simp only [functionE, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨-, hb⟩ := hE
  refine List.all_eq_true.mpr fun b hbm => List.all_eq_true.mpr fun s hs => ?_
  have hi := (hb b hbm).1.2 s hs
  clear hb
  generalize s.inst = i at hi ⊢
  cases i with
  | select ty c x y =>
    simp only [instE, Bool.and_eq_true] at hi
    simp only [isFloat_of_tyE hi, Bool.not_false, Bool.true_or]
  | _ => rfl

end Compile

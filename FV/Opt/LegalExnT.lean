import FV.Opt.LegalExn

/-!
# The handler edges of an `i128` legalisation, `try_call_indirect` included (#1076)

`exnOk` (`FV/Opt/LegalExn.lean`) checks the exception tables of the `try_call` terminators of a
legalisation; a function in its domain (`check`'s, `indOldB`) has no `try_call_indirect`. Rust's
`Box<dyn Any>::downcast` has one in an `i128` function (two `TypeId`s compared by `load.i128`, the
vtable's `type_id` called by a `try_call_indirect` with an `i128`-free signature).

`exnOkT f g cert`: `exnOk f g cert`, and for every `try_call_indirect` terminator of `f` and every
`try_call_indirect` terminator of `g` that `termOk` relates, the items agree one by one (`itemsOk`,
as for `try_call`). Decidable (a compiler-side check). `exnOkT_of_exnOk`: on a function without
`try_call_indirect` it is `exnOk`.
-/

namespace Opt.Legal

open Clif Opt.Legalize128

/-- The handler edges of a `try_call_indirect` of `f` and of one of `g` that `termOk` relates. -/
def termExnOkT (C : Ctx) : Terminator → Terminator → Bool
  | .tryCallIndirect c args et, .tryCallIndirect c' args' et' =>
    !termOk C (.tryCallIndirect c args et) [] (.tryCallIndirect c' args' et') ||
      itemsOk C et.items et'.items
  | _, _ => true

/-- **The handler-edge check, `try_call_indirect` included**, of a legalisation `g` of `f`
(certificate `cert`): `exnOk`, and the items of related `try_call_indirect` terminators. -/
def exnOkT (f g : Function) (cert : Cert) : Bool :=
  exnOk f g cert &&
    f.blocks.all fun b => g.blocks.all fun b' => termExnOkT ⟨f, g, cert⟩ b.term b'.term

/-! ### `exnOkT` as the compiler runs it (#1074)

`termExnOkT` evaluates `termOk` for every pair of `try_call_indirect` terminators, which recomputes
`C.T0` (`maxValueId`) and the two `freshValue`s (passes over the whole function): the cost
`exnOk` had (`exnOk_eq_F`). `exnOkTF` computes the three once per function, for both loops
(`termOkF`); `exnOkT_eq_F` (`@[csimp]`) proves it equal. -/

/-- `termExnOkT` with `C.T0`, `C.f.freshValue` and `C.g.freshValue` given (`t0`, `ff`, `gf`). -/
def termExnOkTF (C : Ctx) (t0 ff gf : Nat) : Terminator → Terminator → Bool
  | .tryCallIndirect c args et, .tryCallIndirect c' args' et' =>
    !termOkF C t0 ff gf (.tryCallIndirect c args et) [] (.tryCallIndirect c' args' et') ||
      itemsOk C et.items et'.items
  | _, _ => true

theorem termExnOkT_eq_F (C : Ctx) (t t' : Terminator) :
    termExnOkT C t t' = termExnOkTF C C.T0 C.f.freshValue C.g.freshValue t t' := by
  cases t <;> cases t' <;> rfl

/-- `exnOkT` as the compiler runs it (`exnOkT_eq_F`, `@[csimp]`): `T0` and the two `freshValue`s
once per function. -/
def exnOkTF (f g : Function) (cert : Cert) : Bool :=
  let C : Ctx := ⟨f, g, cert⟩
  let t0 := C.T0
  let ff := f.freshValue
  let gf := g.freshValue
  ((f.blocks.all fun b => g.blocks.all fun b' => termExnOkF C t0 ff gf b.term b'.term) &&
    g.blocks.all fun b' => !isReturnCall b'.term) &&
  f.blocks.all fun b => g.blocks.all fun b' => termExnOkTF C t0 ff gf b.term b'.term

@[csimp] theorem exnOkT_eq_F : @exnOkT = @exnOkTF := by
  funext f g cert
  simp only [exnOkT, exnOkTF, exnOk, termExnOk_eq_F, termExnOkT_eq_F]

/-! ## Spec -/

theorem exnOkT_exnOk {f g : Function} {cert : Cert} (h : exnOkT f g cert = true) :
    exnOk f g cert = true := by
  simp only [exnOkT, Bool.and_eq_true] at h
  exact h.1

theorem exnOkT_itemsInd {f g : Function} {cert : Cert} (h : exnOkT f g cert = true) {B B' : Block}
    (hB : B ∈ f.blocks) (hB' : B' ∈ g.blocks) {c c' : ValueId} {args args' : List ValueId}
    {et et' : ExnTable} (ht : B.term = .tryCallIndirect c args et)
    (ht' : B'.term = .tryCallIndirect c' args' et')
    (hok : termOk ⟨f, g, cert⟩ (.tryCallIndirect c args et) [] (.tryCallIndirect c' args' et') = true) :
    itemsOk ⟨f, g, cert⟩ et.items et'.items = true := by
  simp only [exnOkT, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 B hB B' hB'
  rw [ht, ht'] at this
  simpa [termExnOkT, hok] using this

/-- Without `try_call_indirect` in `f`, `exnOkT` is `exnOk`. -/
theorem exnOkT_of_exnOk {f g : Function} {cert : Cert} (h : exnOk f g cert = true)
    (hn : ∀ B ∈ f.blocks, ∀ c args et, B.term ≠ .tryCallIndirect c args et) :
    exnOkT f g cert = true := by
  simp only [exnOkT, h, Bool.true_and, List.all_eq_true]
  intro B hB B' _
  cases ht : B.term with
  | tryCallIndirect c args et => exact absurd ht (hn B hB c args et)
  | _ => rfl

end Opt.Legal

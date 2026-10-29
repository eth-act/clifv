module

public import FV.Clif.Run

public section

/-! # Facts about `Clif.evalFloat` shared by the mid-end and backend proofs -/

namespace Clif

private theorem bind_eq_ok {α β : Type} {x : Res α} {f : α → Res β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Res.bind]

private theorem ofOption_eq_ok {α : Type} {m : String} {o : Option α} {a : α} :
    Res.ofOption m o = .ok a ↔ o = some a := by
  cases o <;> simp [Res.ofOption]

/-- The result type of `Inst.float op ty` (`Inst.resultTypes`): `i8` for `fcmp`, the
controlling type otherwise. -/
@[expose] def floatResTy : FOp → Ty → Ty
  | .fcmp _, _ => .i8
  | _, ty => ty

/-- `Inst.resultTypes` of a float operation is `[floatResTy op ty]`. -/
theorem resultTypes_float {op : FOp} {ty : Ty} {args : List ValueId}
    {sigOf : FnRef → Option Signature} {sigDeclOf : Nat → Option Signature} :
    (Inst.float op ty args).resultTypes sigOf sigDeclOf = some [floatResTy op ty] := by
  cases op <;> rfl

/-- A float operation's result has the type `floatResTy`. -/
theorem evalFloat_ty {op : FOp} {ty : Ty} {vs : List Val} {r : Val}
    (h : evalFloat op ty vs = .ok r) : r.ty = floatResTy op ty := by
  unfold evalFloat at h
  split at h
  all_goals (repeat' (first
    | (simp only [bind_eq_ok, Res.pure_eq, Res.ok.injEq, ofOption_eq_ok] at h)
    | (obtain ⟨_, _, h⟩ : ∃ _, _ ∧ _ := h)
    | (cases hu : FSem.unary op <;> simp only [hu] at h)
    | (cases hu : FSem.binary op <;> simp only [hu] at h)
    | (split at h)))
  all_goals first
    | (cases h; done)
    | (subst h; simp_all [floatResTy, Val.ofBool]; done)
    | (subst h; cases op <;> simp_all [floatResTy, FSem.unary, FSem.binary]; done)
    | (cases op <;> simp_all [floatResTy, FSem.unary, FSem.binary]; done)

end Clif

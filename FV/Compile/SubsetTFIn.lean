import FV.Compile.SubsetTF

/-!
# The float scope of the decider-free input chain (S11f, #35)

`Compile.functionETF f`: the typed movement scope `functionET` with the S11f float operations of
`instETF` (arithmetic, rounding, the `from` and saturating conversions, scalar `fcmp`), their
integer positions `intOperandsF` (`opsTypedTF`: the operand of an `fcvt_from_*` is not
float-defined) and their float positions `floatOperands` (`floatOpsTyped`: the operands of an
`fcmp` and of a saturating conversion are float-defined; their `lower` roots match on the operand
type). Without typed `try_call`s (externs keep `sigE`). The scope of `Backend.Proof.Driver.LowerScopeTF`
and of the float input chain (`FV/E2E/LinkScopeInputT3F.lean`). `functionETF_of_functionET`: it
widens the typed movement scope. Kept apart from `SubsetTF` (which the compiler imports).
-/

namespace Compile

open Clif

/-- The operands the CLIF verifier types as floats that the lowering of the float operations needs
typed (their `lower` roots match on the operand type): the operands of an `fcmp` and of a
saturating `fcvt_to_{u,s}int_sat`. -/
def floatOperands : Inst → List Nat
  | .float (.fcmp _) _ [x, y] => [x, y]
  | .float .fcvtToUintSat _ [x] | .float .fcvtToSintSat _ [x] => [x]
  | _ => []

/-- The float-position operands are float-defined values: every definition of each is a float
(`argClassOk` at `f32`). -/
def floatOpsTyped (f : Function) : Bool :=
  let df := defFloats f
  f.blocks.all fun b => b.body.all fun s => (floatOperands s.inst).all fun x => argClassOk df x .f32

/-- `opsTypedT` with `intOperandsF` (the operand of an `fcvt_from_*` is an integer position). -/
def opsTypedTF (f : Function) : Bool :=
  let fd := floatDefs f
  f.blocks.all fun b =>
    b.body.all (fun s => (intOperandsF s.inst).all fun x => !fd.contains x) &&
      (termIntOperands b.term).all fun x => !fd.contains x

/-- **The typed scope with the proven float operations, without typed `try_call`s**
(S11f, #35): `functionET` with `instETF` for `instET`, the integer positions of `intOperandsF`
(`opsTypedTF`) and the float positions of `floatOperands` (`floatOpsTyped`). The scope of the
decider-free input chain over floats (`E2E.LinkCheck.lowerScopeTFB`). -/
def functionETF (f : Function) : Bool :=
  sigET f.sig && f.globals.all (globalE ·.2) && f.externs.all (sigE ·.2.sig) &&
    f.blocks.all (fun b =>
      b.params.all (tyM ·.2) && b.body.all (instETF ·.inst) && termE b.term) &&
    opsTypedTF f && edgeClassOk f && floatOpsTyped f

/-- `floatOperands` of an instruction of the typed movement scope are none. -/
theorem floatOperands_eq_nil {i : Inst} (h : instET i = true) : floatOperands i = [] := by
  cases i with
  | float op ty args => simp [instET, instE] at h
  | _ => rfl

/-- **The typed movement scope is in the float scope.** -/
theorem functionETF_of_functionET {f : Function} (h : functionET f = true) :
    functionETF f = true := by
  simp only [functionET, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hs, hg⟩, hx⟩, hb⟩, ho⟩, he⟩ := h
  simp only [functionETF, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hs, hg⟩, hx⟩, fun b hb' => ?_⟩, ?_⟩, he⟩, ?_⟩
  · obtain ⟨⟨hp, hi⟩, ht⟩ := hb b hb'
    exact ⟨⟨hp, fun s hs' => instETF_of_instET (hi s hs')⟩, ht⟩
  · simp only [opsTypedT, opsTypedTF, Bool.and_eq_true, List.all_eq_true] at ho ⊢
    intro b hb'
    refine ⟨fun s hs' => ?_, (ho b hb').2⟩
    rw [intOperandsF_eq ((hb b hb').1.2 s hs')]
    exact (ho b hb').1 s hs'
  · simp only [floatOpsTyped, List.all_eq_true]
    intro b hb' s hs' x hx
    rw [floatOperands_eq_nil ((hb b hb').1.2 s hs')] at hx
    cases hx

end Compile

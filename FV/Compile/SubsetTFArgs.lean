import FV.Compile.SubsetTFIn

/-!
# The float operands of the float scope are float-defined (S11f, #35)

`Compile.floatArgsTyped f`: every operand the CLIF verifier types as a float of a float
operation of `Compile.instETF` (`floatArgs`: the operands of the arithmetic and rounding, of an
`fcmp`, of a saturating `fcvt_to_*_sat`) is float-defined (`argClassOk` at `f32`). The
coverage, shape, size and emission analyses of the checks need it: `fadd` of an integer-defined
value would lower to an `fpu_rrr` reading an integer vreg, a form `formsCoveredB` rejects.
`floatOpsTyped` (the positions `lower_ok` needs) is the special case `floatOperands`;
`floatArgsTyped_floatOpsTyped`.
-/

namespace Compile

open Clif

/-- The float positions of a float operation of the float scope: the operands of the arithmetic
and rounding (`fBinaryOpcode`, `fUnaryOpcode`), of an `fcmp` and of a saturating conversion
(`floatOperands`). -/
def floatArgs : Inst → List Nat
  | .float op ty args =>
    if (Backend.fBinaryOpcode op).isSome || (Backend.fUnaryOpcode op).isSome then args
    else floatOperands (.float op ty args)
  | _ => []

/-- **The float positions are float-defined.** -/
def floatArgsTyped (f : Function) : Bool :=
  let df := defFloats f
  f.blocks.all fun b => b.body.all fun s => (floatArgs s.inst).all fun x => argClassOk df x .f32

/-- `floatOperands` positions are `floatArgs` positions. -/
theorem floatOperands_sub_floatArgs {i : Inst} {x : Nat} (h : x ∈ floatOperands i) :
    x ∈ floatArgs i := by
  cases i with
  | float op ty args =>
    show x ∈ (if ((Backend.fBinaryOpcode op).isSome || (Backend.fUnaryOpcode op).isSome) = true
      then args else floatOperands (.float op ty args))
    split
    · unfold floatOperands at h; split at h <;> simp_all
    · exact h
  | _ => simp [floatOperands] at h

theorem floatArgsTyped_floatOpsTyped {f : Function} (h : floatArgsTyped f = true) :
    floatOpsTyped f = true := by
  simp only [floatArgsTyped, floatOpsTyped, List.all_eq_true] at h ⊢
  exact fun b hb s hs x hx => h b hb s hs x (floatOperands_sub_floatArgs hx)

end Compile

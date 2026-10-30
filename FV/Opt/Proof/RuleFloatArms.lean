import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr

/-!
# `all_zero` at a float type

`all_zero ty` has `$F16`/`$F32`/`$F64`/`$F128` arms besides `ty_int`. Matching a presented type
`CTy.ofClif t` against them is `t.isFloat && b == t.width` (`CTy.ofClif_beq_float`); these
`opt_monad` facts evaluate it at an integer type (concrete, or a variable with an `isInt`
hypothesis from `opt_split_int`) and at a float variable. The `$F32`/`$F64` arms call
`f32_from_uint`/`f64_from_uint`, which the interpreter does not model: the evaluation aborts.
-/

namespace Opt.Proof

open Isle Isle.Opt Clif

@[opt_monad] theorem ty_isFloat_of_isInt {t : Ty} (h : t.isInt = true) : t.isFloat = false := by
  cases t <;> simp_all

@[opt_monad] theorem ty_isFloat_of_not_isInt {t : Ty} (h : ¬t.isInt = true) :
    t.isFloat = true := by
  cases t <;> simp_all

@[opt_monad] theorem ty_width_ne_16_of_not_isInt {t : Ty} (h : ¬t.isInt = true) :
    (16 == t.width) = false := by
  cases t <;> simp_all [Ty.width]

@[opt_monad] theorem ty_width_ne_128_of_not_isInt {t : Ty} (h : ¬t.isInt = true) :
    (128 == t.width) = false := by
  cases t <;> simp_all [Ty.width]

@[opt_monad] theorem ty_isFloat_ints : Ty.i8.isFloat = false ∧ Ty.i16.isFloat = false ∧
    Ty.i32.isFloat = false ∧ Ty.i64.isFloat = false ∧ Ty.i128.isFloat = false := by decide

attribute [opt_monad] Bool.false_and Bool.true_and

section
variable {σ : Type} (G : EGraph σ)

@[opt_monad] theorem ctorFn_f32_from_uint_zero (s : St σ) :
    ctorFn G "f32_from_uint" [.int 0] s = .error "unmodeled extern constructor f32_from_uint" :=
  rfl

@[opt_monad] theorem ctorFn_f64_from_uint_zero (s : St σ) :
    ctorFn G "f64_from_uint" [.int 0] s = .error "unmodeled extern constructor f64_from_uint" :=
  rfl

end

end Opt.Proof

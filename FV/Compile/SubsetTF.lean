import FV.Compile.SubsetTC

/-!
# The typed scope with the proven float operations (S11f, #35)

`Compile.functionETCF f`: the scope with typed direct `try_call`s (`functionETC`) whose
statements may also be the S11f float operations whose `lower` roots are proven over float-capable
contexts: the arithmetic and rounding of `fArithET` (`fadd`/`fsub`/`fmul`/`fdiv`/`fmin`/`fmax`,
`sqrt`/`fneg`/`fabs`/`fpromote`/`fdemote`, `ceil`/`floor`/`trunc`/`nearest`), the conversions
of `fCvtET` (`fcvt_from_{u,s}int` to `f32`/`f64`, the saturating `fcvt_to_{u,s}int_sat` to
`i32`/`i64`; `Backend.fCvtOpcode`/`Backend.fCvtTyOk`, the types `instData` admits) and the scalar
comparisons of `fCmpET` (`fcmp` of two `f32`/`f64` operands with an `i8` result, at the
conditions `Backend.fccOk` that `instData` admits: not `one`/`ueq`). The trapping
`fcvt_to_{u,s}int` stay outside (cg_clif never emits them). The operand of an `fcvt_from_*` is an
integer position (`intOperandsF`); the operands of an `fcmp` are float positions.

`functionETC`, `functionET` and their theorems are unchanged; `functionETCF_of_functionETC`:
every function of the scope with typed `try_call`s is in this one.
-/

namespace Compile

open Clif

/-- The S11f-cvt conversions whose `lower` roots are proven (`Backend.Proof.IselFloatCvt`):
one operand, an opcode of `Backend.fCvtOpcode`, at a type of `Backend.fCvtTyOk`. -/
def fCvtET : Inst → Bool
  | .float op ty [_] => (Backend.fCvtOpcode op).isSome && Backend.fCvtTyOk op ty
  | _ => false

/-- The S11f scalar comparisons whose `lower` root is proven (`rule_lower_2176`,
`Backend.Proof.IselFloatCmp`): `fcmp` of two operands at `f32`/`f64` (the operands' type; the
result is an `i8`), at a condition of `Backend.fccOk` (the conditions `instData` admits). -/
def fCmpET : Inst → Bool
  | .float (.fcmp cc) ty [_, _] => ty.isFloat && Backend.fccOk cc
  | _ => false

/-- **The instructions of the typed scope with the proven float operations**: `instET`, the
arithmetic and rounding (`fArithET`), the conversions (`fCvtET`) and the scalar comparisons
(`fCmpET`). -/
def instETF (i : Inst) : Bool := instETA i || fCvtET i || fCmpET i

theorem instETF_of_instETA {i : Inst} (h : instETA i = true) : instETF i = true := by
  simp [instETF, h]

theorem instETF_of_instET {i : Inst} (h : instET i = true) : instETF i = true :=
  instETF_of_instETA (instETA_of_instET h)

/-- The operands in integer positions with the conversions: an `fcvt_from_*`'s operand is an
integer (the CLIF verifier's typing). -/
def intOperandsF : Inst → List Nat
  | .float .fcvtFromUint _ [x] | .float .fcvtFromSint _ [x] => [x]
  | i => intOperands i

/-- `intOperandsF` is `intOperands` on the typed movement scope. -/
theorem intOperandsF_eq {i : Inst} (h : instET i = true) : intOperandsF i = intOperands i := by
  cases i with
  | float op ty args => simp [instET, instE] at h
  | _ => rfl

/-- `opsTypedTC` with `intOperandsF`. -/
def opsTypedTCF (f : Function) : Bool :=
  let fd := floatDefs f
  f.blocks.all fun b =>
    b.body.all (fun s => (intOperandsF s.inst).all fun x => !fd.contains x) &&
      (termIntOperandsC b.term).all fun x => !fd.contains x

/-- **The typed scope with the proven float operations** (`functionETC` with `instETF`). -/
def functionETCF (f : Function) : Bool :=
  sigET f.sig && f.globals.all (globalE ·.2) && f.externs.all (sigET ·.2.sig) && callsE f &&
    f.blocks.all (fun b =>
      b.params.all (tyM ·.2) && b.body.all (instETF ·.inst) && termE b.term) &&
    opsTypedTCF f && edgeClassOk f

/-- **The scope with typed `try_call`s is in the scope with the float operations.** -/
theorem functionETCF_of_functionETC {f : Function} (h : functionETC f = true) :
    functionETCF f = true := by
  simp only [functionETC, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, hg⟩, hx⟩, hc⟩, hb⟩, ho⟩, he⟩ := h
  simp only [functionETCF, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hs, hg⟩, hx⟩, hc⟩, fun b hb' => ?_⟩, ?_⟩, he⟩
  · obtain ⟨⟨hp, hi⟩, ht⟩ := hb b hb'
    exact ⟨⟨hp, fun s hs' => instETF_of_instET (hi s hs')⟩, ht⟩
  · simp only [opsTypedTC, opsTypedTCF, Bool.and_eq_true, List.all_eq_true] at ho ⊢
    intro b hb'
    refine ⟨fun s hs' => ?_, (ho b hb').2⟩
    rw [intOperandsF_eq ((hb b hb').1.2 s hs')]
    exact (ho b hb').1 s hs'

/-! ## The float scope of the decider-free input chain -/

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
decider-free input chain over floats (`E2E.LinkCheck.fnScopeInTB3F`). -/
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

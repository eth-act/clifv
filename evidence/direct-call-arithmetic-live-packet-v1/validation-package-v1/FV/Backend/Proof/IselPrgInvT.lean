import FV.Backend.Proof.IselContract
import FV.Backend.Proof.IselPrgDom
import FV.Backend.Proof.DriverCheck
import FV.Compile.SubsetTFIn

/-!
# Progress of the ISLE lowering over the typed scope: the context invariant

`PInvT f ctx`: `PInv` (`IselPrgInv`) for a float-capable lowering context (`CtxInvT` for
`CtxInv`): the context's instructions are `f`'s and in the typed scope (`Compile.instET`), the
operands in integer positions (`intArgs`) of `f`'s statements are integers, operands and results
have types, stack slots exist, callees are declared with signatures the lowering handles, and
every `uextend`/`sextend` widens a narrower than 64-bit value. `IselPrgCtxT` proves it for the
context `buildCtx f` builds (and its terminator/`try_call` variants) from the input conditions.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

/-- **The context invariant of the progress analysis over the typed scope.** -/
structure PInvT (f : Clif.Function) (ctx : Ctx) : Prop where
  ctxInv : CtxInvT f ctx
  /-- The context's CLIF instructions are statements of `f`. -/
  clifOf : ∀ (j : Nat) (info : IInfo) (c : Clif.Inst), ctx.insts[j]? = some info → info.clif = some c → InstOf f c
  /-- The callees of `f` have integer signatures (`Compile.functionET`). -/
  externsE : f.externs.all (Compile.sigE ·.2.sig) = true
  /-- `f`'s statements are in the typed scope. -/
  instET : ∀ (c : Clif.Inst), InstOf f c → Compile.instET c = true
  /-- The operands in integer positions of `f`'s statements are integers. -/
  intArgsOf : ∀ (c : Clif.Inst), InstOf f c → ∀ x ∈ intArgs c, IntPos ctx x
  /-- Every operand of a statement of `f` has a type. -/
  argsTyped : ∀ (c : Clif.Inst), InstOf f c → ∀ x ∈ Driver.instArgs c, (ctx.valueType? x).isSome
  /-- Every result of an instruction of the context has a type. -/
  resTyped : ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info → ∀ r ∈ info.results, (ctx.valueType? r).isSome
  /-- An entry without CLIF instruction (a terminator's slot) has no result types. -/
  noClifRes : ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info → info.clif = none → info.resTys = []
  /-- The result types of an E instruction are E's integers (calls have integer signatures). -/
  resE : ∀ (j : Nat) (info : IInfo) (c : Clif.Inst), ctx.insts[j]? = some info → info.clif = some c →
    Compile.instE c = true → ∀ t ∈ info.resTys, t ∈ eCTys
  /-- The operands of `f`'s terminators in integer positions (a branch condition, a `br_table`
  index, a `try_call`'s callee and arguments) are integers. -/
  termIntOf : ∀ B ∈ f.blocks, ∀ x ∈ Compile.termIntOperands B.term, IntPos ctx x
  /-- Every `stack_addr` names a stack slot of the frame. -/
  slots : ∀ ty s off, InstOf f (.stackAddr ty s off) → (ctx.slotOff.lookup s).isSome
  /-- Every `call`/`func_addr` names a declared callee whose signature the lowering handles. -/
  callees : ∀ (c : Clif.Inst) (fn : Nat), InstOf f c → ((∃ args, c = .call fn args) ∨ (∃ ty, c = .funcAddr ty fn)) →
    ∃ ext, f.extern? fn = some ext ∧ SigOk ext.sig
  /-- Every `call_indirect`'s declared signature is handled. -/
  indSigs : ∀ sig callee args s, InstOf f (.callIndirect sig callee args) →
    f.sigDecls.lookup sig = some s → SigOk s
  /-- Every `uextend`/`sextend` extends an 8-, 16- or 32-bit value. -/
  extNarrow : ∀ op ty x, InstOf f (.extend op ty x) →
    ∃ b, ctx.valueType? x = some (.int b) ∧ (b = 8 ∨ b = 16 ∨ b = 32)

/-- **`PInvT` without the instruction scope** (S11f, #35): every field of `PInvT` except
`instET`. The progress facts that hold for any instruction scope take it (`…B` theorems); `PInvT`
(`PInvT.toB`) and the float scope's `PInvTF` (`IselPrgInvTF`) give it. -/
structure PInvTB (f : Clif.Function) (ctx : Ctx) : Prop where
  ctxInv : CtxInvT f ctx
  clifOf : ∀ (j : Nat) (info : IInfo) (c : Clif.Inst), ctx.insts[j]? = some info → info.clif = some c → InstOf f c
  externsE : f.externs.all (Compile.sigE ·.2.sig) = true
  intArgsOf : ∀ (c : Clif.Inst), InstOf f c → ∀ x ∈ intArgs c, IntPos ctx x
  argsTyped : ∀ (c : Clif.Inst), InstOf f c → ∀ x ∈ Driver.instArgs c, (ctx.valueType? x).isSome
  resTyped : ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info → ∀ r ∈ info.results, (ctx.valueType? r).isSome
  noClifRes : ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info → info.clif = none → info.resTys = []
  resE : ∀ (j : Nat) (info : IInfo) (c : Clif.Inst), ctx.insts[j]? = some info → info.clif = some c →
    Compile.instE c = true → ∀ t ∈ info.resTys, t ∈ eCTys
  termIntOf : ∀ B ∈ f.blocks, ∀ x ∈ Compile.termIntOperands B.term, IntPos ctx x
  slots : ∀ ty s off, InstOf f (.stackAddr ty s off) → (ctx.slotOff.lookup s).isSome
  callees : ∀ (c : Clif.Inst) (fn : Nat), InstOf f c → ((∃ args, c = .call fn args) ∨ (∃ ty, c = .funcAddr ty fn)) →
    ∃ ext, f.extern? fn = some ext ∧ SigOk ext.sig
  indSigs : ∀ sig callee args s, InstOf f (.callIndirect sig callee args) →
    f.sigDecls.lookup sig = some s → SigOk s
  extNarrow : ∀ op ty x, InstOf f (.extend op ty x) →
    ∃ b, ctx.valueType? x = some (.int b) ∧ (b = 8 ∨ b = 16 ∨ b = 32)

/-- `PInvT` without its instruction scope. -/
theorem PInvT.toB {f : Clif.Function} {ctx : Ctx} (h : PInvT f ctx) : PInvTB f ctx :=
  ⟨h.ctxInv, h.clifOf, h.externsE, h.intArgsOf, h.argsTyped, h.resTyped, h.noClifRes, h.resE,
    h.termIntOf, h.slots, h.callees, h.indSigs, h.extNarrow⟩

/-- A value in a float position: of type `f32` or `f64` (if any). -/
def FloatPos (ctx : Ctx) (x : Nat) : Prop := ∀ t, ctx.valueType? x = some t → t = .float 32 ∨ t = .float 64

/-- **The context invariant of the progress analysis over the float scope** (S11f, #35):
`PInvTB`, `f`'s statements are in the float scope (`Compile.instETF`), the operands of `f`'s
statements in the integer positions of the conversions (`Compile.intOperandsF`) are integers, and
those in float positions (`Compile.floatOperands`: of an `fcmp` and of a saturating conversion) are
floats. -/
structure PInvTF (f : Clif.Function) (ctx : Ctx) : Prop extends PInvTB f ctx where
  instETF : ∀ (c : Clif.Inst), InstOf f c → Compile.instETF c = true
  intOpsFOf : ∀ (c : Clif.Inst), InstOf f c → ∀ x ∈ Compile.intOperandsF c, IntPos ctx x
  floatOpsOf : ∀ (c : Clif.Inst), InstOf f c → ∀ x ∈ Compile.floatOperands c, FloatPos ctx x

/-- An `iconst` of the float scope is one of the typed movement scope. -/
theorem instET_of_iconstF {ty : Clif.Ty} {imm : BitVec ty.width}
    (h : Compile.instETF (.iconst ty imm) = true) : Compile.instET (.iconst ty imm) = true := by
  simpa [Compile.instETF, Compile.instETA, Compile.fArithET, Compile.fCvtET, Compile.fCmpET] using h

end Backend.Proof.Prg

import FV.Backend.Proof.IselPrgRootT
import FV.Backend.Proof.IselPrgInv

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

end Backend.Proof.Prg

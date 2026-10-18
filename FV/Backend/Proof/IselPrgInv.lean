import FV.Backend.Proof.IselPrgRoot
import FV.Backend.Proof.DriverCheck

/-!
# Progress of the ISLE lowering (V7): the context invariant

`PInv f ctx`: what the extern helpers' transfer functions (`IselPrgExt`) rely on about the
lowering context `ctx` of `f`, beyond `CtxInv`: the context's instructions are `f`'s, their
operands and results have types, stack slots exist, callees are declared with signatures the
lowering handles (`SigOk`), and every `uextend`/`sextend` widens a narrower than 64-bit value.
`IselPrgCtx` proves it for the context `buildCtx f` builds (and its terminator/`try_call`
variants) from the input conditions.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

/-- **The context invariant of the progress analysis.** -/
structure PInv (f : Clif.Function) (ctx : Ctx) : Prop where
  ctxInv : CtxInv f ctx
  /-- The context's CLIF instructions are statements of `f`. -/
  clifOf : ∀ (j : Nat) (info : IInfo) (c : Clif.Inst), ctx.insts[j]? = some info → info.clif = some c → InstOf f c
  /-- Every operand of a statement of `f` has a type. -/
  argsTyped : ∀ (c : Clif.Inst), InstOf f c → ∀ x ∈ Driver.instArgs c, (ctx.valueType? x).isSome
  /-- Every result of an instruction of the context has a type. -/
  resTyped : ∀ (j : Nat) (info : IInfo), ctx.insts[j]? = some info → ∀ r ∈ info.results, (ctx.valueType? r).isSome
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

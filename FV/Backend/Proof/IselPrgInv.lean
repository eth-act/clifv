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

/-- `CtxInv` without its identity register mapping: every typed value has some integer
virtual register. The progress analysis needs no more, so it also covers contexts that
renumber value registers (the Stock driver's). -/
structure CtxInvW (f : Clif.Function) (ctx : Ctx) : Prop where
  func : ctx.func = f
  data : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    instData f inst = .ok info.data
  instE : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instE inst = true
  resTys : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    ∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
      info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length
  typedSome : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t → ∃ n, ctx.valueReg? x = some (.vreg n .int)
  defInst : ∀ (x d : Nat), ctx.defInst? x = some d → ∃ info, ctx.insts[d]? = some info ∧ x ∈ info.results
  defClif : ∀ (x d : Nat) (info : IInfo), ctx.defInst? x = some d → ctx.insts[d]? = some info →
    info.clif.isSome = true
  slotOff : ctx.slotOff = (slotLayout f.slots).1
  resTysE : ∀ (ii : Nat) (info : IInfo), ctx.insts[ii]? = some info → ∀ t ∈ info.resTys, t ∈ eCTys
  valTyE : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t → t ∈ eCTys
  addr64 : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst) (x : Nat), ctx.insts[ii]? = some info →
    info.clif = some inst → memAddr? inst = some x → ctx.valueType? x = some (.int 64)

theorem _root_.Backend.Proof.CtxInv.weak {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx) : CtxInvW f ctx :=
  { h with typedSome := fun x t ht => ⟨x,h.typedReg x t ht⟩ }

/-- A defining instruction of the context is a CLIF instruction with its `InstructionData`. -/
theorem CtxInvW.clif {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvW f ctx) {y j : Nat}
    {info : IInfo} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) :
    ∃ cl, info.clif = some cl ∧ instData f cl = .ok info.data := by
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp (hctx.defClif y j info hj hi)
  exact ⟨cl, hcl, hctx.data j info cl hi hcl⟩

/-- **The context invariant of the progress analysis.** -/
structure PInv (f : Clif.Function) (ctx : Ctx) : Prop where
  ctxInv : CtxInvW f ctx
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

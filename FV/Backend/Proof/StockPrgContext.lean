import FV.Backend.Proof.IselPrgDriver
import FV.Backend.Proof.StockDFG

/-!
# Progress of the baseline instruction selector on the Stock context

The progress analysis (`Prg.PInv`, `Prg.stmtProg`) needs only a context whose typed values have
integer virtual registers (`CtxInvW`). The Stock context renumbers value registers but keeps the
original instructions, value types and slot offsets (`DFGViewEq`), so the baseline invariant of the
original context transfers to it. Then every statement of the Stock context has a baseline
`lower` run that returns its result registers (`StmtProg`).
-/

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Prg
set_option autoImplicit false

theorem MappedCtxInv.weak {f : Clif.Function} {ctx : Ctx} (h : MappedCtxInv f ctx) : CtxInvW f ctx :=
  { h with typedSome := h.typedReg }

/-- The progress invariant of the Stock context, from the original input conditions. -/
theorem stock_pinv {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx,ranges,st)) (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (hw : extendsWidenB f = true) (hin : iselInB f = true) : PInv f ctx := by
  obtain ⟨original,st0,hold,-,view⟩ := buildCtx_source hb
  have hP := pinv_build hdom hs hw hin hold
  have mapped := buildCtx_mappedInv (lowerScope_of hs) hb
  refine pinv_of_insts hP mapped.weak view.valTy view.slotOff fun j info h => .inl ?_
  rw [← view.insts]
  exact h

/-- The progress invariant of a Stock terminator/statement context (`termCtx` with any `try_call`
registers): the placeholder holds the terminator data, other instructions are unchanged. -/
theorem stock_pinv_termCtx {f : Clif.Function} {ctx : Ctx} (hP : PInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) (regs : List Reg × List Reg) :
    PInv f { termCtx ctx ti data with tryRegs := regs } := by
  have hT := pinv_termCtx hP hph data
  exact pinv_of_insts hT { hT.ctxInv with } rfl rfl fun _ _ h => .inl h

/-- Every statement of the Stock context has a baseline `lower` run that returns its result
registers, for every baseline state. -/
theorem stock_stmtProg {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx,ranges,st)) (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (hw : extendsWidenB f = true) (hin : iselInB f = true) : StmtProg ctx :=
  stmtProg (stock_pinv hb hdom hs hw hin)
end Backend.Stock.Proof

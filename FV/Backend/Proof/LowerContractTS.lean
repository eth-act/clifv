import FV.Backend.Proof.LowerContractTP
import FV.Backend.Proof.LowerContractTF
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.ShapeS
import FV.Backend.Proof.ScopeTransport

/-!
# The typed rule contexts and families over an abstract scope (#1002 part 2)

`CtxTW f ctx` (S11g) is `CtxInvT f ctx` and the instructions of `ctx` in `InstScopeTF`. Its
scope-generic form `CtxTS S f ctx` has the instructions in `S.P` (`S : InstScope`, `ShapeS.lean`);
`CtxTW` is `CtxTS InstScope.tf` (`CtxTW.toS`). The typed rule families over `CtxTW` have forms over
`CtxTS S` for every `S` (`…S`, declared by `scopeS_transport_defs`, `ScopeTransport.lean`):
`LowerRuleOkTXS`, `LowerRuleOkTIS`, `LowerRulesCorrectTIS`, `MemRuleOkRTXS`, `MemRulesCorrectRTIS`,
`IndRuleOkTS`, `IndRulesCorrectTS`, `LowerTermRuleOkTS`, `LowerTermRulesCorrectTS`,
`TermUnmatchableTS`, `BranchRuleOkTS`, `BranchRulesCorrectTS`, `BranchExcludedUnmatchableTS`,
`TryIndRuleOkTS`, `TryIndRulesCorrectTS`, `TryIndUnmatchableTS`, `IndRuleOkTPS`,
`IndRulesCorrectTPS`, `TryIndRuleOkTPS`, `TryIndRulesCorrectTPS`, `NonEUnmatchableTFS`: each is
the `…W` definition with `CtxTS S` in place of `CtxTW`. `CtxTW`, the `…W` families and their
theorems are unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64 Backend.Proof.Driver

/-- **The context premise of the typed rule families over the scope `S`** (#1002 part 2): a
float-capable lowering context whose instructions are in `S.P`. -/
structure CtxTS (S : InstScope) (f : Clif.Function) (ctx : Ctx) : Prop where
  inv : CtxInvT f ctx
  scope : S.P ctx

/-- `CtxTS` from `CtxTS` (the image of `CtxTW.self` under the scope-generic transport). -/
theorem CtxTS.self (S : InstScope) {f : Clif.Function} {ctx : Ctx} (h : CtxTS S f ctx) :
    CtxTS S f ctx := h

/-- `CtxTW` is `CtxTS` at the scope with the proven float operations. -/
theorem CtxTW.toS {f : Clif.Function} {ctx : Ctx} (h : CtxTW f ctx) : CtxTS InstScope.tf f ctx :=
  ⟨h.inv, h.scope⟩

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- Filling in the terminator's data at `buildCtx`'s placeholder keeps `CtxTS S`. -/
theorem ctxTS_termCtx (S : InstScope) {f : Clif.Function} {ctx : Ctx} (h : CtxTS S f ctx)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    CtxTS S f (termCtx ctx ti data) :=
  ⟨ctxInvT_termCtx h.inv hph data, S.termCtxOk ctx ti data hph h.scope⟩

/-- `CtxTS S` does not depend on the `try_call` vregs. -/
theorem ctxTS_tryRegs (S : InstScope) {f : Clif.Function} {ctx : Ctx} (h : CtxTS S f ctx)
    (trs : List Reg × List Reg) : CtxTS S f { ctx with tryRegs := trs } :=
  ⟨⟨h.inv.func, h.inv.data, h.inv.resTys, h.inv.valueReg, h.inv.typedReg, h.inv.defInst,
    h.inv.defClif, h.inv.slotOff, h.inv.resTysM, h.inv.valTyM, h.inv.addr64, h.inv.intOps⟩,
    S.tryRegsOk ctx trs h.scope⟩

end Backend.Proof.Driver

-- **The typed rule families over `CtxTS S`** (the `…W` definitions with `CtxTS S`).
scopeS_transport_defs

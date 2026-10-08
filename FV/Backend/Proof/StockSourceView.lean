import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.StockProjection

/-!
A proof-only identity-register view reuses source-pattern facts from the legacy
context invariant. It never changes the stock driver's register assignment.
The DFG extractors and pattern matches are independent of that assignment.
-/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

def sourceIdentityCtx (ctx : Ctx) : Ctx := { ctx with
  valReg := (Array.range ctx.valTy.size).map (fun x => some (.vreg x .int)) }

private theorem identityView_valueReg (ctx : Ctx) (x : Nat) :
    (sourceIdentityCtx ctx).valueReg? x =
      if x < ctx.valTy.size then some (.vreg x .int) else none := by
  by_cases hx : x < ctx.valTy.size <;>
    simp [sourceIdentityCtx, Ctx.valueReg?, hx]

/-- Every mapped source context has a canonical identity-register source view.
Only the register field changes; this is not a runtime lowering context. -/
theorem MappedCtxInv.identityView {f : Clif.Function} {ctx : Ctx} (h : MappedCtxInv f ctx) :
    CtxInv f (sourceIdentityCtx ctx) := by
  refine ⟨h.func, h.data, h.instE, h.resTys, ?_, ?_, h.defInst, h.defClif,
    h.slotOff, h.resTysE, h.valTyE, h.addr64⟩
  · intro x r hr
    rw [identityView_valueReg] at hr
    split at hr
    · exact (Option.some.inj hr).symm
    · cases hr
  · intro x t ht
    have hx : x < ctx.valTy.size := by
      change (ctx.valTy[x]?).join = some t at ht
      cases he : ctx.valTy[x]? with
      | none => rw [he] at ht; cases ht
      | some value => exact (Array.getElem?_eq_some_iff.mp he).1
    rw [identityView_valueReg]
    simp only [hx, ite_true]

/-- DFG extraction depends on the source view, not assigned register numbers. -/
theorem DFGViewEq.externExtract {ctx original : Ctx} (h : DFGViewEq ctx original)
    (t : Term) (v : V) (st : LState) :
    Backend.externExtract ctx t v st = Backend.externExtract original t v st := by
  simp only [Backend.externExtract, Ctx.defInst?, Ctx.valueType?, Ctx.defClif?,
    h.func, h.insts, h.valTy, h.valDef]

/-- Stock pattern matching transports to any equal source view, including the
canonical proof view, without a condition on the scheduling state. -/
theorem DFGViewEq.stock_matchPat {ctx original : Ctx} (h : DFGViewEq ctx original)
    (p : Program) (st : State) (pat : Pattern) (v : V) (env : Isle.Interp.Env V) :
    matchPat p (Stock.sem ctx) st pat v env =
      matchPat p (Backend.sem original) st.base pat v env :=
  matchPat_restate p (Backend.sem original) State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t v st => h.externExtract t v st.base) st pat v env

private theorem sourceIdentityView (ctx : Ctx) : DFGViewEq ctx (sourceIdentityCtx ctx) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem MappedCtxInv.identityView_witness :
    ∃ f ctx, MappedCtxInv f ctx ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      CtxInv f (sourceIdentityCtx ctx) ∧
      (sourceIdentityCtx ctx).valueReg? 2 = some (.vreg 2 .int) := by
  obtain ⟨_, _, hctx, hreg⟩ := buildCtx_mappedInv_witness
  refine ⟨_, _, hctx, hreg, hctx.identityView, ?_⟩
  rw [identityView_valueReg]
  decide

theorem DFGViewEq.externExtract_witness :
    ∃ f ctx, MappedCtxInv f ctx ∧ DFGViewEq ctx (sourceIdentityCtx ctx) ∧
      Backend.externExtract ctx T.def_inst (.value 2) sinkState.base = .ok [.inst 0] ∧
      Backend.externExtract ctx T.def_inst (.value 2) sinkState.base =
        Backend.externExtract (sourceIdentityCtx ctx) T.def_inst (.value 2) sinkState.base := by
  obtain ⟨_, _, hctx, _⟩ := buildCtx_mappedInv_witness
  exact ⟨_, _, hctx, sourceIdentityView _, rfl, (sourceIdentityView _).externExtract _ _ _⟩

theorem DFGViewEq.stock_matchPat_witness :
    ∃ f ctx, MappedCtxInv f ctx ∧ DFGViewEq ctx (sourceIdentityCtx ctx) ∧
      matchPat projectionProgram (Stock.sem ctx) sinkState projectionPat (.value 2) #[none] =
        .ok (some #[some (.inst 0)]) ∧
      matchPat projectionProgram (Stock.sem ctx) sinkState projectionPat (.value 2) #[none] =
        matchPat projectionProgram (Backend.sem (sourceIdentityCtx ctx)) sinkState.base
          projectionPat (.value 2) #[none] := by
  obtain ⟨_, _, hctx, _⟩ := buildCtx_mappedInv_witness
  exact ⟨_, _, hctx, sourceIdentityView _, rfl, (sourceIdentityView _).stock_matchPat _ _ _ _ _⟩

end Backend.Stock.Proof

import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.StockProjection

/-! Stock pattern matching depends on source/DFG fields, independently of the
register mapping and scheduler constructors. -/
namespace Backend.Stock.Proof

open Isle Isle.Interp Isle.Aarch64

theorem DFGViewEq.externExtract_eq {ctx original : Ctx}
    (view : DFGViewEq ctx original) (t : Term) (v : V) (st : LState) :
    Backend.externExtract ctx t v st = Backend.externExtract original t v st := by
  simp only [Backend.externExtract, Ctx.defInst?, Ctx.valueType?, Ctx.defClif?,
    view.valDef, view.valTy, view.insts, view.func]

theorem stock_matchPat_source {ctx original : Ctx} (view : DFGViewEq ctx original)
    (p : Program) (st : State) (pat : Pattern) (v : V) (env : Isle.Interp.Env V) :
    matchPat p (Stock.sem ctx) st pat v env =
      matchPat p (Backend.sem original) st.base pat v env :=
  matchPat_restate p (Backend.sem original) State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t v st => view.externExtract_eq t v st.base) st pat v env

theorem stock_matchArgs_source {ctx original : Ctx} (view : DFGViewEq ctx original)
    (p : Program) (st : State) (ps : List Pattern) (vs : List V) (env : Isle.Interp.Env V) :
    matchArgs p (Stock.sem ctx) st ps vs env =
      matchArgs p (Backend.sem original) st.base ps vs env :=
  matchArgs_restate p (Backend.sem original) State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t v st => view.externExtract_eq t v st.base) st ps vs env

private def originalSinkCtx : Ctx := { sinkCtx with valReg := #[some (.vreg 0 .int)] }

private theorem sinkView : DFGViewEq sinkCtx originalSinkCtx :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stock_extract_source_witness :
    sinkCtx.valueReg? 0 = some (.vreg 192 .int) ∧
    originalSinkCtx.valueReg? 0 = some (.vreg 0 .int) ∧
    Backend.externExtract sinkCtx T.def_inst (.value 0) sinkState.base =
      Backend.externExtract originalSinkCtx T.def_inst (.value 0) sinkState.base ∧
    Backend.externExtract sinkCtx T.def_inst (.value 0) sinkState.base = .ok [.inst 0] :=
  ⟨rfl, rfl, sinkView.externExtract_eq _ _ _, rfl⟩

theorem stock_matchPat_source_witness :
    matchPat projectionProgram (Stock.sem sinkCtx) sinkState projectionPat (.value 0) #[none] =
      matchPat projectionProgram (Backend.sem originalSinkCtx) sinkState.base
        projectionPat (.value 0) #[none] ∧
    matchPat projectionProgram (Stock.sem sinkCtx) sinkState projectionPat (.value 0) #[none] =
      .ok (some #[some (.inst 0)]) :=
  ⟨stock_matchPat_source sinkView _ _ _ _ _, rfl⟩

theorem stock_matchArgs_source_witness :
    matchArgs projectionProgram (Stock.sem sinkCtx) sinkState [projectionPat] [.value 0] #[none] =
      matchArgs projectionProgram (Backend.sem originalSinkCtx) sinkState.base
        [projectionPat] [.value 0] #[none] ∧
    matchArgs projectionProgram (Stock.sem sinkCtx) sinkState [projectionPat] [.value 0] #[none] =
      .ok (some #[some (.inst 0)]) :=
  ⟨stock_matchArgs_source sinkView _ _ _ _ _, rfl⟩

end Backend.Stock.Proof

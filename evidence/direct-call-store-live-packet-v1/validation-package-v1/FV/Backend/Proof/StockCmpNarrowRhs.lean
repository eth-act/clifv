import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.StockCmpExtendBuilder
import FV.Backend.Proof.StockCmpNarrowExtendRequest
import FV.Backend.Proof.StockCmpNarrowExtendOp
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem condition (ctx : Ctx) (st : State) (cc : Clif.IntCC) :
    Stock.externCtor ctx T.cond_code [.data 145 (ccIdx cc) []] st =
      .ok (.data 96 (condOf cc).idx [],st) := by
  rw [stock_ctor_baseOnly ctx T.cond_code _ st (by decide)]
  have legacy := (ctor_cond_code_iff ctx st.base (.data 145 (ccIdx cc) [])
    (.data 96 (condOf cc).idx []) st.base).mpr
    ⟨condOf cc,by rw [V.intcc?_data]; exact some_bind_ccIdx cc,rfl,rfl⟩
  exact congrArg (fun r => match r with
    | .ok (v,base) => ExtResult.ok (v,{st with base})
    | .fail => .fail | .unmodeled e => .unmodeled e) legacy

/-- Actual narrow register-comparison RHS execution requests both original
sources, emits only the left extension, and builds the right extension into the
flag producer. The complete Stock state is retained. -/
theorem stock_cmp_narrow_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    (signed half : Bool) (cc : Clif.IntCC) {x y : Nat} {rx ry : Reg}
    (type : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+160)
      (if signed then rule_inst_5108 else rule_inst_5117).rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),
        some (.ty (.int (if half then 16 else 8))),some (.value y)]).run (st,tr) =
      .ok (some (.data 123 2 [.data 47 1 [.data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,
        .reg (st.base.fresh .int).1,.reg ry,
        .data 84 (if signed then (if half then 5 else 4) else (if half then 1 else 0)) []]],
        .data 96 (condOf cc).idx []]),
        {(st.mark x).mark y with base := ((st.base.fresh .int).2.emit
          (.extend (st.base.fresh .int).1 rx signed (if half then 16 else 8) 32))},trace) := by
  have width : (if half then 16 else 8) ≤ 16 := by cases half <;> decide
  obtain ⟨leftTrace,leftRun⟩ := stock_cmp_narrow_extend_request hp ctx signed width type mapX st safeX tr (n+94)
  let extended : State := {st.mark x with base := ((st.base.fresh .int).2.emit
    (.extend (st.base.fresh .int).1 rx signed (if half then 16 else 8) 32))}
  have rightRun := stock_put_in_reg ctx extended y ry mapY safeY
  dsimp only [extended] at rightRun
  have op := fun q trace fuel => stock_cmp_narrow_extend_op hp ctx signed half q trace fuel
  have builder := fun q trace fuel => stock_cmp_extend_builder hp ctx (cfg := {}) rfl q trace fuel
    (.data 93 0 []) (.reg (st.base.fresh .int).1) (.reg ry)
    (.data 84 (if signed then (if half then 5 else 4) else (if half then 1 else 0)) [])
  have code := fun q => condition ctx q cc
  have get0 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[0]? = some (some (.data 145 (ccIdx cc) [])) := rfl
  have get1 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[1]? = some (some (.value x)) := rfl
  have get2 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[2]? = some (some (.ty (.int (if half then 16 else 8)))) := rfl
  have get3 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[3]? = some (some (.value y)) := rfl
  cases hp
  cases signed
  · refine Exists.intro ?traceU ?proofU
    case proofU =>
      simp only [Bool.false_eq_true,ite_false] at *
      isel_eval [*, isel_monad,rule_inst_5117,sem_ctor,sem_mkData,Array.getElem?_eq_getElem]
      all_goals rfl
  · refine Exists.intro ?traceS ?proofS
    case proofS =>
      simp only [ite_true] at *
      isel_eval [*, isel_monad,rule_inst_5108,sem_ctor,sem_mkData,Array.getElem?_eq_getElem]
      all_goals rfl
end Backend.Stock.Proof.ScalarCmp

import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.StockCmpBuilders
import FV.Backend.Proof.StockCmpNarrowExtendRequest
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

/-- The actual narrow immediate comparison RHS requests and zero-extends
only the original left operand, preserving complete Stock scheduling state. -/
theorem stock_cmp_narrow_immediate_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    (half : Bool) (cc : Clif.IntCC) {x : Nat} {rx : Reg} (imm : Imm12)
    (type : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+160) rule_inst_5134.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),
        some (.value x),some (.op (.imm12 imm))]).run (st,tr) =
      .ok (some (.data 123 2 [.data 47 1 [.data 58 4 [.data 59 10 [],.data 93 0 [],.reg .xzr,
        .reg (st.base.fresh .int).1,.op (.imm12 imm)]],.data 96 (condOf cc).idx []]),
        {st.mark x with base := ((st.base.fresh .int).2.emit
          (.extend (st.base.fresh .int).1 rx false (if half then 16 else 8) 32))},trace) := by
  have width : (if half then 16 else 8) ≤ 16 := by cases half <;> decide
  obtain ⟨leftTrace,leftRun⟩ := stock_cmp_narrow_extend_request hp ctx false width type mapped st safe tr (n+94)
  simp only [Bool.false_eq_true,ite_false] at leftRun
  have builder := fun q trace fuel => stock_cmp_imm_builder hp ctx (cfg := {}) rfl q trace fuel
    (.data 93 0 []) (.reg (st.base.fresh .int).1) (.op (.imm12 imm))
  have code := fun q => condition ctx q cc
  have get0 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[0]? = some (some (.data 145 (ccIdx cc) [])) := rfl
  have get1 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[1]? = some (some (.ty (.int (if half then 16 else 8)))) := rfl
  have get2 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[2]? = some (some (.value x)) := rfl
  have get3 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[3]? = some (some (.op (.imm12 imm))) := rfl
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, isel_monad,rule_inst_5134,sem_ctor,sem_mkData,Array.getElem?_eq_getElem]
    all_goals rfl
end Backend.Stock.Proof.ScalarCmp

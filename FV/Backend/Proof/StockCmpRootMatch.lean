import FV.Backend.Lowering.Stock
import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.IselCovForm
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
def cmpEnv (cc : Clif.IntCC) (x y : Nat) : Isle.Interp.Env V :=
  env3 (.value x) (.value y) (.data 145 (ccIdx cc) [])
/-- Original comparison data matches its real root and canonical source
environment, preserving every Stock scheduling field. -/
theorem stock_cmp_root_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i x y w : Nat} {cc : Clif.IntCC} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int 8))
    (data : info.data = .data 152 14 [.data 151 72 [],.values [x,y],.data 145 (ccIdx cc) []])
    (operandType : ctx.valueType? x = some (.int w)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_2215 [.inst i]).run (st,tr) =
      .ok (some (cmpEnv cc x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have typed := ext_value_type ctx st.base operandType
  cases hp
  isel_eval [*,rule_lower_2215,cmpEnv,env3,sem_extract,sem_unData,ext_value_array_2,ext_ty_int]
/-- Actual successful comparison matching derives the original operand type,
canonical environment and unchanged state internally. -/
theorem stock_cmp_root_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {i x y n : Nat} {cc : Clif.IntCC} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int 8))
    (data : info.data = .data 152 14 [.data 151 72 [],.values [x,y],.data 145 (ccIdx cc) []])
    {st next : State} {tr trace : Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_2215 [.inst i]).run (st,tr) =
      .ok (some env,next,trace)) :
    (∃ w,ctx.valueType? x = some (.int w)) ∧ env = cmpEnv cc x y ∧ next = st ∧ trace = tr := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  isel_inv [*,rule_lower_2215,cmpEnv,env3,sem_extract,sem_unData,ext_value_array_2,
    ext_value_type_iff,ext_ty_int_iff] at matched
  isel_destruct
  simp only [source,Option.some.injEq] at *
  subst_vars
  simp only [data,V.data.injEq,List.cons.injEq] at *
  isel_destruct
  subst_vars
  isel_inv_simp [ext_value_array_2,ext_value_type_iff,ext_ty_int_iff] at *
  isel_destruct
  subst_vars
  obtain ⟨typeCall⟩ : Nonempty (Backend.externExtract ctx T.value_type (.value x) next.base = .ok [_]) := ⟨by assumption⟩
  obtain ⟨t,typed,fields⟩ := (ext_value_type_iff ctx next.base x _).mp typeCall
  have valueEq := (List.cons.inj fields).1
  cases valueEq
  obtain ⟨integer,_⟩ := (ext_ty_int_iff ctx next.base t _).mp (by assumption)
  cases t <;> simp [CTy.isInt] at integer
  exact ⟨⟨_,typed⟩,rfl⟩
end Backend.Stock.Proof.ScalarCmp

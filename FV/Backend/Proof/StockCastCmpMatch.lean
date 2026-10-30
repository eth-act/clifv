import FV.Backend.Proof.StockCmpRootMatch

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

private theorem array2_observed (ctx : Ctx) (st : LState) {v a b : V}
    (run : Backend.externExtract ctx T.value_array_2 v st = .ok [a,b]) :
    ∃ x y,v = .values [x,y] ∧ a = .value x ∧ b = .value y := by
  cases v <;> try (solve | cases run)
  rename_i xs
  cases xs with
  | nil => cases run
  | cons x xs =>
    cases xs with
    | nil => cases run
    | cons y xs =>
      cases xs with
      | nil => cases run; exact ⟨x,y,rfl,rfl,rfl⟩
      | cons => cases run

/-- The real fused cast matcher follows the original comparison definition,
binds the original operands and condition, and preserves every scheduling field. -/
theorem stock_cast_cmp_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i z j x y w operandWidth : Nat} {cc : Clif.IntCC} {info cmp : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 141 [],.value z])
    (fits : w ≤ 64) (defined : ctx.defInst? z = some j) (found : ctx.insts[j]? = some cmp)
    (cmpType : cmp.resTys.head? = some (.int 8))
    (cmpData : cmp.data = .data 152 14 [.data 151 72 [],.values [x,y],.data 145 (ccIdx cc) []])
    (operandType : ctx.valueType? x = some (.int operandWidth)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) rule_lower_1281 [.inst i]).run (st,tr) =
      .ok (some (cmpEnv cc x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have comparison := ext_inst_data_value ctx st.base found
  rw [cmpData,cmpType,Option.getD_some] at comparison
  have defining := ext_def_inst_some ctx st.base defined
  have types := ext_value_type ctx st.base operandType
  have small := ext_fits_in_64 ctx st.base w
  simp only [fits,ite_true] at small
  cases hp
  isel_eval [*,rule_lower_1281,cmpEnv,env3,sem_extract,sem_unData,ext_value_array_2,ext_ty_int]

/-- A successful fused match exposes its actual defining instruction and
original operand environment; it does not take an invented comparison record. -/
theorem stock_cast_cmp_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {i z w n : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 141 [],.value z])
    {st next : State} {tr trace : Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) rule_lower_1281 [.inst i]).run (st,tr) =
      .ok (some env,next,trace)) :
    ∃ j cmp x y cond operandWidth,
      ctx.defInst? z = some j ∧ ctx.insts[j]? = some cmp ∧
      cmp.data = .data 152 14 [.data 151 72 [],.values [x,y],cond] ∧
      ctx.valueType? x = some (.int operandWidth) ∧
      env = env3 (.value x) (.value y) cond ∧ next = st ∧ trace = tr := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  isel_inv [*,rule_lower_1281,env3,sem_extract,sem_unData,ext_value_array_2,
    ext_def_inst_iff,ext_value_type_iff,ext_ty_int_iff,ext_fits_in_64_iff] at matched
  isel_destruct
  subst_vars
  simp only [source,Option.some.injEq] at *
  subst_vars
  simp only [data,V.data.injEq,List.cons.injEq] at *
  isel_destruct
  subst_vars
  isel_inv_simp [ext_def_inst_iff,ext_inst_data_value_iff,ext_value_type_iff,ext_ty_int_iff] at *
  isel_destruct
  subst_vars
  isel_inv_simp [ext_inst_data_value_iff] at *
  isel_destruct
  subst_vars
  obtain ⟨x,y,array,first,second⟩ := array2_observed ctx next.base (by assumption)
  subst_vars
  obtain ⟨operandType,typed,fields⟩ := (ext_value_type_iff ctx next.base x _).mp (by assumption)
  have equal := (List.cons.inj fields).1
  cases equal
  obtain ⟨integer,_⟩ := (ext_ty_int_iff ctx next.base operandType _).mp (by assumption)
  cases operandType <;> simp [CTy.isInt] at integer
  exact ⟨_,by assumption,_,by assumption,x,y,_,Eq.symm (by assumption),⟨_,typed⟩,rfl⟩

end Backend.Stock.Proof.ScalarCmp

import FV.Backend.Proof.StockCmpNarrowConstantSelection
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
def cmpZeroRule (left nonzero : Bool) : Rule :=
  if left then (if nonzero then rule_inst_5173 else rule_inst_5171)
  else (if nonzero then rule_inst_5172 else rule_inst_5170)
private theorem constant_extract {ctx : Ctx} {x : Nat} {st : LState} {node ty payload : V}
    (definition : externExtract ctx T.def_inst (.value x) st = .ok [node])
    (instruction : externExtract ctx T.inst_data_value node st =
      .ok [ty,.data 152 35 [.data 151 57 [],payload]]) :
    ∃ j info,ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],payload] := by
  obtain ⟨j,defined,equal⟩ := (ext_def_inst_iff ctx st x [node]).mp definition
  have nodeEq := (List.cons.inj equal).1
  subst node
  obtain ⟨info,found,equal⟩ := (ext_inst_data_value_iff ctx st j _).mp instruction
  have fields := (List.cons.inj (List.cons.inj equal).2).1
  exact ⟨j,info,defined,found,fields.symm⟩
private theorem constant_integer {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x j : Nat} {info : IInfo} {payload : V}
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],payload]) : ∃ literal,payload = .int literal := by
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty,c,rfl,fields⟩ := instData_iconst_inv raw
  exact ⟨imm64OfIconst ty c,(List.cons.inj fields).1⟩
private def ZeroObservation (ctx : Ctx) (left nonzero : Bool) (cc : Clif.IntCC) (x y : Nat)
    (st : State) (tr : Array RuleId) (env : Isle.Interp.Env V) (after : State × Array RuleId) : Prop :=
    ∃ j info literal,cc = (if nonzero then .ne else .eq) ∧
      ctx.defInst? (if left then x else y) = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧ u64 literal = 0 ∧
      env = #[some (.value (if left then y else x))] ∧ after = (st,tr)
private theorem zero_observation_elim {ctx : Ctx} {left nonzero : Bool} {cc : Clif.IntCC} {x y : Nat}
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (h : ZeroObservation ctx left nonzero cc x y st tr env after) :
    ∃ j info literal,cc = (if nonzero then .ne else .eq) ∧
      ctx.defInst? (if left then x else y) = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧ u64 literal = 0 ∧
      env = #[some (.value (if left then y else x))] ∧ after = (st,tr) := by
  unfold ZeroObservation at h
  exact h
attribute [local irreducible] ZeroObservation
/-- A successful actual zero-rule match derives its source-side classification,
original zero metadata, canonical environment and unchanged state/trace. -/
theorem stock_cmp_zero_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (left nonzero : Bool) (cc : Clif.IntCC) (x y : Nat)
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (cmpZeroRule left nonzero)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) :
    ∃ j info literal,cc = (if nonzero then .ne else .eq) ∧
      ctx.defInst? (if left then x else y) = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧ u64 literal = 0 ∧
      env = #[some (.value (if left then y else x))] ∧ after = (st,tr) := by
  suffices observed : ZeroObservation ctx left nonzero cc x y st tr env after by
    exact zero_observation_elim observed
  have hp' := hp
  cases left <;> cases nonzero <;> cases cc
  all_goals simp only [cmpZeroRule,Bool.false_eq_true,ite_true,ite_false] at matched ⊢
  all_goals isel_inv_simp [hp'.t1,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,
    rule_inst_5170,rule_inst_5171,rule_inst_5172,rule_inst_5173,sem_extract,sem_unData,sem_eq,zero,ccIdx] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [hp'.t1,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,
    rule_inst_5170,rule_inst_5171,rule_inst_5172,rule_inst_5173,sem_extract,sem_unData,sem_eq,zero,ccIdx] at *
  all_goals isel_destruct <;> subst_vars
  all_goals obtain ⟨j,info,defined,found,data⟩ := constant_extract (by assumption) (by assumption)
  all_goals obtain ⟨literal,payload⟩ := constant_integer inv defined found data
  all_goals subst_vars
  all_goals isel_inv_simp [ext_u64_from_imm64] at *
  all_goals unfold ZeroObservation
  all_goals refine ⟨j,info,literal,rfl,defined,found,data,?_,?_,rfl⟩
  all_goals first | assumption | rfl | omega
end Backend.Stock.Proof.ScalarCmp

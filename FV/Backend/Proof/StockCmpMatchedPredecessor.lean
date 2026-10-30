import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockCmpPredecessorSignedMatch
import FV.Backend.Proof.StockCmpPredecessorUnsignedMatch
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem one (ctx : Ctx) : (Stock.sem ctx).int 4 1 = .int 1 := rfl
private theorem yes (ctx : Ctx) : (Stock.sem ctx).bool true = .bool true := rfl
end Integers
private theorem normalized_sub_one (i : Int) : u64 ((u64 i : Int)-1) = u64 (i-1) := by
  unfold u64
  have positive : 0 ≤ i % (2^64 : Int) := Int.emod_nonneg _ (by decide)
  rw [Int.toNat_of_nonneg positive,Int.sub_emod,Int.emod_emod]
  rw [← Int.sub_emod]
private theorem odd_ctor (ctx : Ctx) (a : Int) (st : State) :
    Stock.externCtor ctx T.u64_is_odd [.int a] st = .ok (.bool (a % 2 == 1),st) := by
  rw [stock_ctor_baseOnly ctx T.u64_is_odd _ st (by decide)]
  rfl
private theorem sub_ctor (ctx : Ctx) (a : Int) (st : State) :
    Stock.externCtor ctx T.u64_wrapping_sub [.int a,.int 1] st = .ok (.int (u64 (a-1)),st) := by
  rw [stock_ctor_baseOnly ctx T.u64_wrapping_sub _ st (by decide)]
  rfl
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
private def PredecessorObservation (ctx : Ctx) (signed : Bool) (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat)
    (st : State) (tr : Array RuleId) (env : Isle.Interp.Env V) (after : State × Array RuleId) : Prop :=
  ∃ j info literal imm,cc = (if signed then .sge else .uge) ∧
      ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧
      u64 literal % 2 = 1 ∧ Imm12.ofNat? (u64 (literal-1)) = some imm ∧
      env = #[some (.ty (.int sz.bits)),some (.value x),some (.int (u64 literal)),some (.op (.imm12 imm))] ∧
      after = (st,tr)
private theorem predecessor_observation_elim {ctx : Ctx} {signed : Bool} {cc : Clif.IntCC} {sz : OperandSize} {x y : Nat}
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (h : PredecessorObservation ctx signed cc sz x y st tr env after) :
  ∃ j info literal imm,cc = (if signed then .sge else .uge) ∧
      ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧
      u64 literal % 2 = 1 ∧ Imm12.ofNat? (u64 (literal-1)) = some imm ∧
      env = #[some (.ty (.int sz.bits)),some (.value x),some (.int (u64 literal)),some (.op (.imm12 imm))] ∧
      after = (st,tr) := h
attribute [local irreducible] PredecessorObservation
/-- Successful actual adjusted-immediate matching derives its condition code,
original defining integer, oddness, encoded predecessor, normalized literal slot
and complete unchanged match state/trace. No operand classification is assumed. -/
theorem stock_cmp_predecessor_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (signed : Bool) (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat)
    (typed : ctx.valueType? x = some (.int sz.bits))
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (if signed then rule_inst_5160 else rule_inst_5155)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) :
  ∃ j info literal imm,cc = (if signed then .sge else .uge) ∧
      ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧
      u64 literal % 2 = 1 ∧ Imm12.ofNat? (u64 (literal-1)) = some imm ∧
      env = #[some (.ty (.int sz.bits)),some (.value x),some (.int (u64 literal)),some (.op (.imm12 imm))] ∧
      after = (st,tr) := by
  suffices h : PredecessorObservation ctx signed cc sz x y st tr env after by
    exact predecessor_observation_elim h
  have hp' := hp
  have lookup := ext_value_type ctx st.base typed
  cases signed
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at matched
  all_goals isel_inv_simp [lookup,hp'.t1,hp'.t2,hp'.t120,hp'.t144,hp'.t209,hp'.t325,hp'.t1167,hp'.t1199,
    hp'.t2272,hp'.t2276,hp'.t2341,hp'.t2482,rule_inst_5160,rule_inst_5155,sem_extract,sem_unData,sem_eq,sem_ctor,one,yes] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [lookup,hp'.t1,hp'.t2,hp'.t120,hp'.t144,hp'.t209,hp'.t325,hp'.t1167,hp'.t1199,
    hp'.t2272,hp'.t2276,hp'.t2341,hp'.t2482,rule_inst_5160,rule_inst_5155,sem_extract,sem_unData,sem_eq,sem_ctor,one,yes] at *
  all_goals isel_destruct <;> subst_vars
  all_goals obtain ⟨j,info,defined,found,data⟩ := constant_extract (by assumption) (by assumption)
  all_goals obtain ⟨literal,payload⟩ := constant_integer inv defined found data
  all_goals subst_vars
  all_goals isel_inv_simp [ext_u64_from_imm64,ext_imm12_from_u64_iff,odd_ctor,sub_ctor] at *
  all_goals isel_destruct <;> subst_vars
  all_goals simp only [odd_ctor,sub_ctor,ExtResult.ok.injEq,Prod.mk.injEq,V.bool.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [typed,ext_u64_from_imm64,ext_imm12_from_u64_iff,
    ext_ty_32_or_64_iff,odd_ctor,sub_ctor] at *
  all_goals isel_destruct <;> subst_vars
  all_goals simp only [normalized_sub_one,u64_ofNat (u64_lt' (literal-1))] at *
  all_goals obtain ⟨imm,encoded⟩ : ∃ imm,Imm12.ofNat? (u64 (literal-1)) = some imm := ⟨_,by assumption⟩
  all_goals unfold PredecessorObservation
  all_goals refine ⟨j,info,literal,imm,?_,defined,found,data,?_,?_,?_,?_⟩
  all_goals first
    | assumption
    | rfl
    | (apply ccIdx_eq_3; assumption)
    | (apply ccIdx_eq_7; assumption)
    | (apply Array.toList_inj.mp; simp_all [Array.toList_setIfInBounds,List.set,List.replicate])
    | omega
end Backend.Stock.Proof.ScalarCmp

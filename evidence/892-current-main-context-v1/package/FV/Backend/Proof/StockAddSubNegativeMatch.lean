import FV.Backend.Proof.IselRulesALUA
import FV.Backend.Proof.StockAddSubMatch
import FV.Backend.Proof.StockAddSubNegativePure
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
theorem stock_addsub_neg_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {y j w : Nat} {kk : Int} {info : IInfo} (defined : ctx.defInst? y = some j)
    (source : ctx.insts[j]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 35 [.data 151 57 [],.int kk])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 64 344 [.value y]).run (st,tr) =
      .ok ((negImm12? w kk).map (fun imm => .op (.imm12 imm)),st,
        if (negImm12? w kk).isSome then tr.push rule_inst_2404.id else tr) := by
  cases choice : negImm12? w kk with
  | none =>
    have legacy := imm12_from_negated_value_none hp ctx (cfg := {}) rfl st.base tr n defined source type data choice
    simpa only [choice,Option.map_none,Option.isSome_none,Bool.false_eq_true,ite_false] using
      Negative.stock_addsub_negative_pure_helper hp ctx rfl (by decide) legacy
  | some imm =>
    have legacy := imm12_from_negated_value_some hp ctx (cfg := {}) rfl st.base tr n defined source type data choice
    simpa only [choice,Option.map_some,Option.isSome_some,ite_true] using
      Negative.stock_addsub_negative_pure_helper hp ctx rfl (by decide) legacy
theorem stock_addsub_neg_match {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y w j cw : Nat} {kk : Int} {info infoj : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [],.values [x,y]])
    (defined : ctx.defInst? (if left then x else y) = some j) (found : ctx.insts[j]? = some infoj)
    (constantType : infoj.resTys.head? = some (.int cw))
    (constantData : infoj.data = .data 152 35 [.data 151 57 [],.int kk])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+40) (negImmRule subtract left) [.inst i]).run (st,tr) =
      .ok ((negImm12? cw kk).map (negImmEnv left w (if left then y else x) (if left then x else y)),st,
        if (negImm12? cw kk).isSome then tr.push rule_inst_2404.id else tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have helper := fun q trace fuel => stock_addsub_neg_helper hp ctx defined found constantType constantData q trace fuel
  cases choice : negImm12? cw kk <;> simp only [choice] at helper
  all_goals cases hp
  all_goals cases subtract <;> cases left
  · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_98,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_102,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_810,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · cases side rfl
  · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_98,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_102,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_false,ite_true] at *
    isel_eval [*,rule_lower_810,sem_extract,sem_unData,ext_ty_int_ref_scalar_64_extract ctx st.base width,ext_value_array_2]
    all_goals rfl
  · cases side rfl
private theorem neg_match_project {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i m : Nat} {st next : State} {tr trace : Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule p (Stock.sem ctx) {} (m+40) (negImmRule subtract left) [.inst i]).run (st,tr) = .ok (some env,next,trace)) :
    (matchRule p (Backend.sem ctx) {} (m+40) (negImmRule subtract left) [.inst i]).run (st.base,tr) = .ok (some env,next.base,trace) := by
  apply Negative.stock_addsub_negative_match_project hp ctx (fuel := m+39) _ matched
  cases subtract <;> cases left
  · simp only [negImmRule,Bool.false_eq_true,ite_false,ite_true]
    intro il member
    simp only [rule_lower_98,rule_lower_102,rule_lower_810,List.mem_singleton] at member
    subst il
    intro t call
    simp only [exprCalls,argCalls,List.mem_cons,List.not_mem_nil,List.append_nil,List.mem_nil_iff,or_false] at call
    rcases call with rfl
    decide
  · simp only [negImmRule,Bool.false_eq_true,ite_false,ite_true]
    intro il member
    simp only [rule_lower_98,rule_lower_102,rule_lower_810,List.mem_singleton] at member
    subst il
    intro t call
    simp only [exprCalls,argCalls,List.mem_cons,List.not_mem_nil,List.append_nil,List.mem_nil_iff,or_false] at call
    rcases call with rfl
    decide
  · simp only [negImmRule,Bool.false_eq_true,ite_false,ite_true]
    intro il member
    simp only [rule_lower_98,rule_lower_102,rule_lower_810,List.mem_singleton] at member
    subst il
    intro t call
    simp only [exprCalls,argCalls,List.mem_cons,List.not_mem_nil,List.append_nil,List.mem_nil_iff,or_false] at call
    rcases call with rfl
    decide
  · cases side rfl
private theorem neg_helper_original {p : Program} (hp : Data p) (ctx : Ctx) {f : Clif.Function} (inv : MappedCtxInv f ctx) {m : Nat} {y : Nat} {s s2 : LState × Array RuleId} {v : V}
    (h : (applyTerm p (Backend.sem ctx) {} (m + 5) 64 344 [.value y]).run s = .ok (some v, s2)) :
    ∃ j infoj ty c, ctx.defInst? y = some j ∧ ctx.insts[j]? = some infoj ∧
      infoj.clif = some (.iconst ty c) ∧
      infoj.data = .data 152 35 [.data 151 57 [], .int (imm64OfIconst ty c)] ∧
      infoj.resTys.head? = some (.int ty.width) := by
  obtain ⟨r, hr, m0, env0, s1, st, tr, hmn, hmatch, -, -⟩ :=
    applyTerm_internal_some rfl hp.t344 term_344_kind rfl h
  rw [hp.r344, List.mem_singleton] at hr
  rw [hp.r344, List.length_singleton] at hmn
  subst hr
  obtain ⟨m1, rfl⟩ : ∃ m1, m0 = m1 + 1 := ⟨m0 - 1, by omega⟩
  obtain ⟨env1, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, hp1, -⟩ := matchArgs_cons_inv (qs := []) ha
  obtain ⟨j, infoj, fs, e0, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hp1
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif inv.identityView hj hij
  rw [hdj] at hdat
  obtain ⟨ty, c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨tys, htys, hres, -⟩ := inv.resTys j infoj _ hij hcl
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have typeE := inv.resTysE j infoj hij (CTy.ofClif ty) (by rw [hres]; simp)
  exact ⟨j, infoj, ty, c, hj, hij, hcl, hdj, by
    rw [hres]; simp [ofClif_int_width (isInt_of_ofClif_mem typeE)]⟩

theorem stock_addsub_neg_match_operand {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y m : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {st next : State} {tr trace : Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule p (Stock.sem ctx) {} (m+40) (negImmRule subtract left) [.inst i]).run (st,tr) = .ok (some env,next,trace)) :
    ∃ (j : Nat) (infoj : IInfo) (ty' : Clif.Ty) (c : BitVec ty'.width),
      ctx.defInst? (if left then x else y) = some j ∧ ctx.insts[j]? = some infoj ∧
      infoj.clif = some (.iconst ty' c) ∧ infoj.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty' c)] ∧
      infoj.resTys.head? = some (.int ty'.width) := by
  obtain ⟨_,data,_⟩ := stock_addsub_source_data inv subtract source clif
  have legacy := neg_match_project hp ctx subtract left side matched
  cases subtract <;> cases left
  · simp only [negImmRule,Bool.false_eq_true,ite_false,ite_true] at legacy clif ⊢
    obtain ⟨actual,fields,e0,e1,actualInfo,actualData,rest,iflets⟩ := root_match_inv hp ctx
      (m := m+39) (r := rule_lower_98) rfl hp.t2449 term_2449_kind hp.t2357 term_2357_kind legacy
    rw [source] at actualInfo
    cases actualInfo
    simp only [Bool.false_eq_true,ite_false,ite_true] at data
    rw [data] at actualData
    simp only [V.data.injEq,List.cons.injEq,true_and] at actualData
    cases actualData
    obtain ⟨e2,px,py⟩ := values2_match_inv hp ctx rest
    have bound := matchPat_bind_wild_inv ctx py
    have input := getElem_bind_env (matchPat_bind_inv py).1 bound
    obtain ⟨v0,s2,run⟩ := iflet_term_var_inv ctx (m := m+35) iflets input
    exact neg_helper_original hp ctx inv (m := m+32) run
  · simp only [negImmRule,Bool.false_eq_true,ite_false,ite_true] at legacy clif ⊢
    obtain ⟨actual,fields,e0,e1,actualInfo,actualData,rest,iflets⟩ := root_match_inv hp ctx
      (m := m+39) (r := rule_lower_102) rfl hp.t2449 term_2449_kind hp.t2357 term_2357_kind legacy
    rw [source] at actualInfo
    cases actualInfo
    simp only [Bool.false_eq_true,ite_false,ite_true] at data
    rw [data] at actualData
    simp only [V.data.injEq,List.cons.injEq,true_and] at actualData
    cases actualData
    obtain ⟨e2,px,py⟩ := values2_match_inv hp ctx rest
    have bound := matchPat_bind_wild_inv ctx px
    have first := getElem_bind_env (matchPat_bind_inv px).1 bound
    have input : e1[1]? = some (some (.value x)) := by
      rw [getElem_bind_env_ne (by decide : (2 : Nat) ≠ 1) (matchPat_bind_wild_inv ctx py)]
      exact first
    obtain ⟨v0,s2,run⟩ := iflet_term_var_inv ctx (m := m+35) iflets input
    exact neg_helper_original hp ctx inv (m := m+32) run
  · simp only [negImmRule,Bool.false_eq_true,ite_false,ite_true] at legacy clif ⊢
    obtain ⟨actual,fields,e0,e1,actualInfo,actualData,rest,iflets⟩ := root_match_inv hp ctx
      (m := m+39) (r := rule_lower_810) rfl hp.t2449 term_2449_kind hp.t2358 term_2358_kind legacy
    rw [source] at actualInfo
    cases actualInfo
    simp only [Bool.false_eq_true,ite_false,ite_true] at data
    rw [data] at actualData
    simp only [V.data.injEq,List.cons.injEq,true_and] at actualData
    cases actualData
    obtain ⟨e2,px,py⟩ := values2_match_inv hp ctx rest
    have bound := matchPat_bind_wild_inv ctx py
    have input := getElem_bind_env (matchPat_bind_inv py).1 bound
    obtain ⟨v0,s2,run⟩ := iflet_term_var_inv ctx (m := m+35) iflets input
    exact neg_helper_original hp ctx inv (m := m+32) run
  · cases side rfl
theorem stock_addsub_neg_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {i x y m : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width}
    (get : fr.getAs (if left then x else y) ty = .ok v)
    {st next : State} {tr trace : Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule p (Stock.sem ctx) {} (m+40) (negImmRule subtract left) [.inst i]).run (st,tr) = .ok (some env,next,trace)) :
    ∃ imm, env = negImmEnv left ty.width (if left then y else x) (if left then x else y) imm ∧
      next = st ∧ trace = tr.push rule_inst_2404.id ∧ imm.bits < 4096 ∧
      (BitVec.ofNat (szOf ty.width).bits imm.value).setWidth ty.width = -v := by
  obtain ⟨width,data,type⟩ := stock_addsub_source_data inv subtract source clif
  obtain ⟨j,infoj,ty',c,defined,found,original,constantData,constantType⟩ :=
    stock_addsub_neg_match_operand hp inv subtract left side source clif matched
  have value := dfg_single dfg defined found original rfl (getAs_ok get) (a := ⟨ty',c⟩)
    (fun vals cm cm' run => by rw [evalInst_iconst] at run; cases run; rfl)
  cases value
  rw [stock_addsub_neg_match hp ctx subtract left side source type width data defined found constantType constantData st tr m] at matched
  cases choice : negImm12? ty.width (imm64OfIconst ty v) with
  | none => rw [choice] at matched; cases matched
  | some imm =>
    rw [choice] at matched
    simp only [Option.map_some,Option.isSome_some,ite_true,Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    obtain ⟨valid,encoded⟩ := negImm12_value width v (by unfold negImm12? at choice; exact choice)
    exact ⟨imm,envEq.symm,stateEq.symm,traceEq.symm,valid,encoded _ (szOf_bits width)⟩
end Backend.Stock.Proof.ScalarAddSub

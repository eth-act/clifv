import FV.Backend.Proof.StockDivRhs
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem source_literal {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {r : Rule} {tp xp : Pattern} {slot id x y w : Nat} {info : IInfo}
    (shape : r.args = [.term 18 209 [tp,.term 152 2449 [.term 151 2367 [],
      .term 147 1614 [xp,.term 15 1 [.term 18 209 [.wildcard 14,
        .term 152 2482 [.term 151 2341 [],.bind 134 slot (.wildcard 134)]]]]]]])
    (source : ctx.insts[id]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 83 [],.values [x,y]])
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs p (Backend.sem ctx) st r.args [.inst id] env = .ok (some env')) :
    ∃ j constant i,ctx.defInst? y = some j ∧ ctx.insts[j]? = some constant ∧
      constant.data = .data 152 35 [.data 151 57 [],.int i] := by
  rw [shape] at matched
  obtain ⟨e1,root,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl root
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [type,data,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨e2,_,patterns⟩ := matchArgs_cons_inv patterns
  obtain ⟨e3,binary,_⟩ := matchArgs_cons_inv patterns
  obtain ⟨fields,decoded,patterns⟩ := matchPat_enum_inv hp.t2449 term_2449_kind binary
  have same := sem_unData_inv decoded
  have equal : fields = [.data 151 83 [],.values [x,y]] := (V.data.inj same).2.2.symm
  subst fields
  obtain ⟨e4,_,patterns⟩ := matchArgs_cons_inv patterns
  obtain ⟨e5,_,literal⟩ := values2_match_inv hp ctx patterns
  obtain ⟨j,constant,fields,e0,defined,found,raw,_⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind literal
  obtain ⟨cl,original,dataCl⟩ := ctxInv_clif inv.identityView defined found
  rw [raw] at dataCl
  obtain ⟨ty,u,rfl,fieldsEq⟩ := instData_iconst_inv dataCl
  rw [fieldsEq] at raw
  exact ⟨j,constant,imm64OfIconst ty u,defined,found,raw⟩
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem safe_ctor_iff (ctx : Ctx) (st next : State) (t : CTy) (i : Int) (out : V) :
    Stock.externCtor ctx T.safe_divisor_from_imm64 [.ty t,.int i] st = .ok (out,next) ↔
    (u64 i % 2^(t.bytes*8) ≠ 0 ∧ u64 i % 2^(t.bytes*8) ≠ 2^(t.bytes*8)-1) ∧
      out = .int (u64 i % 2^(t.bytes*8)) ∧ next = st := by
  have expected : Stock.externCtor ctx T.safe_divisor_from_imm64 [.ty t,.int i] st =
      if (u64 i % 2^(t.bytes*8) == 0 || u64 i % 2^(t.bytes*8) == 2^(t.bytes*8)-1) then .fail
      else .ok (.int (u64 i % 2^(t.bytes*8)),st) := by
    rw [stock_ctor_baseOnly ctx T.safe_divisor_from_imm64 _ st (by decide)]
    have base : Backend.externCtor ctx T.safe_divisor_from_imm64 [.ty t,.int i] st.base =
      if (u64 i % 2^(t.bytes*8) == 0 || u64 i % 2^(t.bytes*8) == 2^(t.bytes*8)-1) then .fail
      else .ok (.int (u64 i % 2^(t.bytes*8)),st.base) := rfl
    rw [base]
    by_cases blocked : (u64 i % 2^(t.bytes*8) == 0 || u64 i % 2^(t.bytes*8) == 2^(t.bytes*8)-1) = true
    · simp only [blocked,ite_true]
      all_goals rfl
    · simp only [blocked,ite_false]
      all_goals rfl
  rw [expected]
  split
  · rename_i h
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    simp only [reduceCtorEq,false_iff,not_and]
    intro h1; omega
  · rename_i h
    simp only [Bool.or_eq_true,beq_iff_eq,not_or] at h
    simp only [ExtResult.ok.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨rfl,rfl⟩; exact ⟨h,rfl,rfl⟩
    · rintro ⟨_,rfl,rfl⟩; exact ⟨rfl,rfl⟩
def SafeMatchReceipt (ctx : Ctx) (wide : Bool) (x y w : Nat) (st : State) (tr : Array RuleId)
    (env : Isle.Interp.Env V) (middle : State × Array RuleId) : Prop :=
  ∃ j constant i,ctx.defInst? y = some j ∧ ctx.insts[j]? = some constant ∧
    constant.data = .data 152 35 [.data 151 57 [],.int i] ∧
    (u64 i % 2^((CTy.int w).bytes*8) ≠ 0 ∧ u64 i % 2^((CTy.int w).bytes*8) ≠ 2^((CTy.int w).bytes*8)-1) ∧
    env = (if wide then safeWideEnv x i (u64 i % 2^((CTy.int w).bytes*8))
      else safeNarrowEnv w x i (u64 i % 2^((CTy.int w).bytes*8))) ∧ middle = (st,tr)
private def LiteralData (ctx : Ctx) (y j : Nat) (constant : IInfo) (i : Int) : Prop :=
  ctx.defInst? y = some j ∧ ctx.insts[j]? = some constant ∧ constant.data = .data 152 35 [.data 151 57 [],.int i]
/-- Successful safe matching derives its real original literal, guard, canonical
environment and complete frame internally. -/
theorem stock_div_safe_wide_match_observed {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {id x y : Nat} {info : IInfo}
    (source : ctx.insts[id]? = some info) (type : info.resTys.head? = some (.int 64))
    (data : info.data = .data 152 2 [.data 151 83 [],.values [x,y]])
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) rule_lower_1163 [.inst id]).run (st,tr) = .ok (some env,middle)) :
    SafeMatchReceipt ctx true x y 64 st tr env middle := by
  have hp' := hp
  have original := matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  obtain ⟨j,constant,i,defined,found,literal⟩ := source_literal hp inv rfl source type data args
  have saved : LiteralData ctx y j constant i := ⟨defined,found,literal⟩
  have extraction := ext_inst_data_value ctx st.base source
  rw [type,data,Option.getD_some] at extraction
  have definition := ext_def_inst_some ctx st.base defined
  have constantData := ext_inst_data_value ctx st.base found
  rw [literal] at constantData
  cases hp
  isel_inv [*,rule_lower_1163,sem_extract,sem_unData,sem_eq,sem_prim,sem_ctor,ext_value_array_2,safe_ctor_iff] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals try simp only [source,found,Option.some.injEq] at *
  all_goals subst_vars
  all_goals try simp only [data,literal,V.data.injEq,List.cons.injEq,true_and,and_true] at *
  all_goals isel_destruct <;> subst_vars
  obtain ⟨defined,found,literal⟩ := saved
  obtain ⟨arrayCall⟩ : Nonempty (Backend.externExtract ctx T.value_array_2 (.values [x,y]) st.base = .ok [_,_]) := ⟨by assumption⟩
  rw [ext_value_array_2] at arrayCall
  cases arrayCall
  obtain ⟨definitionCall⟩ : Nonempty (Backend.externExtract ctx T.def_inst (.value y) st.base = .ok [_]) := ⟨by assumption⟩
  rw [ext_def_inst_some ctx st.base defined] at definitionCall
  cases definitionCall
  obtain ⟨constantCall⟩ : Nonempty (Backend.externExtract ctx T.inst_data_value (.inst j) st.base =
    .ok [_,.data 152 35 [.data 151 57 [],_]]) := ⟨by assumption⟩
  rw [ext_inst_data_value ctx st.base found,literal] at constantCall
  simp only [ExtResult.ok.injEq,List.cons.injEq,V.data.injEq,true_and,and_true] at constantCall
  isel_destruct <;> subst_vars
  try simp only [type,Option.getD_some] at *
  obtain ⟨guardCall⟩ : Nonempty (Stock.externCtor ctx T.safe_divisor_from_imm64 [.ty (.int 64),.int i] st =
    .ok (_,_)) := ⟨by assumption⟩
  obtain ⟨safe,output,state⟩ := (safe_ctor_iff ctx _ _ _ _ _).mp guardCall
  subst_vars
  unfold SafeMatchReceipt
  refine ⟨j,_,i,defined,found,literal,?_,?_,?_⟩
  · exact safe
  · rfl
  · rfl
theorem stock_div_safe_narrow_match_observed {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {id x y w : Nat} (width : w ≤ 32) {info : IInfo}
    (source : ctx.insts[id]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 83 [],.values [x,y]])
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+10) rule_lower_1167 [.inst id]).run (st,tr) = .ok (some env,middle)) :
    SafeMatchReceipt ctx false x y w st tr env middle := by
  have hp' := hp
  have original := matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  obtain ⟨j,constant,i,defined,found,literal⟩ := source_literal hp inv rfl source type data args
  have saved : LiteralData ctx y j constant i := ⟨defined,found,literal⟩
  have extraction := ext_inst_data_value ctx st.base source
  rw [type,data,Option.getD_some] at extraction
  have definition := ext_def_inst_some ctx st.base defined
  have constantData := ext_inst_data_value ctx st.base found
  rw [literal] at constantData
  have fits := ext_fits_in_32_ty_fa ctx st.base (.int w)
  simp only [CTy.bits,width,ite_true] at fits
  cases hp
  isel_inv [*,rule_lower_1167,sem_extract,sem_unData,sem_eq,sem_prim,sem_ctor,ext_value_array_2,safe_ctor_iff] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals try simp only [source,found,Option.some.injEq] at *
  all_goals subst_vars
  all_goals try simp only [data,literal,V.data.injEq,List.cons.injEq,true_and,and_true] at *
  all_goals isel_destruct <;> subst_vars
  obtain ⟨defined,found,literal⟩ := saved
  obtain ⟨arrayCall⟩ : Nonempty (Backend.externExtract ctx T.value_array_2 (.values [x,y]) st.base = .ok [_,_]) := ⟨by assumption⟩
  rw [ext_value_array_2] at arrayCall
  cases arrayCall
  obtain ⟨definitionCall⟩ : Nonempty (Backend.externExtract ctx T.def_inst (.value y) st.base = .ok [_]) := ⟨by assumption⟩
  rw [ext_def_inst_some ctx st.base defined] at definitionCall
  cases definitionCall
  obtain ⟨constantCall⟩ : Nonempty (Backend.externExtract ctx T.inst_data_value (.inst j) st.base =
    .ok [_,.data 152 35 [.data 151 57 [],_]]) := ⟨by assumption⟩
  rw [ext_inst_data_value ctx st.base found,literal] at constantCall
  simp only [ExtResult.ok.injEq,List.cons.injEq,V.data.injEq,true_and,and_true] at constantCall
  isel_destruct <;> subst_vars
  try simp only [type,Option.getD_some] at *
  obtain ⟨guardCall⟩ : Nonempty (Stock.externCtor ctx T.safe_divisor_from_imm64 [.ty (.int w),.int i] st =
    .ok (_,_)) := ⟨by assumption⟩
  obtain ⟨safe,output,state⟩ := (safe_ctor_iff ctx _ _ _ _ _).mp guardCall
  subst_vars
  unfold SafeMatchReceipt
  refine ⟨j,_,i,defined,found,literal,?_,?_,?_⟩
  · exact safe
  · rfl
  · rfl
end Backend.Stock.Proof.ScalarDiv

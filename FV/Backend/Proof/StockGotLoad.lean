import FV.Backend.Proof.StockGotCallRhs
namespace Backend.Stock.Proof.GotLoadDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
private theorem sem_i64 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_zero (ctx : Ctx) : (Stock.sem ctx).int 10 0 = .int 0 := by
  unfold Stock.sem Backend.sem normInt Isle.Aarch64.program
  rfl
private theorem stock_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
    (hc : cfg.checkOverlap = false) {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : σ × Array RuleId} {v : V}
    (h : ApplyInternal p sem cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p sem cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p sem cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) ∧ n = n' + 20 := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩

private theorem fresh_call (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.temp_writable_reg [.ty (.int 64)] st =
      .ok (.reg (st.base.fresh .int).1,{st with base := (st.base.fresh .int).2}) := by
  rw [stock_ctor_baseOnly _ _ _ _ (by decide),ctor_temp_writable_reg_i64] <;> rfl
private theorem writable_call (ctx : Ctx) (st : State) (r : V) :
    Stock.externCtor ctx T.writable_reg_to_reg [r] st = .ok (r,st) := by
  rw [stock_ctor_baseOnly _ _ _ _ (by decide),ctor_writable_reg_to_reg] <;> rfl
private theorem emit_shape (ctx : Ctx) (st : State) (i v : V) (next : State) :
    Stock.externCtor ctx T.emit [i] st = .ok (v,next) ↔
      ∃ m,MInst.ofV i = some m ∧ v = .op .unit ∧ next = {st with base := st.base.emit m} := by
  rw [stock_ctor_baseOnly _ _ _ _ (by decide)]
  have legacy : Backend.externCtor ctx T.emit [i] st.base =
      match MInst.ofV i with
      | some m => .ok (.op .unit,st.base.emit m)
      | none => .unmodeled s!"emit of {((i.variant?).map (·.2.1)).getD "?"}" := rfl
  rw [legacy]
  cases found : MInst.ofV i <;> simp [eq_comm]
private theorem pic (ctx : Ctx) (st : State) (v : V) (next : State) :
    Stock.externCtor ctx T.is_pic [] st = .ok (v,next) ↔ v = .bool true ∧ next = st := by
  have actual : Stock.externCtor ctx T.is_pic [] st = .ok (.bool true,st) := rfl
  rw [actual]; simp [eq_comm]
private theorem pic_call (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.is_pic [] st = .ok (.bool true,st) := rfl

private theorem load571 {p : Program} (hp : Data p) {ctx : Ctx} {n : Nat} (enough : 30 ≤ n)
    {name : String} {st next : State} {tr trace : Array RuleId} {value : V}
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 571 [.op (.extName name)] (st,tr) value (next,trace)) :
    value = .reg (st.base.fresh .int).1 ∧
      next = {st with base := (st.base.fresh .int).2.emit (.loadExtNameGot (st.base.fresh .int).1 name)} := by
  obtain ⟨_,_,_,hL,hpre,_,_,_,_,_,_,hm,he,stateEq,fuelEq⟩ :=
    stock_internal_split_first rfl hp.t571 term_571_kind rfl (by rw [hp.r571]; simp; omega) run
  rcases Prod.mk.inj stateEq with ⟨rfl,rfl⟩
  cases fuelEq
  rw [hp.r571] at hL
  isel_rule_cases hL
  cases hp
  isel_inv [*,rule_inst_4002,sem_ctor,sem_mkData,sem_unData,sem_i64,fresh_call,writable_call,emit_shape] at hm he
  isel_destruct
  simp only [fresh_call,writable_call,emit_shape,ExtResult.ok.injEq,Prod.mk.injEq] at *
  isel_destruct
  subst_vars
  have convert := ‹MInst.ofV _ = some _›
  rw [ofV_loadExtNameGot_ctl] at convert
  cases convert
  constructor <;> rfl

/-- The real zero-offset external-name helper allocates one fresh GOT target
and emits its actual load, preserving every Stock scheduling field. -/
theorem stock_load_ext_name_got {p : Program} (hp : Data p) {ctx : Ctx} {n : Nat} (enough : 40 ≤ n)
    {name : String} {distance : V} {st next : State} {tr trace : Array RuleId} {value : V}
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 570 [.op (.extName name),.int 0,distance]
      (st,tr) value (next,trace)) :
    value = .reg (st.base.fresh .int).1 ∧
      next = {st with base := (st.base.fresh .int).2.emit (.loadExtNameGot (st.base.fresh .int).1 name)} := by
  obtain ⟨_,_,_,hL,hpre,_,_,_,_,_,_,hm,he,stateEq,fuelEq⟩ :=
    stock_internal_split_first rfl hp.t570 term_570_kind rfl (by rw [hp.r570]; simp; omega) run
  rcases Prod.mk.inj stateEq with ⟨rfl,rfl⟩
  cases fuelEq
  rw [hp.r570] at hL
  isel_rule_cases hL
  have savedData := hp
  all_goals cases hp
  · isel_inv [*,rule_inst_3986,sem_ctor,sem_eq,sem_bool,sem_zero,pic] at hm he
    isel_destruct
    simp only [pic,ExtResult.ok.injEq,Prod.mk.injEq] at *
    isel_destruct
    subst_vars
    have got := ‹ApplyInternal _ _ _ _ 27 571 _ _ _ _›
    apply load571 savedData (run := got)
    omega
  · isel_inv [*,rule_inst_3991,sem_ctor,sem_eq,sem_bool,pic] at hm
    simp only [pic] at *
    isel_destruct
    cases ‹V.bool false = V.bool true›
  · isel_inv [*,rule_inst_3996,sem_ctor,sem_eq,sem_bool,pic] at hm
    simp only [pic] at *
    isel_destruct
    cases ‹V.bool false = V.bool true›
  · obtain ⟨fuel,after,failed⟩ := hpre _ (List.mem_cons_self ..)
    revert failed
    isel_eval [*,rule_inst_3986,sem_ctor,sem_eq,sem_bool,sem_zero,pic_call]
    simp
end Backend.Stock.Proof.GotLoadDraft

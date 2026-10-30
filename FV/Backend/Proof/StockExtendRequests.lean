import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockShiftHelper
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem sem_prim_type (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
private theorem sem_int (ctx : Ctx) (ty : TypeId) (i : Int) :
    (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
section IntConstants
attribute [local semireducible] Isle.Aarch64.program
private theorem int32 (ctx : Ctx) : (Stock.sem ctx).int 1 32 = .int 32 := rfl
private theorem int64 (ctx : Ctx) : (Stock.sem ctx).int 1 64 = .int 64 := rfl
end IntConstants
private theorem ty_bits (ctx : Ctx) (st : State) (ty : CTy) :
    Stock.externCtor ctx T.ty_bits [.ty ty] st = .ok (.int ty.bits,st) := by
  rw [stock_ctor_baseOnly ctx T.ty_bits _ st (by decide)]
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

open Lean in
/-- `isel_split hp hc h t`: split the internal call `h : ApplyInternal … t …` into one goal per
rule of term `t`, with hypotheses `hm` (the match), `he` (the right-hand side) and `hpre`
(the earlier rules failed), after `cases hp` (data facts in context). -/
macro "stock_split " hp:ident hc:ident h:ident t:num : tactic => do
  let tN := mkIdent (hp.getId ++ Name.mkSimple s!"t{t.getNat}")
  let rN := mkIdent (hp.getId ++ Name.mkSimple s!"r{t.getNat}")
  let kN := mkIdent (Name.mkStr `Backend.Proof s!"term_{t.getNat}_kind")
  let hm := mkIdent `hm
  let he := mkIdent `he
  let hpre := mkIdent `hpre
  let hL := mkIdent `hL
  `(tactic| (
    obtain ⟨_, _, _, $hL, $hpre, _, _, _, _, _, _, $hm, $he, rfl, rfl⟩ := stock_internal_split_first $hc $tN $kN rfl (by rw [$rN:ident]; simp; omega) $h
    rw [$rN:ident] at $hL:ident
    isel_rule_cases $hL
    all_goals cases $hp:ident))

private theorem extend_internal_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} (enough : 19 ≤ n)
    {s s' : State × Array RuleId} {rx : Reg} {sg : Bool} {fb tb : Nat} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 417 [.reg rx,.bool sg,.int fb,.int tb] s v s') :
    v = .reg (s.1.base.fresh .int).1 ∧
      s'.1 = {s.1 with base := (s.1.base.fresh .int).2.emit (.extend (s.1.base.fresh .int).1 rx sg fb tb)} := by
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,n+1 = fuel+20 := ⟨n-19,by omega⟩
  unfold ApplyInternal at h
  rw [fuelEq] at h
  exact stock_extend_helper_observed hp ctx hc h

def MappedExtOut (ctx : Ctx) (x : Nat) (sg : Bool) (toB : Nat) (pass : List CTy)
    (st next : State) (out : V) : Prop :=
  ∃ t,ctx.valueType? x = some t ∧ DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx ∧
    ((t ∈ pass ∧ out = .reg rx ∧ next = st.mark x) ∨
      (t ∉ pass ∧ t.bits ≤ 32 ∧ out = .reg (st.base.fresh .int).1 ∧
        next = {st.mark x with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx sg t.bits toB)}))

/-- Successful actual zero-extension helper calls supply the source type,
guarded request and complete pass-through/extension state internally. -/
theorem stock_zext32_out {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {n x : Nat} (enough : 60 ≤ n)
    {s s' : State × Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 556 [.value x] s v s') :
    MappedExtOut ctx x false 32 [.int 32,.int 64] s.1 s'.1 v := by
  obtain ⟨start,tr⟩ := s
  obtain ⟨finish,trace⟩ := s'
  have hp' := hp
  stock_split hp hc h 556
  · isel_inv [*,rule_inst_3813,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff] at hm he
    all_goals simp only [stock_put_in_reg_iff,sem_prim_type,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    exact ⟨_,‹_›,‹_›,_,‹_›,.inl ⟨by simp,rfl,rfl⟩⟩
  · isel_inv [*,rule_inst_3814,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff] at hm he
    all_goals simp only [stock_put_in_reg_iff,sem_prim_type,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    exact ⟨_,‹_›,‹_›,_,‹_›,.inl ⟨by simp,rfl,rfl⟩⟩
  · isel_inv [*,rule_inst_3809,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff,ty_bits] at hm he
    all_goals simp only [stock_put_in_reg_iff,sem_prim_type,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    rename_i t hT hb safe rx hx hext
    have ext := extend_internal_observed hp' ctx hc (by omega) hext
    have h32 : t ≠ .int 32 := by
      intro equal; subst t
      obtain ⟨k,s2,failed⟩ := hpre _ (List.mem_cons_self ..)
      revert failed
      isel_eval [*,rule_inst_3813,sem_extract,sem_eq,sem_prim_type,ext_value_type ctx _ hT]
      simp
    refine ⟨t,hT,safe,rx,hx,.inr ⟨?_,hb,ext.1,ext.2⟩⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨h32,fun equal => by subst t; exact absurd hb (by decide)⟩
/-- Successful actual sign-extension helper calls supply the source type,
guarded request and complete pass-through/extension state internally. -/
theorem stock_sext32_out {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {n x : Nat} (enough : 60 ≤ n)
    {s s' : State × Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 555 [.value x] s v s') :
    MappedExtOut ctx x true 32 [.int 32,.int 64] s.1 s'.1 v := by
  obtain ⟨start,tr⟩ := s
  obtain ⟨finish,trace⟩ := s'
  have hp' := hp
  stock_split hp hc h 555
  · isel_inv [*,rule_inst_3803,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff] at hm he
    all_goals simp only [stock_put_in_reg_iff,sem_prim_type,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    exact ⟨_,‹_›,‹_›,_,‹_›,.inl ⟨by simp,rfl,rfl⟩⟩
  · isel_inv [*,rule_inst_3804,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff] at hm he
    all_goals simp only [stock_put_in_reg_iff,sem_prim_type,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    exact ⟨_,‹_›,‹_›,_,‹_›,.inl ⟨by simp,rfl,rfl⟩⟩
  · isel_inv [*,rule_inst_3799,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff,ty_bits] at hm he
    all_goals simp only [stock_put_in_reg_iff,sem_prim_type,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    rename_i t hT hb safe rx hx hext
    have ext := extend_internal_observed hp' ctx hc (by omega) hext
    have h32 : t ≠ .int 32 := by
      intro equal; subst t
      obtain ⟨k,s2,failed⟩ := hpre _ (List.mem_cons_self ..)
      revert failed
      isel_eval [*,rule_inst_3803,sem_extract,sem_eq,sem_prim_type,ext_value_type ctx _ hT]
      simp
    refine ⟨t,hT,safe,rx,hx,.inr ⟨?_,hb,ext.1,ext.2⟩⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨h32,fun equal => by subst t; exact absurd hb (by decide)⟩
/-- Successful actual64-bit extension helpers derive their type, guarded
source request and complete pass-through/extension state from execution. -/
theorem stock_zext64_out {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {n x : Nat} (enough : 60 ≤ n)
    {s s' : State × Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 558 [.value x] s v s') :
    MappedExtOut ctx x false 64 [.int 64] s.1 s'.1 v := by
  obtain ⟨start,tr⟩ := s
  obtain ⟨finish,trace⟩ := s'
  have hp' := hp
  stock_split hp hc h 558
  · isel_inv [*,rule_inst_3829,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff,ty_bits] at hm he
    all_goals simp only [stock_put_in_reg_iff,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    rename_i t hT hb safe rx hx hext
    have ext := extend_internal_observed hp' ctx hc (by omega) hext
    refine ⟨t,hT,safe,rx,hx,.inr ⟨?_,hb,ext.1,ext.2⟩⟩
    simp only [List.mem_singleton]
    intro equal; subst t; exact absurd hb (by decide)
  · isel_inv [*,rule_inst_3833,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff] at hm he
    all_goals simp only [stock_put_in_reg_iff] at *
    all_goals isel_destruct <;> subst_vars
    exact ⟨_,‹_›,‹_›,_,‹_›,.inl ⟨by simp,rfl,rfl⟩⟩

/-- Successful actual64-bit extension helpers derive their type, guarded
source request and complete pass-through/extension state from execution. -/
theorem stock_sext64_out {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {n x : Nat} (enough : 60 ≤ n)
    {s s' : State × Array RuleId} {v : V}
    (h : ApplyInternal p (Stock.sem ctx) cfg n 27 557 [.value x] s v s') :
    MappedExtOut ctx x true 64 [.int 64] s.1 s'.1 v := by
  obtain ⟨start,tr⟩ := s
  obtain ⟨finish,trace⟩ := s'
  have hp' := hp
  stock_split hp hc h 557
  · isel_inv [*,rule_inst_3819,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff,ty_bits] at hm he
    all_goals simp only [stock_put_in_reg_iff,ty_bits,sem_bool,int32,int64,ExtResult.ok.injEq,Prod.mk.injEq,V.int.injEq] at *
    all_goals isel_destruct <;> subst_vars
    rename_i t hT hb safe rx hx hext
    have ext := extend_internal_observed hp' ctx hc (by omega) hext
    refine ⟨t,hT,safe,rx,hx,.inr ⟨?_,hb,ext.1,ext.2⟩⟩
    simp only [List.mem_singleton]
    intro equal; subst t; exact absurd hb (by decide)
  · isel_inv [*,rule_inst_3823,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim_type,stock_put_in_reg_iff] at hm he
    all_goals simp only [stock_put_in_reg_iff] at *
    all_goals isel_destruct <;> subst_vars
    exact ⟨_,‹_›,‹_›,_,‹_›,.inl ⟨by simp,rfl,rfl⟩⟩

end Backend.Stock.Proof.ScalarShift

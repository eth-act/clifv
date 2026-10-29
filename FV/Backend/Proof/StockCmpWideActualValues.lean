module

public import FV.Backend.Proof.StockCmpMatchedPredecessor
public import FV.Backend.Proof.StockCmpNarrowMatchedValues
public import FV.Backend.Proof.StockCmpImmediateSourceValues
public import FV.Backend.Proof.StockCmpRegisterTraceValues
public import FV.Backend.Proof.StockCmpPredecessorSignedSourceValues
public import FV.Backend.Proof.StockCmpPredecessorUnsignedSourceValues
public import FV.Backend.Proof.StockCmpZero32OriginalRhsValues
public import FV.Backend.Proof.StockCmpZero64OriginalRhsValues

@[expose] public section

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
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem base_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem wide_incompatible {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (wide : Bool)
    {x y : Nat} (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : ctx.valueType? y = some (.int (if wide then 64 else 32))) {r : Rule}
    (member : r ∈ [rule_inst_5142,rule_inst_5134,rule_inst_5117,rule_inst_5108])
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) r
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  have tx := ext_value_type ctx st.base typeX
  have ty := ext_value_type ctx st.base typeY
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals cases hp
  all_goals cases wide
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_inv [*,rule_inst_5142,rule_inst_5134,rule_inst_5117,rule_inst_5108,
    sem_extract,sem_unData,sem_eq,sem_prim,sem_ctor,base_eq,base_prim,ccIdx,CTy.ofName?] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals simp only [typeX,typeY,Option.some.injEq,reduceCtorEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals simp [CTy.bits,CTy.ofName?,ext_fits_in_16_iff] at *
private theorem cmp_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
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

private def WideType (ty : Clif.Ty) (wide : Bool) : Prop := ty = if wide then .i64 else .i32
private theorem save_type {ty : Clif.Ty} {wide : Bool} (h : ty = if wide then .i64 else .i32) : WideType ty wide := h
private theorem wide_type_elim {ty : Clif.Ty} {wide : Bool} (h : WideType ty wide) : ty = if wide then .i64 else .i32 := h
attribute [local irreducible] WideType
private theorem constant_zero {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} {x j : Nat} {info : IInfo} {literal : Int}
    {u : BitVec ty.width} (get : fr.getAs x ty = .ok u)
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int literal]) (normalized : u64 literal = 0)
    (width : ty.width ≤ 64) : u = 0 := by
  have constant := (ScalarDiv.stock_div_constant_source_value inv dfg get defined found data).2
  have actual : u64 literal = u.toNat := by
    rw [constant]
    exact u64_imm64OfIconst width u
  apply BitVec.eq_of_toNat_eq
  exact actual.symm.trans normalized
set_option backward.dsimp.instances true in
private theorem zero_rhs_execution {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (wide left nonzero : Bool) {ty : Clif.Ty} (sourceTy : ty = if wide then .i64 else .i32)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y j : Nat} {info : IInfo} {literal : Int}
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (defined : ctx.defInst? (if left then x else y) = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int literal]) (normalized : u64 literal = 0)
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enough : 119 ≤ fuel)
    (rhs : (evalExpr program (Stock.sem ctx) {} (n+240) (cmpZeroRule left nonzero).rhs
      #[some (.value (if left then y else x))]).run (st,tr) = .ok (some condition,middle,emitTrace))
    (conditionCall : ApplyInternal program (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    CmpExecution F isem aliases (if nonzero then .ne else .eq) ty u v st next out ρ := by
  subst ty
  cases wide <;> cases left <;> cases nonzero
  all_goals dsimp only [cmpZeroRule,Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false] at *
  case false.false.false =>
    have zeroValue : v = 0 := constant_zero inv dfg getY defined found data normalized (by decide)
    subst v
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero32_original_eq_rhs_values inv getX typeX enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u == (0#32))⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
  case false.false.true =>
    have zeroValue : v = 0 := constant_zero inv dfg getY defined found data normalized (by decide)
    subst v
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero32_original_ne_rhs_values inv getX typeX enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u != (0#32))⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
  case false.true.false =>
    have zeroValue : u = 0 := constant_zero inv dfg getX defined found data normalized (by decide)
    subst u
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero32_original_eq_rhs_values inv getY typeY enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#32) == v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#32) == v) = (v == (0#32)) := Bool.beq_comm
    try simp only [bne] at execution ⊢
    rw [commute]
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
  case false.true.true =>
    have zeroValue : u = 0 := constant_zero inv dfg getX defined found data normalized (by decide)
    subst u
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero32_original_ne_rhs_values inv getY typeY enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#32) != v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#32) == v) = (v == (0#32)) := Bool.beq_comm
    try simp only [bne] at execution ⊢
    rw [commute]
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
  case true.false.false =>
    have zeroValue : v = 0 := constant_zero inv dfg getY defined found data normalized (by decide)
    subst v
    have rhs' : (evalExpr program (Stock.sem ctx) {} ((n+20)+220) (cmpZeroRule false false).rhs
        #[some (.value x)]).run (st,tr) = .ok (some condition,middle,emitTrace) := by
      simpa only [cmpZeroRule,Nat.add_assoc,show 20+220=240 from rfl,Bool.false_eq_true,ite_true,ite_false] using rhs
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero64_original_eq_rhs_values inv getX typeX enough rhs' conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u == (0#64))⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
  case true.false.true =>
    have zeroValue : v = 0 := constant_zero inv dfg getY defined found data normalized (by decide)
    subst v
    have rhs' : (evalExpr program (Stock.sem ctx) {} ((n+20)+220) (cmpZeroRule false true).rhs
        #[some (.value x)]).run (st,tr) = .ok (some condition,middle,emitTrace) := by
      simpa only [cmpZeroRule,Nat.add_assoc,show 20+220=240 from rfl,Bool.false_eq_true,ite_true,ite_false] using rhs
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero64_original_ne_rhs_values inv getX typeX enough rhs' conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u != (0#64))⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
  case true.true.false =>
    have zeroValue : u = 0 := constant_zero inv dfg getX defined found data normalized (by decide)
    subst u
    have rhs' : (evalExpr program (Stock.sem ctx) {} ((n+20)+220) (cmpZeroRule true false).rhs
        #[some (.value y)]).run (st,tr) = .ok (some condition,middle,emitTrace) := by
      simpa only [cmpZeroRule,Nat.add_assoc,show 20+220=240 from rfl,Bool.false_eq_true,ite_true,ite_false] using rhs
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero64_original_eq_rhs_values inv getY typeY enough rhs' conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#64) == v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#64) == v) = (v == (0#64)) := Bool.beq_comm
    try simp only [bne] at execution ⊢
    rw [commute]
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
  case true.true.true =>
    have zeroValue : u = 0 := constant_zero inv dfg getX defined found data normalized (by decide)
    subst u
    have rhs' : (evalExpr program (Stock.sem ctx) {} ((n+20)+220) (cmpZeroRule true true).rhs
        #[some (.value y)]).run (st,tr) = .ok (some condition,middle,emitTrace) := by
      simpa only [cmpZeroRule,Nat.add_assoc,show 20+220=240 from rfl,Bool.false_eq_true,ite_true,ite_false] using rhs
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero64_original_ne_rhs_values inv getY typeY enough rhs' conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#64) != v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#64) == v) = (v == (0#64)) := Bool.beq_comm
    try simp only [bne] at execution ⊢
    rw [commute]
    apply (execution world).imp
    intro ρ' world' valid result
    rcases result with ⟨value,kept⟩
    constructor
    · simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using value
    · intro k outside
      exact kept k (by omega)
/-- Every successful actual32/64 comparison emitter and condition call computes
its original source predicate, without operand classifications or caller RHS
certificates. The actual twelve-rule split covers zero on either side, ordinary
and adjusted immediates, and register comparisons. -/
theorem stock_cmp_wide_actual_emitter_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (wide : Bool) (cc : Clif.IntCC)
    {ty : Clif.Ty} (sourceTy : ty = if wide then .i64 else .i32)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : ctx.valueType? y = some (.int (if wide then 64 else 32)))
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 300 ≤ emitFuel) (enough : 119 ≤ fuel)
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) condition (middle,emitTrace))
    (conditionCall : ApplyInternal program (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    CmpExecution F isem aliases cc ty u v st next out ρ := by
  have savedType := save_type sourceTy
  clear sourceTy
  have hp := data_program
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  obtain ⟨pre,r,post,hL,hpre,matchN,rhsN,env,afterMatch,emittedState,rhsTrace,hm,he,stateEq,fuelEq⟩ :=
    cmp_internal_split_first hc hp.t652 term_652_kind rfl (by rw [hp.r652]; simp; omega) emitter
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj stateEq
  subst emitFuel
  rw [hp.r652] at hL
  isel_rule_cases hL
  all_goals cases hp
  all_goals simp only [Prod.mk.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals have sourceTy := wide_type_elim savedType
  case inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv true false cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv wide true false sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv true true cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv wide true true sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inr.inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv false false cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv wide false false sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inr.inr.inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv false true cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv wide false true sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inl.mk =>
    have bits : (szOf ty.width).bits = ty.width := by rw [sourceTy]; cases wide <;> rfl
    have width : ty.width = 32 ∨ ty.width = 64 := by rw [sourceTy]; cases wide <;> simp [Clif.Ty.width]
    obtain ⟨j,info,literal,imm,defined,found,data,encoded,_,envEq,afterEq⟩ :=
      stock_cmp_immediate_match_observed hp' ctx inv false cc ty x y (by cases wide <;> simpa only [sourceTy,Bool.false_eq_true,ite_true,ite_false,Clif.Ty.width] using typeX) hm
    rw [envEq,afterEq,← bits] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨nx,d,mapped,output,lower,upper,fragment,execution⟩ :=
      stock_cmp_immediate_condition_source_values hp' inv cc width dfg getX getY
        defined found data encoded enough he conditionCall refines bounded extent held
    unfold CmpExecution
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    exact (execution world).imp (fun ρ' _ _ result => ⟨result.1,fun k outside => result.2 k (by omega)⟩)
  case inr.inr.inr.inr.inr.inl.mk =>
    have bits : (szOf ty.width).bits = if wide then 64 else 32 := by rw [sourceTy]; cases wide <;> rfl
    have width : ty.width = 32 ∨ ty.width = 64 := by rw [sourceTy]; cases wide <;> simp [Clif.Ty.width]
    obtain ⟨j,info,literal,imm,ccEq,defined,found,data,odd,encoded,envEq,afterEq⟩ :=
      stock_cmp_predecessor_match_observed hp' ctx inv false cc (szOf ty.width) x y (by simpa only [bits] using typeX) hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_predecessor_unsigned_rhs_observed hp' ctx rfl (szOf ty.width) he
    have raw := stock_cmp_predecessor_unsigned_rhs hp' ctx (cfg := {}) rfl (szOf ty.width) st tr m x literal rx imm mapped safe
    rw [← producer,← finish] at raw
    obtain ⟨nx,d,mapX,output,lower,upper,fragment,execution⟩ :=
      stock_cmp_predecessor_unsigned_condition_source_values hp' inv width dfg getX getY defined found data encoded odd enough
        raw conditionCall refines bounded extent held
    unfold CmpExecution
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    exact (execution world).imp (fun ρ' _ _ result => ⟨result.1,fun k outside => result.2 k (by omega)⟩)
  case inr.inr.inr.inr.inr.inr.inl.mk =>
    have bits : (szOf ty.width).bits = if wide then 64 else 32 := by rw [sourceTy]; cases wide <;> rfl
    have width : ty.width = 32 ∨ ty.width = 64 := by rw [sourceTy]; cases wide <;> simp [Clif.Ty.width]
    obtain ⟨j,info,literal,imm,ccEq,defined,found,data,odd,encoded,envEq,afterEq⟩ :=
      stock_cmp_predecessor_match_observed hp' ctx inv true cc (szOf ty.width) x y (by simpa only [bits] using typeX) hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_predecessor_signed_rhs_observed hp' ctx rfl (szOf ty.width) he
    have raw := stock_cmp_predecessor_signed_rhs hp' ctx (cfg := {}) rfl (szOf ty.width) st tr m x literal rx imm mapped safe
    rw [← producer,← finish] at raw
    obtain ⟨nx,d,mapX,output,lower,upper,fragment,execution⟩ :=
      stock_cmp_predecessor_signed_condition_source_values hp' inv width dfg getX getY defined found data encoded odd enough
        raw conditionCall refines bounded extent held
    unfold CmpExecution
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    exact (execution world).imp (fun ρ' _ _ result => ⟨result.1,fun k outside => result.2 k (by omega)⟩)
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    have bits : (szOf ty.width).bits = if wide then 64 else 32 := by rw [sourceTy]; cases wide <;> rfl
    have width : ty.width = 32 ∨ ty.width = 64 := by rw [sourceTy]; cases wide <;> simp [Clif.Ty.width]
    obtain ⟨envEq,afterEq⟩ := stock_cmp_wide_match_observed hp' ctx cc (szOf ty.width) (by simpa only [bits] using typeY) hm
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ :=
      stock_cmp_register_condition_source_values_any_trace hp' inv cc width getX getY enough he conditionCall refines bounded extent held
    unfold CmpExecution
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    exact (execution world).imp (fun ρ' _ _ result => ⟨result.1,fun k outside => result.2 k (by omega)⟩)
end Backend.Stock.Proof.ScalarCmp

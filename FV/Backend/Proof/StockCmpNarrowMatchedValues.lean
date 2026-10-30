import FV.Backend.Proof.StockCmpMatchedZero
import FV.Backend.Proof.StockCmpMatchedRegister
import FV.Backend.Proof.StockCmpMatchedImmediate
import FV.Backend.Proof.StockCmpNarrowImmediateSourceValues
import FV.Backend.Proof.StockCmpNarrowSourceValues
import FV.Backend.Proof.StockCmpZero8OriginalRhsValues
import FV.Backend.Proof.StockCmpZero16OriginalRhsValues
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
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem base_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem narrow128_failure {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5142
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have not128 : (V.ty (.int (if half then 16 else 8)) == V.ty (.int 128)) = false := by cases half <;> decide
  cases hp
  cases half
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*, isel_monad,rule_inst_5142,sem_extract,sem_unData,sem_eq,sem_prim,
    stock_matchArgs,base_eq,base_prim,CTy.ofName?]
private theorem narrow_scalar_failure {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? x = some (.int (if half then 16 else 8))) {r : Rule}
    (member : r ∈ [rule_inst_5165,rule_inst_5155,rule_inst_5160])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) r [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have absent : externExtract ctx T.ty_32_or_64 (.ty (.int (if half then 16 else 8))) st.base = .fail := by cases half <;> rfl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have hp' := hp
  rcases member with rfl | rfl | rfl
  all_goals cases cc <;> cases half
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*, isel_monad,hp'.t2,hp'.t120,hp'.t2276,hp'.t2272,rule_inst_5165,rule_inst_5155,rule_inst_5160,sem_extract,sem_unData,
    sem_eq,sem_prim,stock_matchArgs,base_eq,base_prim,CTy.ofName?,ccIdx]
  all_goals rfl
private theorem narrow_wide_absurd {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y m : Nat} (typed : ctx.valueType? x = some (.int (if half then 16 else 8))) {r : Rule}
    (member : r ∈ [rule_inst_5165,rule_inst_5155,rule_inst_5160,rule_inst_5142])
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) r
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals first
    | (rw [narrow128_failure hp ctx cc half typed st tr m] at matched; cases matched)
    | (rw [narrow_scalar_failure hp ctx cc half typed (by decide +kernel) st tr m] at matched; cases matched)
private theorem wide_failure {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8))) (wide128 : Bool)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if wide128 then rule_inst_5142 else rule_inst_5128)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have xTy := ext_value_type ctx st.base typeX
  have yTy := ext_value_type ctx st.base typeY
  have notWide : externExtract ctx T.ty_32_or_64 (.ty (.int (if half then 16 else 8))) st.base = .fail := by cases half <;> rfl
  have not128 : (V.ty (.int (if half then 16 else 8)) == V.ty (.int 128)) = false := by cases half <;> decide
  cases hp
  cases wide128 <;> cases half
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*, isel_monad,rule_inst_5142,rule_inst_5128,sem_extract,sem_unData,sem_eq,sem_prim,
    stock_matchArgs,base_eq,base_prim,CTy.ofName?]
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

private def NarrowType (ty : Clif.Ty) (half : Bool) : Prop := ty = if half then .i16 else .i8
private theorem save_type {ty : Clif.Ty} {half : Bool} (h : ty = if half then .i16 else .i8) : NarrowType ty half := h
private theorem narrow_type_elim {ty : Clif.Ty} {half : Bool} (h : NarrowType ty half) : ty = if half then .i16 else .i8 := h
attribute [local irreducible] NarrowType
def CmpExecution (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (aliases : Array (Option Nat))
    (cc : Clif.IntCC) (ty : Clif.Ty) (u v : BitVec ty.width)
    (st next : State) (out : V) (ρ : Nat → CV) : Prop :=
  ∃ d code,out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
    Frag st.base next.base code ∧
    ∀ world,Runs F isem (code.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧
        ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
attribute [local irreducible] CmpExecution
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
    (half left nonzero : Bool) {ty : Clif.Ty} (sourceTy : ty = if half then .i16 else .i8)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y j : Nat} {info : IInfo} {literal : Int}
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
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
  cases half <;> cases left <;> cases nonzero
  all_goals dsimp only [cmpZeroRule,Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false] at *
  case false.false.false =>
    have zeroValue : v = 0 := constant_zero inv dfg getY defined found data normalized (by decide)
    subst v
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero8_original_eq_rhs_values inv getX typeX enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u == (0#8))⟩ (ρ' d) ∧
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
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero8_original_ne_rhs_values inv getX typeX enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u != (0#8))⟩ (ρ' d) ∧
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
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero8_original_eq_rhs_values inv getY typeY enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#8) == v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#8) == v) = (v == (0#8)) := Bool.beq_comm
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
    obtain ⟨key,d,mapped,output,lower,upper,fragment,execution⟩ := stock_cmp_zero8_original_ne_rhs_values inv getY typeY enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#8) != v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#8) == v) = (v == (0#8)) := Bool.beq_comm
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
    obtain ⟨ms,r,d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero16_original_eq_rhs_values inv dfg getX typeX enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u == (0#16))⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using execution world
  case true.false.true =>
    have zeroValue : v = 0 := constant_zero inv dfg getY defined found data normalized (by decide)
    subst v
    obtain ⟨ms,r,d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero16_original_ne_rhs_values inv dfg getX typeX enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (u != (0#16))⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using execution world
  case true.true.false =>
    have zeroValue : u = 0 := constant_zero inv dfg getX defined found data normalized (by decide)
    subst u
    obtain ⟨ms,r,d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero16_original_eq_rhs_values inv dfg getY typeY enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#16) == v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#16) == v) = (v == (0#16)) := Bool.beq_comm
    try simp only [bne] at execution ⊢
    rw [commute]
    simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using execution world
  case true.true.true =>
    have zeroValue : u = 0 := constant_zero inv dfg getX defined found data normalized (by decide)
    subst u
    obtain ⟨ms,r,d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero16_original_ne_rhs_values inv dfg getY typeY enough rhs conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨d,_,output,lower,upper,fragment,?_⟩
    intro world
    change Runs F isem _ ρ world (fun ρ' _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 ((0#16) != v)⟩ (ρ' d) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k)
    have commute : ((0#16) == v) = (v == (0#16)) := Bool.beq_comm
    try simp only [bne] at execution ⊢
    rw [commute]
    simpa [Clif.Ty.width,Clif.Sem.intcc,bne,Bool.beq_comm] using execution world
/-- Source values for every successful actual narrow comparison emitter,
including constants on either side. Caller classifications and RHS certificates
are unnecessary. Scratch separation remains an internal retained-record obligation. -/
theorem stock_cmp_narrow_actual_emitter_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (half : Bool) (cc : Clif.IntCC)
    {ty : Clif.Ty} (sourceTy : ty = if half then .i16 else .i8)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 300 ≤ emitFuel) (enough : 119 ≤ fuel)
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) condition (middle,emitTrace))
    (conditionCall : ApplyInternal program (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedY : ∀ r,ctx.valueReg? y = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg) :
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
  all_goals have sourceTy := narrow_type_elim savedType
  case inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv true false cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv half true false sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv true true cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv half true true sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inr.inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv false false cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv half false false sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inr.inr.inl.mk =>
    obtain ⟨j,info,literal,ccEq,defined,found,data,normalized,envEq,afterEq⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv false true cc x y hm
    subst cc
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact zero_rhs_execution inv half false true sourceTy dfg getX getY typeX typeY
      defined found data normalized enough he conditionCall refines bounded extent held
  case inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    obtain ⟨j,info,literal,imm,defined,found,data,encoded,unsigned,envEq,afterEq⟩ :=
      stock_cmp_immediate_match_observed hp' ctx inv true cc ty x y (by cases half <;> simpa only [sourceTy,Bool.false_eq_true,ite_true,ite_false,Clif.Ty.width] using typeX) hm
    rw [envEq,afterEq] at he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+160 := ⟨rhsN+20-160,by omega⟩
    rw [gas] at he
    obtain ⟨nx,d,mapped,output,lower,upper,fragment,execution⟩ :=
      stock_cmp_narrow_immediate_condition_source_values hp' inv half cc sourceTy (unsigned rfl) dfg getX getY
        defined found data encoded typeX enough he conditionCall refines bounded extent held
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    exact ⟨d,_,output,lower,upper,fragment,execution⟩
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    have failure := wide_failure hp' ctx cc half typeX typeY false st tr matchN
    simp only [Bool.false_eq_true,ite_false] at failure
    rw [failure] at hm
    cases hm
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    obtain ⟨signed,envEq,afterEq⟩ := stock_cmp_narrow_match_observed hp' ctx cc half false typeY hm
    rw [envEq,afterEq] at he
    have rhs : (evalExpr program (Stock.sem ctx) {} (rhsN+20)
        (if signedCC cc then rule_inst_5108 else rule_inst_5117).rhs
        #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)]).run
        (st,tr) = .ok (some condition,middle,rhsTrace) := by simpa only [signed,Bool.false_eq_true,ite_true,ite_false] using he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+160 := ⟨rhsN+20-160,by omega⟩
    rw [gas] at rhs
    obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ :=
      stock_cmp_narrow_condition_source_values hp' inv half cc sourceTy getX getY typeX enough
        rhs conditionCall refines bounded extent held separatedY
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    exact ⟨d,_,output,lower,upper,fragment,execution⟩
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.mk =>
    obtain ⟨signed,envEq,afterEq⟩ := stock_cmp_narrow_match_observed hp' ctx cc half true typeY hm
    rw [envEq,afterEq] at he
    have rhs : (evalExpr program (Stock.sem ctx) {} (rhsN+20)
        (if signedCC cc then rule_inst_5108 else rule_inst_5117).rhs
        #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)]).run
        (st,tr) = .ok (some condition,middle,rhsTrace) := by simpa only [signed,Bool.false_eq_true,ite_true,ite_false] using he
    obtain ⟨m,gas⟩ : ∃ m,rhsN+20=m+160 := ⟨rhsN+20-160,by omega⟩
    rw [gas] at rhs
    obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ :=
      stock_cmp_narrow_condition_source_values hp' inv half cc sourceTy getX getY typeX enough
        rhs conditionCall refines bounded extent held separatedY
    unfold CmpExecution
    dsimp only [Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false]
    exact ⟨d,_,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp

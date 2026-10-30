import FV.Backend.Proof.StockCmpNonconstantSelection
import FV.Backend.Proof.StockCmpConstantLeftFailures
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
private def narrowRule (cc : Clif.IntCC) : Rule := if signedCC cc then rule_inst_5108 else rule_inst_5117
private def narrowEnv (cc : Clif.IntCC) (half : Bool) (x y : Nat) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 1 (some (.value x))).setIfInBounds 3 (some (.value y))).setIfInBounds 2 (some (.ty (.int (if half then 16 else 8))))
private theorem narrowEnv_eq (cc : Clif.IntCC) (half : Bool) (x y : Nat) :
    narrowEnv cc half x y = #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] := by
  apply Array.toList_inj.mp
  simp [narrowEnv,Array.toList_setIfInBounds,List.set,List.replicate]
private theorem signed_code (ctx : Ctx) (cc : Clif.IntCC) (st : State) :
    Stock.externCtor ctx T.signed_cond_code [.data 145 (ccIdx cc) []] st =
      if signedCC cc then .ok (.data 145 (ccIdx cc) [],st) else .fail := by
  rw [stock_ctor_baseOnly ctx T.signed_cond_code _ st (by decide)]
  cases cc <;> rfl
private theorem unsigned_code (ctx : Ctx) (cc : Clif.IntCC) (st : State) :
    Stock.externCtor ctx T.unsigned_cond_code [.data 145 (ccIdx cc) []] st =
      if signedCC cc then .fail else .ok (.data 145 (ccIdx cc) [],st) := by
  rw [stock_ctor_baseOnly ctx T.unsigned_cond_code _ st (by decide)]
  cases cc <;> rfl
private theorem narrow_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? y = some (.int (if half then 16 else 8)))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (narrowRule cc)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some (narrowEnv cc half x y),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have fits := ext_fits_in_16 ctx st.base (if half then 16 else 8)
  have signed := fun q => signed_code ctx cc q
  have unsigned := fun q => unsigned_code ctx cc q
  cases hp
  cases sign : signedCC cc <;> cases half
  all_goals simp only [narrowRule,sign,ite_true,ite_false,Bool.false_eq_true] at *
  all_goals isel_eval [*, isel_monad,narrowRule,narrowEnv,rule_inst_5108,rule_inst_5117,
    sem_extract,sem_unData,sem_eq,sem_ctor,stock_matchArgs]
private theorem opposite_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? y = some (.int (if half then 16 else 8)))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if signedCC cc then rule_inst_5117 else rule_inst_5108)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have fits := ext_fits_in_16 ctx st.base (if half then 16 else 8)
  have signed := fun q => signed_code ctx cc q
  have unsigned := fun q => unsigned_code ctx cc q
  cases hp
  cases sign : signedCC cc <;> cases half
  all_goals simp only [narrowRule,sign,ite_true,ite_false,Bool.false_eq_true] at *
  all_goals isel_eval [*, isel_monad,rule_inst_5108,rule_inst_5117,
    sem_extract,sem_unData,sem_eq,sem_ctor,stock_matchArgs]
private def Canonical (p : Program) (ctx : Ctx) (r : Rule) (args : List V) (env : Isle.Interp.Env V) : Prop :=
  ∀ st tr n,(matchRule p (Stock.sem ctx) {} (n+20) r args).run (st,tr) = .ok (some env,st,tr)
private def SavedMatch (p : Program) (ctx : Ctx) (fuel : Nat) (r : Rule) (args : List V)
    (start : State × Array RuleId) (env : Isle.Interp.Env V) (finish : State × Array RuleId) : Prop :=
  (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)
private def SavedRhs (p : Program) (ctx : Ctx) (fuel : Nat) (r : Rule) (env : Isle.Interp.Env V)
    (start : State × Array RuleId) (out : V) (finish : State × Array RuleId) : Prop :=
  (evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run start = .ok (some out,finish)
private def Outcome (p : Program) (ctx : Ctx) (r : Rule) (env : Isle.Interp.Env V) (fuel : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run (st,tr) = .ok (some out,next,rhsTrace) ∧
    trace = rhsTrace.push r.id
attribute [local irreducible] Canonical SavedMatch SavedRhs Outcome
private theorem outcome_elim {p : Program} {ctx : Ctx} {r : Rule} {env : Isle.Interp.Env V}
    {fuel : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (h : Outcome p ctx r env fuel st next tr trace out) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run (st,tr) = .ok (some out,next,rhsTrace) ∧
      trace = rhsTrace.push r.id := by
  unfold Outcome at h
  exact h
private theorem save_match {p : Program} {ctx : Ctx} {fuel : Nat} {r : Rule} {args : List V}
    {start finish : State × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)) :
    SavedMatch p ctx fuel r args start env finish := by unfold SavedMatch; exact h
private theorem save_rhs {p : Program} {ctx : Ctx} {fuel : Nat} {r : Rule} {env : Isle.Interp.Env V}
    {start finish : State × Array RuleId} {out : V}
    (h : (evalExpr p (Stock.sem ctx) {} fuel r.rhs env).run start = .ok (some out,finish)) :
    SavedRhs p ctx fuel r env start out finish := by unfold SavedRhs; exact h
private theorem selected {p : Program} {ctx : Ctx} {r : Rule} {args : List V}
    {canonical env : Isle.Interp.Env V} {m fuel : Nat} {st next : State} {tr trace : Array RuleId}
    {after : State × Array RuleId} {out : V} (matchProof : Canonical p ctx r args canonical)
    (matched : SavedMatch p ctx (m+20) r args (st,tr) env after)
    (rhs : SavedRhs p ctx fuel r env after out (next,trace)) :
    Outcome p ctx r canonical fuel st next tr (trace.push r.id) out := by
  unfold Canonical at matchProof
  unfold SavedMatch at matched
  unfold SavedRhs at rhs
  rw [matchProof st tr m] at matched
  have parts := Prod.mk.inj (Except.ok.inj matched)
  have eq := Option.some.inj parts.1
  rw [← eq,← parts.2] at rhs
  unfold Outcome
  exact ⟨trace,rhs,rfl⟩
private theorem rejected_prefix {p : Program} {ctx : Ctx} {r : Rule} {args : List V}
    {env : Isle.Interp.Env V} {st : State} {tr : Array RuleId} {pre : List Rule}
    (matchProof : Canonical p ctx r args env)
    (failed : ∀ r' ∈ pre,∃ n after,(matchRule p (Stock.sem ctx) {} (n+20) r' args).run (st,tr) = .ok (none,after))
    (member : r ∈ pre) : False := by
  obtain ⟨n,after,run⟩ := failed r member
  unfold Canonical at matchProof
  rw [matchProof st tr n] at run
  cases run
private theorem nonconstant_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x j : Nat} {info : IInfo} (notConstant : NonConstantSource ctx x)
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    {value : V} (data : info.data = .data 152 35 [.data 151 57 [],value]) : False := by
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty,c,rfl,fields⟩ := instData_iconst_inv raw
  exact notConstant j info defined found ty c clif
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
private theorem nonconstant_extract {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x : Nat} (notConstant : NonConstantSource ctx x) {st : LState} {node ty payload : V}
    (definition : externExtract ctx T.def_inst (.value x) st = .ok [node])
    (instruction : externExtract ctx T.inst_data_value node st =
      .ok [ty,.data 152 35 [.data 151 57 [],payload]]) : False := by
  obtain ⟨j,info,defined,found,data⟩ := constant_extract definition instruction
  exact nonconstant_data inv notConstant defined found data

private theorem constant_absurd {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) {x y m : Nat}
    (notY : NonConstantSource ctx y) {r : Rule}
    (member : r ∈ [rule_inst_5170,rule_inst_5172,rule_inst_5165,
      rule_inst_5155,rule_inst_5160,rule_inst_5134])
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) r
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  have hp' := hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals isel_inv_simp [hp'.t1,hp'.t2,hp'.t110,hp'.t120,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,
    hp'.t2269,hp'.t2270,hp'.t2276,hp'.t2272,rule_inst_5171,rule_inst_5173,rule_inst_5170,rule_inst_5172,
    rule_inst_5165,rule_inst_5155,rule_inst_5160,rule_inst_5134,sem_extract,sem_unData,sem_eq,stock_matchArgs] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [hp'.t1,hp'.t2,hp'.t110,hp'.t120,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,
    hp'.t2269,hp'.t2270,hp'.t2276,hp'.t2272,rule_inst_5171,rule_inst_5173,rule_inst_5170,rule_inst_5172,
    rule_inst_5165,rule_inst_5155,rule_inst_5160,rule_inst_5134,sem_extract,sem_unData,sem_eq,stock_matchArgs] at *
  all_goals isel_destruct <;> subst_vars
  all_goals exact nonconstant_extract inv notY (by assumption) (by assumption)
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
private theorem left_absurd {p : Program} (hp : Data p) (ctx : Ctx)
    (cc : Clif.IntCC) (nonzeroRule : Bool) {x y j m : Nat} {info : IInfo} {literal : Int}
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int literal]) (nonzero : u64 literal ≠ 0)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) (if nonzeroRule then rule_inst_5173 else rule_inst_5171)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  rw [stock_cmp_constant_left_zero_failure hp ctx nonzeroRule cc defined found data nonzero st tr m] at matched
  cases matched
/-- A successful actual comparison of an original nonzero constant left operand and nonconstant narrow right operand
selects the signed or unsigned extended-register RHS. Matching, rejected
higher-priority alternatives, canonical environment and trace are derived. -/
theorem stock_cmp_narrow_constant_left_emitter_selected {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) (half : Bool) {x y fuel constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (enough : 200 ≤ fuel) (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    (defined : ctx.defInst? x = some constantJ) (found : ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal]) (nonzero : u64 literal ≠ 0)
    (notConstantY : NonConstantSource ctx y)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel (if signedCC cc then rule_inst_5108 else rule_inst_5117).rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧
      trace = rhsTrace.push (if signedCC cc then rule_inst_5108 else rule_inst_5117).id := by
  suffices result : Outcome p ctx (narrowRule cc)
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)]
      fuel st next tr trace out by
    exact outcome_elim result
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have matchProof : Canonical p ctx (narrowRule cc) [.data 145 (ccIdx cc) [],.value x,.value y]
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] := by
    unfold Canonical
    intro q t n
    simpa only [narrowEnv_eq] using narrow_match hp ctx cc half (x := x) typeY q t n
  have wide := fun q t n => wide_failure hp ctx cc half typeX typeY false q t n
  have huge := fun q t n => wide_failure hp ctx cc half typeX typeY true q t n
  have opposite := fun q t n => opposite_match hp ctx cc half (x := x) typeY q t n
  cases sign : signedCC cc
  all_goals simp only [narrowRule,sign,Bool.false_eq_true,ite_true,ite_false] at matchProof wide huge opposite ⊢
  all_goals stock_split hp hc run 652
  all_goals simp only [Prod.mk.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals try (
    exfalso
    apply rejected_prefix (p := p) (ctx := ctx) (st := st) (tr := tr) matchProof hpre
    decide +kernel)
  all_goals have savedMatch := save_match hm
  all_goals have savedRhs := save_rhs he
  all_goals try (exact selected (p := p) (ctx := ctx) (st := st) (tr := tr) matchProof savedMatch savedRhs)
  case false.inl.mk =>
    exact False.elim (left_absurd hp' ctx cc false defined found data nonzero hm)
  case false.inr.inl.mk =>
    exact False.elim (left_absurd hp' ctx cc true defined found data nonzero hm)
  case false.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case false.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case false.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case false.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case false.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case false.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    rw [huge] at hm; cases hm
  case false.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case false.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    rw [wide] at hm; cases hm
  case true.inl.mk =>
    exact False.elim (left_absurd hp' ctx cc false defined found data nonzero hm)
  case true.inr.inl.mk =>
    exact False.elim (left_absurd hp' ctx cc true defined found data nonzero hm)
  case true.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case true.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case true.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case true.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case true.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case true.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    rw [huge] at hm; cases hm
  case true.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (constant_absurd hp' ctx inv cc notConstantY (by decide +kernel) hm)
  case true.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    rw [wide] at hm; cases hm
  case true.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    rw [opposite] at hm; cases hm
end Backend.Stock.Proof.ScalarCmp

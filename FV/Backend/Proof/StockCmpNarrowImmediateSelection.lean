import FV.Backend.Proof.StockCmpNonconstantSelection
import FV.Backend.Proof.StockCmpNonencodableFailures
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

private theorem zero_absurd {p : Program} (hp : Data p) (ctx : Ctx) (nonzeroRule : Bool) (cc : Clif.IntCC)
    {x y j m : Nat} {info : IInfo} {i : Int}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (guard : u64 i ≠ 0)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) (if nonzeroRule then rule_inst_5172 else rule_inst_5170)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  rw [stock_cmp_nonencodable_zero_failure hp ctx nonzeroRule cc defined found data guard st tr m] at matched
  cases matched
private theorem left_zero_absurd {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (nonzeroRule : Bool) (cc : Clif.IntCC)
    {x y m : Nat} (notConstant : NonConstantSource ctx x)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) (if nonzeroRule then rule_inst_5173 else rule_inst_5171)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  have hp' := hp
  cases nonzeroRule
  all_goals isel_inv_simp [hp'.t1,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,
    rule_inst_5171,rule_inst_5173,sem_extract,sem_unData,sem_eq] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [hp'.t1,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,
    rule_inst_5171,rule_inst_5173,sem_extract,sem_unData,sem_eq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals exact nonconstant_extract inv notConstant (by assumption) (by assumption)
private def immediateEnv (cc : Clif.IntCC) (half : Bool) (x : Nat) (imm : Imm12) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 2 (some (.value x))).setIfInBounds 1 (some (.ty (.int (if half then 16 else 8))))).setIfInBounds 3 (some (.op (.imm12 imm)))
private theorem immediateEnv_eq (cc : Clif.IntCC) (half : Bool) (x : Nat) (imm : Imm12) :
    immediateEnv cc half x imm = #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] := by
  apply Array.toList_inj.mp
  simp [immediateEnv,Array.toList_setIfInBounds,List.set,List.replicate]
private theorem immediate_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y j : Nat} {info : IInfo} {i : Int} {imm : Imm12}
    (unsigned : signedCC cc = false)
    (typed : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (encoded : Imm12.ofNat? (u64 i) = some imm) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5134 [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (some (immediateEnv cc half x imm),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have normalizedEncoded : Imm12.ofNat? (u64 (u64 i)) = some imm := by
    rw [u64_ofNat (u64_lt' i)]; exact encoded
  have literal := (ext_imm12_from_u64_iff (ctx := ctx) (st := st.base) (u64 i) [.op (.imm12 imm)]).mpr ⟨imm,normalizedEncoded,rfl⟩
  have fits := ext_fits_in_16 ctx st.base (if half then 16 else 8)
  have code : ∀ q,Stock.externCtor ctx T.unsigned_cond_code [.data 145 (ccIdx cc) []] q =
      .ok (.data 145 (ccIdx cc) [],q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.unsigned_cond_code _ q (by decide)]
    cases cc <;> simp [signedCC] at unsigned <;> rfl
  cases hp
  cases half
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*,rule_inst_5134,immediateEnv,sem_extract,sem_unData,sem_eq,sem_ctor,stock_matchArgs]
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
/-- Actual5134 first-match selection follows from original nonconstant left,
nonzero encodable right constant, narrow typing and unsigned condition. All
higher-priority failures, canonical fields and selected trace are internal. -/
theorem stock_cmp_narrow_immediate_emitter_selected {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) (half : Bool)
    {x y j fuel : Nat} {info : IInfo} {literal : Int} {imm : Imm12}
    (enough : 200 ≤ fuel) (unsigned : signedCC cc = false)
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (notConstantX : NonConstantSource ctx x)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int literal]) (nonzero : u64 literal ≠ 0)
    (encoded : Imm12.ofNat? (u64 literal) = some imm)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_5134.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5134.id := by
  suffices result : Outcome p ctx rule_inst_5134
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))]
      fuel st next tr trace out by exact outcome_elim result
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have matchProof : Canonical p ctx rule_inst_5134 [.data 145 (ccIdx cc) [],.value x,.value y]
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] := by
    unfold Canonical
    intro q t n
    simpa only [immediateEnv_eq] using immediate_match hp ctx cc half unsigned typeX defined found data encoded q t n
  stock_split hp hc run 652
  all_goals simp only [Prod.mk.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals try (
    exfalso
    apply rejected_prefix (p := p) (ctx := ctx) (st := st) (tr := tr) matchProof hpre
    decide +kernel)
  all_goals have savedMatch := save_match hm
  all_goals have savedRhs := save_rhs he
  all_goals try (exact selected (p := p) (ctx := ctx) (st := st) (tr := tr) matchProof savedMatch savedRhs)
  case inl.mk => exact False.elim (left_zero_absurd hp' ctx inv false cc notConstantX hm)
  case inr.inl.mk => exact False.elim (left_zero_absurd hp' ctx inv true cc notConstantX hm)
  case inr.inr.inl.mk => exact False.elim (zero_absurd hp' ctx false cc defined found data nonzero hm)
  case inr.inr.inr.inl.mk => exact False.elim (zero_absurd hp' ctx true cc defined found data nonzero hm)
  all_goals exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
end Backend.Stock.Proof.ScalarCmp

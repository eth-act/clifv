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
private def registerEnv (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 1 (some (.value x))).setIfInBounds 3 (some (.value y))).setIfInBounds 2 (some (.ty (.int sz.bits)))
private def RegisterMatches (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) : Prop :=
  ∀ q trace n,(matchRule p (Stock.sem ctx) {} (n+2) rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]).run (q,trace) =
    .ok (some (registerEnv cc sz x y),q,trace)
attribute [local irreducible] RegisterMatches
private theorem registerEnv_eq (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) :
    registerEnv cc sz x y = #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] := by
  apply Array.toList_inj.mp
  simp [registerEnv,Array.toList_setIfInBounds,List.set,List.replicate]
private theorem register_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y : Nat} (typed : ctx.valueType? y = some (.int sz.bits)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (some (registerEnv cc sz x y),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  cases hp
  cases sz
  all_goals isel_eval [*,rule_inst_5128,registerEnv,sem_extract,sem_unData,ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits]
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

private theorem ordinary_absurd {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y j m : Nat} {info : IInfo} {i : Int} (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (guard : Imm12.ofNat? (u64 i) = none)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  rw [stock_cmp_nonencodable_ordinary_failure hp ctx cc sz typed defined found data guard st tr m] at matched
  cases matched
private theorem predecessor_absurd {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool) (cc : Clif.IntCC) (sz : OperandSize)
    {x y j m : Nat} {info : IInfo} {i : Int} (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (guard : Imm12.ofNat? (u64 (i-1)) = none)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) (if signed then rule_inst_5160 else rule_inst_5155)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  rw [stock_cmp_nonencodable_predecessor_failure hp ctx signed cc sz typed defined found data guard st tr m] at matched
  cases matched
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
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem base_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem width_failure {p : Program} (hp : Data p) (ctx : Ctx) (narrow : Bool)
    (cc : Clif.IntCC) (sz : OperandSize) {x y : Nat}
    (typed : ctx.valueType? x = some (.int sz.bits)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if narrow then rule_inst_5134 else rule_inst_5142)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have noSmall : externExtract ctx T.fits_in_16 (.ty (.int sz.bits)) st.base = .fail := by cases sz <;> rfl
  cases hp
  cases narrow <;> cases sz
  all_goals isel_eval [*,rule_inst_5134,rule_inst_5142,sem_extract,sem_unData,sem_eq,sem_prim,base_eq,base_prim,
    stock_matchArgs,CTy.ofName?,OperandSize.bits]
  all_goals rfl
private theorem width_absurd {p : Program} (hp : Data p) (ctx : Ctx) (narrow : Bool)
    (cc : Clif.IntCC) (sz : OperandSize) {x y m : Nat}
    (typed : ctx.valueType? x = some (.int sz.bits))
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) (if narrow then rule_inst_5134 else rule_inst_5142)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  rw [width_failure hp ctx narrow cc sz typed st tr m] at matched
  cases matched
/-- A successful actual comparison with a nonconstant original left operand and
nonencodable original/right predecessor selects the real register RHS. All
failed higher-priority alternatives and the exact selected environment are derived. -/
theorem stock_cmp_nonencodable_emitter_selected {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y j fuel : Nat} {info : IInfo} {i : Int}
    (enough : 200 ≤ fuel) (typeX : ctx.valueType? x = some (.int sz.bits))
    (typeY : ctx.valueType? y = some (.int sz.bits)) (notConstantX : NonConstantSource ctx x)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (nonzero : u64 i ≠ 0)
    (ordinaryNone : Imm12.ofNat? (u64 i) = none)
    (predecessorNone : Imm12.ofNat? (u64 (i-1)) = none)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5128.id := by
  suffices result : Outcome p ctx rule_inst_5128
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] fuel st next tr trace out by
    exact outcome_elim result
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have lookupX := fun q => ext_value_type ctx q typeX
  have lookupY := fun q => ext_value_type ctx q typeY
  have matchProof : Canonical p ctx rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] := by
    unfold Canonical
    intro q t n
    have actual := register_match hp' ctx cc sz (x := x) typeY q t (n+18)
    simpa only [show (n+18)+2=n+20 from by omega,registerEnv_eq] using actual
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
  case inl.mk =>
    exact False.elim (left_zero_absurd hp' ctx inv false cc notConstantX hm)
  case inr.inl.mk =>
    exact False.elim (left_zero_absurd hp' ctx inv true cc notConstantX hm)
  case inr.inr.inl.mk =>
    exact False.elim (zero_absurd hp' ctx false cc defined found data nonzero hm)
  case inr.inr.inr.inl.mk =>
    exact False.elim (zero_absurd hp' ctx true cc defined found data nonzero hm)
  case inr.inr.inr.inr.inl.mk =>
    exact False.elim (ordinary_absurd hp' ctx cc sz typeX defined found data ordinaryNone hm)
  case inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (predecessor_absurd hp' ctx false cc sz typeX defined found data predecessorNone hm)
  case inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (predecessor_absurd hp' ctx true cc sz typeX defined found data predecessorNone hm)
  case inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (width_absurd hp' ctx false cc sz typeX hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (width_absurd hp' ctx true cc sz typeX hm)
end Backend.Stock.Proof.ScalarCmp

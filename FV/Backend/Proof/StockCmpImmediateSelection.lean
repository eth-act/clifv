module

public import FV.Backend.Proof.StockCmpNonconstantSelection
public import FV.Backend.Proof.StockExtendRequests

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
private def immediateEnv (cc : Clif.IntCC) (sz : OperandSize) (x : Nat) (imm : Imm12) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 2 (some (.value x))).setIfInBounds 1 (some (.ty (.int sz.bits)))).setIfInBounds 3 (some (.op (.imm12 imm)))
private theorem immediateEnv_eq (cc : Clif.IntCC) (sz : OperandSize) (x : Nat) (imm : Imm12) :
    immediateEnv cc sz x imm = #[some (.data 145 (ccIdx cc) []),some (.ty (.int sz.bits)),some (.value x),some (.op (.imm12 imm))] := by
  apply Array.toList_inj.mp
  simp [immediateEnv,Array.toList_setIfInBounds,List.set,List.replicate]
private def ImmediateMatches (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) (imm : Imm12) : Prop :=
  ∀ q trace n,(matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5165 [.data 145 (ccIdx cc) [],.value x,.value y]).run (q,trace) =
    .ok (some (immediateEnv cc sz x imm),q,trace)
attribute [local irreducible] ImmediateMatches
private theorem immediate_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y j : Nat} {info : IInfo} {i : Int} {imm : Imm12}
    (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (encoded : Imm12.ofNat? (u64 i) = some imm) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5165 [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (some (immediateEnv cc sz x imm),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have normalizedEncoded : Imm12.ofNat? (u64 (u64 i)) = some imm := by
    rw [u64_ofNat (u64_lt' i)]; exact encoded
  have literal := (ext_imm12_from_u64_iff (ctx := ctx) (st := st.base) (u64 i) [.op (.imm12 imm)]).mpr ⟨imm,normalizedEncoded,rfl⟩
  cases hp
  cases sz
  all_goals isel_eval [*,rule_inst_5165,immediateEnv,sem_extract,sem_unData,ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits]
private theorem nonconstant_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x j : Nat} {info : IInfo} (notConstant : NonConstantSource ctx x)
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    {value : V} (data : info.data = .data 152 35 [.data 151 57 [],value]) : False := by
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty,c,rfl,fields⟩ := instData_iconst_inv raw
  exact notConstant j info defined found ty c clif
private theorem rejected_immediate {p : Program} {ctx : Ctx} {cc : Clif.IntCC} {sz : OperandSize}
    {x y : Nat} {imm : Imm12} {st : State} {tr : Array RuleId}
    (matchProof : ImmediateMatches p ctx cc sz x y imm)
    (failed : ∃ m after,(matchRule p (Stock.sem ctx) {} (m+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,after)) : False := by
  obtain ⟨m,after,failed⟩ := failed
  unfold ImmediateMatches at matchProof
  rw [matchProof st tr m] at failed
  cases failed
private theorem rejected_prefix {p : Program} {ctx : Ctx} {cc : Clif.IntCC} {sz : OperandSize}
    {x y : Nat} {imm : Imm12} {st : State} {tr : Array RuleId} {pre : List Rule}
    (matchProof : ImmediateMatches p ctx cc sz x y imm)
    (rejected : ∀ r ∈ pre,∃ m after,(matchRule p (Stock.sem ctx) {} (m+20) r
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,after))
    (earlier : rule_inst_5165 ∈ pre) : False := rejected_immediate matchProof (rejected _ earlier)
private theorem immediate_rhs_from_match {p : Program} {ctx : Ctx} {cc : Clif.IntCC} {sz : OperandSize}
    {x y m fuel : Nat} {imm : Imm12} {st next : State} {tr trace : Array RuleId}
    {env : Isle.Interp.Env V} {s1 : State × Array RuleId} {out : V}
    (matchProof : ImmediateMatches p ctx cc sz x y imm)
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,s1))
    (rhs : (evalExpr p (Stock.sem ctx) {} fuel rule_inst_5165.rhs env).run s1 = .ok (some out,next,trace)) :
    (evalExpr p (Stock.sem ctx) {} fuel rule_inst_5165.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int sz.bits)),some (.value x),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,trace) := by
  unfold ImmediateMatches at matchProof
  rw [matchProof st tr m] at matched
  have parts := Prod.mk.inj (Except.ok.inj matched)
  have envEq := Option.some.inj parts.1
  have stateEq := parts.2
  rw [← envEq,← stateEq] at rhs
  simpa only [immediateEnv_eq] using rhs
private def SavedMatch (p : Program) (ctx : Ctx) (fuel : Nat) (r : Rule) (args : List V)
    (start : State × Array RuleId) (env : Isle.Interp.Env V) (finish : State × Array RuleId) : Prop :=
  (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)
attribute [local irreducible] SavedMatch
private theorem save_match {p : Program} {ctx : Ctx} {fuel : Nat} {r : Rule} {args : List V}
    {start finish : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule p (Stock.sem ctx) {} fuel r args).run start = .ok (some env,finish)) :
    SavedMatch p ctx fuel r args start env finish := by
  unfold SavedMatch
  exact matched
private def SavedRhs (p : Program) (ctx : Ctx) (fuel : Nat) (expr : Expr) (env : Isle.Interp.Env V)
    (start : State × Array RuleId) (out : V) (finish : State × Array RuleId) : Prop :=
  (evalExpr p (Stock.sem ctx) {} fuel expr env).run start = .ok (some out,finish)
attribute [local irreducible] SavedRhs
private theorem save_rhs {p : Program} {ctx : Ctx} {fuel : Nat} {expr : Expr} {env : Isle.Interp.Env V}
    {start finish : State × Array RuleId} {out : V}
    (rhs : (evalExpr p (Stock.sem ctx) {} fuel expr env).run start = .ok (some out,finish)) :
    SavedRhs p ctx fuel expr env start out finish := by
  unfold SavedRhs
  exact rhs
private theorem immediate_rhs_saved {p : Program} {ctx : Ctx} {cc : Clif.IntCC} {sz : OperandSize}
    {x y m fuel : Nat} {imm : Imm12} {st next : State} {tr trace : Array RuleId}
    {env : Isle.Interp.Env V} {s1 : State × Array RuleId} {out : V}
    (matchProof : ImmediateMatches p ctx cc sz x y imm)
    (matched : SavedMatch p ctx (m+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) env s1)
    (rhs : SavedRhs p ctx fuel rule_inst_5165.rhs env s1 out (next,trace)) :
    (evalExpr p (Stock.sem ctx) {} fuel rule_inst_5165.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int sz.bits)),some (.value x),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,trace) := by
  unfold SavedMatch at matched
  unfold SavedRhs at rhs
  exact immediate_rhs_from_match matchProof matched rhs
private def ImmediateOutcome (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize)
    (x : Nat) (imm : Imm12) (fuel : Nat) (st : State) (tr : Array RuleId)
    (out : V) (next : State) (trace : Array RuleId) : Prop :=
  ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_5165.rhs
    #[some (.data 145 (ccIdx cc) []),some (.ty (.int sz.bits)),some (.value x),some (.op (.imm12 imm))]).run
    (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5165.id
attribute [local irreducible] ImmediateOutcome
private theorem immediate_outcome_elim {p : Program} {ctx : Ctx} {cc : Clif.IntCC} {sz : OperandSize}
    {x fuel : Nat} {imm : Imm12} {st next : State} {tr trace : Array RuleId} {out : V}
    (outcome : ImmediateOutcome p ctx cc sz x imm fuel st tr out next trace) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_5165.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int sz.bits)),some (.value x),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5165.id := by
  unfold ImmediateOutcome at outcome
  exact outcome
private theorem immediate_outcome {p : Program} {ctx : Ctx} {cc : Clif.IntCC} {sz : OperandSize}
    {x y m fuel : Nat} {imm : Imm12} {st next : State} {tr trace : Array RuleId}
    {env : Isle.Interp.Env V} {s1 : State × Array RuleId} {out : V}
    (matchProof : ImmediateMatches p ctx cc sz x y imm)
    (matched : SavedMatch p ctx (m+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) env s1)
    (rhs : SavedRhs p ctx fuel rule_inst_5165.rhs env s1 out (next,trace)) :
    ImmediateOutcome p ctx cc sz x imm fuel st tr out next (trace.push rule_inst_5165.id) := by
  unfold ImmediateOutcome
  exact ⟨trace,immediate_rhs_saved matchProof matched rhs,rfl⟩
private def LiteralSource (ctx : Ctx) (y j : Nat) (info : IInfo) (i : Int) : Prop :=
  ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧ info.data = .data 152 35 [.data 151 57 [],.int i]
attribute [local irreducible] LiteralSource
private theorem nonzero_literal {ctx : Ctx} {y j : Nat} {info : IInfo} {i : Int}
    (original : LiteralSource ctx y j info i) (nonzero : u64 i ≠ 0)
    {j' : Nat} {info' : IInfo} {payload : V} {st : LState}
    (defined : ctx.defInst? y = some j') (found : ctx.insts[j']? = some info')
    (data : info'.data = .data 152 35 [.data 151 57 [],payload])
    (extracted : externExtract ctx T.u64_from_imm64 payload st = .ok [.int 0]) : False := by
  unfold LiteralSource at original
  obtain ⟨defOriginal,foundOriginal,dataOriginal⟩ := original
  have sameIndex := Option.some.inj (defined.symm.trans defOriginal)
  subst j'
  have sameInfo := Option.some.inj (found.symm.trans foundOriginal)
  subst info'
  have same := data.symm.trans dataOriginal
  have fields := (V.data.inj same).2.2
  have payloadEq := (List.cons.inj (List.cons.inj fields).2).1
  rw [payloadEq,ext_u64_from_imm64] at extracted
  have zero := V.int.inj (List.cons.inj (ExtResult.ok.inj extracted)).1
  apply nonzero
  omega
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
private theorem nonzero_extract {ctx : Ctx} {y j : Nat} {info : IInfo} {i : Int}
    (original : LiteralSource ctx y j info i) (nonzero : u64 i ≠ 0)
    {st : LState} {node ty payload : V}
    (definition : externExtract ctx T.def_inst (.value y) st = .ok [node])
    (instruction : externExtract ctx T.inst_data_value node st =
      .ok [ty,.data 152 35 [.data 151 57 [],payload]])
    (extracted : externExtract ctx T.u64_from_imm64 payload st = .ok [.int 0]) : False := by
  obtain ⟨j',info',defined,found,data⟩ := constant_extract definition instruction
  exact nonzero_literal original nonzero defined found data extracted
private theorem rejected_match {p : Program} {ctx : Ctx} {cc : Clif.IntCC} {sz : OperandSize}
    {x y m : Nat} {imm : Imm12} {st : State} {tr : Array RuleId} {after : State × Array RuleId}
    (matchProof : ImmediateMatches p ctx cc sz x y imm)
    (failed : (matchRule p (Stock.sem ctx) {} (m+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,after)) : False :=
  rejected_immediate matchProof ⟨m,after,failed⟩
/-- Real emitter success with an original nonzero encodable RHS constant
selects the actual immediate rule. Earlier zero cases and later register/narrow
fallbacks are excluded by original source data and the successful earlier match. -/
theorem stock_cmp_immediate_emitter_selected {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y j fuel : Nat} {info : IInfo} {i : Int} {imm : Imm12}
    (enough : 200 ≤ fuel) (typeX : ctx.valueType? x = some (.int sz.bits))
    (typeY : ctx.valueType? y = some (.int sz.bits)) (notConstantX : NonConstantSource ctx x)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (nonzero : u64 i ≠ 0)
    (encoded : Imm12.ofNat? (u64 i) = some imm)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_5165.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int sz.bits)),some (.value x),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5165.id := by
  suffices outcome : ImmediateOutcome p ctx cc sz x imm fuel st tr out next trace by
    exact immediate_outcome_elim outcome
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have typedX := fun q => ext_value_type ctx q typeX
  have typedY := fun q => ext_value_type ctx q typeY
  have definition := fun q => ext_def_inst_some ctx q defined
  have instruction := fun q => ext_inst_data_value ctx q found
  simp only [data] at instruction
  have normalized := fun q => ext_u64_from_imm64 ctx q i
  have original : LiteralSource ctx y j info i := by
    unfold LiteralSource
    exact ⟨defined,found,data⟩
  have matchImm : ImmediateMatches p ctx cc sz x y imm := by
    unfold ImmediateMatches
    exact fun q trace n => immediate_match hp' ctx cc sz typeX defined found data encoded q trace n
  have envEq := immediateEnv_eq cc sz x imm
  stock_split hp hc run 652
  all_goals try (
    exfalso
    apply rejected_prefix (st := st) (tr := tr) matchImm hpre
    simp only [List.mem_cons,List.mem_singleton]
    repeat first | exact Or.inl rfl | apply Or.inr
    rfl)
  all_goals have savedMatch := save_match hm
  all_goals have savedRhs := save_rhs he
  all_goals clear he run
  all_goals try (exact immediate_outcome (st := st) (tr := tr) matchImm savedMatch savedRhs)
  all_goals clear defined found data definition instruction normalized
  all_goals isel_inv_simp [hp'.t1,hp'.t2,hp'.t120,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,hp'.t325,rule_inst_5165,rule_inst_5171,rule_inst_5173,rule_inst_5170,rule_inst_5172,
    sem_extract,sem_unData,sem_eq,sem_prim,zero] at hm
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [hp'.t1,hp'.t2,hp'.t120,hp'.t144,hp'.t209,hp'.t2341,hp'.t2482,hp'.t2269,hp'.t2270,hp'.t325,rule_inst_5165,rule_inst_5171,rule_inst_5173,rule_inst_5170,rule_inst_5172,
    sem_extract,sem_unData,sem_eq,sem_prim,zero] at *
  all_goals try (cases sz <;> simp [OperandSize.bits,ext_ty_32_or_64_32,ext_ty_32_or_64_64] at hm)
  all_goals isel_destruct <;> subst_vars
  all_goals simp only [typeX,typeY,nonzero,Option.some.injEq,reduceCtorEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals try (
    exfalso
    apply nonconstant_data inv notConstantX
    · assumption
    · assumption
    · symm; assumption)
  all_goals try (
    exfalso
    apply nonzero_literal original nonzero
    · assumption
    · assumption
    · symm; assumption
    · assumption)
  all_goals try (
    exfalso
    apply nonconstant_extract inv notConstantX
    · assumption
    · assumption)
  all_goals try (
    exfalso
    apply nonzero_extract original nonzero
    · assumption
    · assumption
    · assumption)
  all_goals have normalizedPrefix := hpre
  all_goals simp at normalizedPrefix
  all_goals try (
    obtain ⟨m,a,b,failed⟩ := normalizedPrefix.2.2.2.2.1
    exact False.elim (rejected_match (st := st) (tr := tr) (m := m) (after := (a,b)) matchImm failed))
  all_goals try (
    obtain ⟨m,a,b,failed⟩ := normalizedPrefix.2.2.2.2
    exact False.elim (rejected_match (st := st) (tr := tr) (m := m) (after := (a,b)) matchImm failed))
  all_goals try (cases sz <;> simp [OperandSize.bits,CTy.ofName?,CTy.int.injEq] at *)
  all_goals unfold ImmediateOutcome
  all_goals unfold SavedMatch at savedMatch
  all_goals unfold SavedRhs at savedRhs
  all_goals exact ⟨_,immediate_rhs_from_match (st := st) (tr := tr) matchImm savedMatch savedRhs,rfl⟩
end Backend.Stock.Proof.ScalarCmp

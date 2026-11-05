import FV.Backend.Proof.StockComparisonBranchFacts
import FV.Backend.Proof.StockCmpMatchedImmediate
import FV.Backend.Proof.StockCmpImmediateEmission

namespace Backend.Stock.Proof.ComparisonBranch
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem icmp_instData {f : Clif.Function} {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat} {d : V}
    (h : instData f (.icmp cc ty a b) = .ok d) :
    d = .data 152 14 [.data 151 72 [],.values [a,b],.data 145 (ccIdx cc) []] := by
  simp only [instData] at h
  split at h
  · simp only [pure,Except.pure,Except.ok.injEq] at h
    rw [← h,mkVariant_intcc]
    rfl
  · cases h

/-- The instruction data `instData` gives a subset-E integer constant. -/
private theorem iconst_instData {f : Clif.Function} {ty : Clif.Ty} {k : BitVec ty.width} {d : V}
    (integer : Compile.instE (.iconst ty k) = true) (h : instData f (.iconst ty k) = .ok d) :
    d = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty k)] := by
  have typed : eTy ty = true := integer
  simp only [instData,typed,ite_true,pure,Except.pure,Except.ok.injEq] at h
  rw [← h]
  rfl

attribute [local irreducible] Isle.Aarch64.program

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

private theorem comparison_source {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {c : Nat} {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) :
    ∃ j info,ctx.defInst? c = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 14 [.data 151 72 [],.values [a,b],.data 145 (ccIdx cc) []] := by
  cases defined : ctx.defInst? c with
  | none => simp [Ctx.defClif?,defined] at origin
  | some j =>
    cases found : ctx.insts[j]? with
    | none => simp [Ctx.defClif?,defined,found] at origin
    | some info =>
      have clif : info.clif = some (.icmp cc ty a b) := by
        simpa [Ctx.defClif?,defined,found] using origin
      exact ⟨j,info,rfl,found,icmp_instData (inv.data j info _ found clif)⟩

/-- The source definition of a constant operand carries `iconst` data with
its original `Imm64`, and its type is at most 64 bits wide. -/
private theorem constant_source {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {y : Nat} {ty : Clif.Ty} {k : BitVec ty.width} (constant : ctx.defClif? y = some (.iconst ty k)) :
    ∃ j info,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty k)] ∧ ty.width ≤ 64 := by
  cases defined : ctx.defInst? y with
  | none => simp [Ctx.defClif?,defined] at constant
  | some j =>
    cases found : ctx.insts[j]? with
    | none => simp [Ctx.defClif?,defined,found] at constant
    | some info =>
      have clif : info.clif = some (.iconst ty k) := by
        simpa [Ctx.defClif?,defined,found] using constant
      have integer := inv.instE j info _ found clif
      refine ⟨j,info,rfl,found,iconst_instData integer (inv.data j info _ found clif),?_⟩
      cases ty <;> simp [Compile.instE,Compile.tyE,Clif.Ty.isInt,Clif.Ty.width] at integer ⊢

private theorem maybe_uextend_icmp {ctx : Ctx} {c : Nat} {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) (st : LState) :
    externExtract ctx T.maybe_uextend (.value c) st = .ok [.value c] := by
  have unfolded : externExtract ctx T.maybe_uextend (.value c) st = match ctx.defClif? c with
    | some (.extend .uextend _ x) => .ok [.value x]
    | _ => .ok [.value c] := rfl
  rw [unfolded,origin]

section Names
attribute [local semireducible] Isle.Aarch64.program
private theorem fcmp_name : (variantNames 151)[112]? = some "Fcmp" := by decide +kernel
end Names
private theorem legacy_fcmp_absurd {f : Clif.Function} {ctx : Ctx} (inv : CtxInv f ctx)
    {c : Nat} {st : LState} {env next : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st rule_inst_4965.args [.value c] env = .ok (some next)) : False := by
  have hp := data_program
  isel_inv' hp [] at matched
  rcases ‹(∃ _ _, _) ∨ _› with ⟨uty,z,definition,rfl⟩ | ⟨_,rfl⟩
  all_goals repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)
  all_goals
    obtain ⟨defined⟩ : Nonempty (ctx.defInst? _ = some _) := ⟨‹_›⟩
    obtain ⟨found⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
    obtain ⟨data⟩ : Nonempty (V.data 152 11 _ = _) := ⟨‹_›⟩
    exact opcode_absurd inv defined found data fcmp_name (by decide +kernel)
private theorem fcmp_absurd {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {c fuel : Nat} {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {next : State × Array RuleId}
    (matched : (matchRule program (Stock.sem ctx) {} fuel rule_inst_4965 [.value c]).run (st,tr) = .ok (some env,next)) : False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨before,args,_⟩ := matchRule_some_inv matched
    have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl,rfl,rfl,rfl,rfl⟩
    rw [stock_matchArgs_source view] at args
    exact legacy_fcmp_absurd inv.identityView args

/-- Actual4966 matching succeeds on an original comparison condition, with
unchanged state and trace. -/
private theorem comparison_match {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_4966 [.value c]).run (st,tr) =
      .ok (some #[some (.value a),some (.value b),some (.data 145 (ccIdx cc) [])],st,tr) := by
  obtain ⟨j,info,defined,found,data⟩ := comparison_source inv origin
  have uext := maybe_uextend_icmp origin st.base
  have dinst := ext_def_inst_some ctx st.base defined
  have idata := ext_inst_data_value ctx st.base found
  rw [data] at idata
  have pair := ext_value_array_2 ctx st.base a b
  cases hp
  isel_eval [*,rule_inst_4966,sem_extract,sem_unData,stock_matchArgs]
  rfl

/-- Actual original650 on a direct integer comparison takes rule 4966: rule
4965 needs a float comparison, and the fallback 4967 is unreachable because
4966 matches. Its RHS calls emit_icmp with the original operands. -/
private theorem comparison_condition_call {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c : Nat} {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) {fuel : Nat} (enough : 400 ≤ fuel)
    {st middle : State} {tr trace : Array RuleId} {condition : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 650 [.value c] (st,tr) condition (middle,trace)) :
    ∃ helperFuel helperTrace,300 ≤ helperFuel ∧
      ApplyInternal program (Stock.sem ctx) {} helperFuel 123 652
        [.data 145 (ccIdx cc) [],.value a,.value b] (st,tr) condition (middle,helperTrace) := by
  have hp := data_program
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  stock_split hp hc run 650
  · exact False.elim (fcmp_absurd inv hm)
  · rw [comparison_match hp' inv origin st tr] at hm
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at hm
    obtain ⟨rfl,rfl⟩ := hm
    isel_inv [*,rule_inst_4966,sem_extract,sem_unData,stock_matchArgs] at he
    obtain ⟨call⟩ : Nonempty (ApplyInternal program (Stock.sem ctx) {} _ 123 652 _ _ _ _) := ⟨‹_›⟩
    have first : #[some (V.value a),some (V.value b),some (V.data 145 (ccIdx cc) [])][0]? = some (some _) := ‹_›
    have second : #[some (V.value a),some (V.value b),some (V.data 145 (ccIdx cc) [])][1]? = some (some _) := ‹_›
    have third : #[some (V.value a),some (V.value b),some (V.data 145 (ccIdx cc) [])][2]? = some (some _) := ‹_›
    simp only [List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at first second third
    subst first second third
    exact ⟨_,by omega,_,call⟩
  · obtain ⟨fuel,after,failed⟩ := hpre rule_inst_4966 (by simp)
    rw [comparison_match hp' inv origin st tr fuel] at failed
    simp at failed

private def immediateEnv (cc : Clif.IntCC) (sz : OperandSize) (x : Nat) (imm : Imm12) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 2 (some (.value x))).setIfInBounds 1 (some (.ty (.int sz.bits)))).setIfInBounds 3 (some (.op (.imm12 imm)))

/-- Actual immediate-rule 5165 matching succeeds on a 32/64-bit first operand
and an original encodable constant second operand. -/
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

/-- A zero-rule match on the constant operand reads the same constant, so the
constant is zero. -/
private theorem zero_constant {ctx : Ctx} {y j j' : Nat} {info info' : IInfo}
    {ty : Clif.Ty} {k : BitVec ty.width} {literal : Int} (width : ty.width ≤ 64)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty k)])
    (defined' : ctx.defInst? y = some j') (found' : ctx.insts[j']? = some info')
    (data' : info'.data = .data 152 35 [.data 151 57 [],.int literal]) (zero : u64 literal = 0) : k = 0 := by
  rw [defined] at defined'
  cases defined'
  rw [found] at found'
  cases found'
  rw [data] at data'
  simp only [V.data.injEq,List.cons.injEq,V.int.injEq,and_true,true_and] at data'
  rw [← data',u64_imm64OfIconst width] at zero
  exact BitVec.eq_of_toNat_eq (by simpa using zero)

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

/-- Actual 32/64-bit emit_icmp on a source parameter and an original constant
that `Imm12::maybe_from_u64` encodes selects the immediate rule 5165. The zero
rules need a defined first operand or, for `eq`/`ne`, a zero constant; every
later rule is unreachable because 5165 matches. The result is a flag-producing
`subs xzr, x, #imm` with no definitions, and the compiler state is unchanged
except for operand demand marks. -/
private theorem imm_parameter_comparison {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) (wide : Bool) {x y fuel : Nat}
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0) (enough : 300 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) out (next,trace)) :
    ∃ (mi : V) (producer : MInst),out = .data 123 2 [.data 47 1 [mi],.data 96 (condOf cc).idx []] ∧
      MInst.ofV mi = some producer ∧ vdefs producer = [] ∧ next.base = st.base := by
  have hp := data_program
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  obtain ⟨j,info,defined,found,data,width⟩ := constant_source inv constY
  have encoded : Imm12.ofNat? (u64 (imm64OfIconst ty' k)) = some imm := by
    rw [u64_imm64OfIconst width]
    exact fits
  have typedSize : ctx.valueType? x = some (.int (if wide then OperandSize.size64 else .size32).bits) := by
    cases wide <;> exact typeX
  have rejected : (∃ m s1,(matchRule program (Stock.sem ctx) {} (m+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,s1)) → False := by
    rintro ⟨m,s1,failed⟩
    rw [immediate_match hp' ctx cc _ typedSize defined found data encoded st tr m] at failed
    cases failed
  obtain ⟨pre,r,post,hL,hpre,matchN,rhsN,env,afterMatch,emittedState,rhsTrace,hm,he,stateEq,fuelEq⟩ :=
    cmp_internal_split_first hc hp.t652 term_652_kind rfl (by rw [hp.r652]; simp; omega) run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj stateEq
  subst fuel
  rw [hp.r652] at hL
  isel_rule_cases hL
  all_goals cases hp
  case inl.mk =>
    obtain ⟨_,_,_,_,definedX,_⟩ := stock_cmp_zero_match_observed hp' ctx inv true false cc x y hm
    simp [parameterX] at definedX
  case inr.inl.mk =>
    obtain ⟨_,_,_,_,definedX,_⟩ := stock_cmp_zero_match_observed hp' ctx inv true true cc x y hm
    simp [parameterX] at definedX
  case inr.inr.inl.mk =>
    obtain ⟨_,_,_,ccEq,definedY,foundY,dataY,zero,_⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv false false cc x y hm
    simp only [Bool.false_eq_true,ite_false] at ccEq definedY
    exact False.elim (nonzero (Or.inl ccEq)
      (zero_constant width defined found data definedY foundY dataY zero))
  case inr.inr.inr.inl.mk =>
    obtain ⟨_,_,_,ccEq,definedY,foundY,dataY,zero,_⟩ :=
      stock_cmp_zero_match_observed hp' ctx inv false true cc x y hm
    simp only [Bool.false_eq_true,ite_false,ite_true] at ccEq definedY
    exact False.elim (nonzero (Or.inr ccEq)
      (zero_constant width defined found data definedY foundY dataY zero))
  case inr.inr.inr.inr.inl.mk =>
    have typed : ctx.valueType? x = some (.int (if wide then Clif.Ty.i64 else .i32).width) := by
      cases wide <;> exact typeX
    obtain ⟨_,_,_,actualImm,_,_,_,_,_,envEq,afterEq⟩ :=
      stock_cmp_immediate_match_observed hp' ctx inv false cc (if wide then .i64 else .i32) x y typed hm
    have bits : (if wide then Clif.Ty.i64 else .i32).width = (if wide then OperandSize.size64 else .size32).bits := by
      cases wide <;> rfl
    rw [envEq,afterEq,bits] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨_,rx,mappedX,output,finish⟩ := stock_cmp_immediate_rhs_observed hp' ctx rfl cc
      (if wide then .size64 else .size32) he
    obtain ⟨kx,rfl⟩ := inv.valueReg x rx mappedX
    rw [output,finish]
    refine ⟨_,.aluRRImm12 .subS (if wide then .size64 else .size32) .xzr (.vreg kx .int) actualImm,
      rfl,?_,?_,rfl⟩
    · cases wide <;> rfl
    · cases wide <;> rfl
  all_goals exact False.elim (rejected (hpre rule_inst_5165 (by simp)))

/-- Actual descriptor construction and emission of a flag condition append
exactly its producer and the conditional branch. -/
private theorem flags_emission {ctx : Ctx} {constructFuel emitFuel : Nat}
    (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {mi : V} {producer : MInst} {condition : Cond} (decoded : MInst.ofV mi = some producer)
    (notAl : condition ≠ .al) (notNv : condition ≠ .nv) (noDefs : vdefs producer = [])
    {descriptor out : V} {yes no : Label} {before middle next : State}
    {trace constructTrace final : Array RuleId}
    (construct : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []],.label yes,.label no]
      (before,trace) descriptor (middle,constructTrace))
    (emit : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (middle,constructTrace) out (next,final)) :
    next.base = (before.base.emit producer).emit (.condBr yes no (.cond condition)) := by
  have shape : CondShape (.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []]) (fun _ => True) :=
    .inr (.inr ⟨mi,producer,condition,rfl,decoded,notAl,notNv,noDefs,fun _ _ => trivial⟩)
  obtain ⟨base,descriptorEq⟩ := ConditionalValues.descriptor_shape rfl enoughConstruct shape construct
  have projected := BranchHelpers.stock_emit_side_effect_projects ctx {} rfl (emitFuel+1)
    [descriptor] middle constructTrace
  have legacy : ApplyInternal program (Backend.sem ctx) {} emitFuel 13 242
      [descriptor] (middle.base,constructTrace) out (next.base,final) := by
    unfold ApplyInternal at emit ⊢
    rw [emit] at projected
    exact projected.symm
  rw [base,descriptorEq] at legacy
  dsimp only [brCondV] at legacy
  obtain ⟨first,last,finish,decodedFirst,decodedLast⟩ :=
    emit_side_effect_inst2_ok data_program rfl enoughEmit legacy
  rw [decoded] at decodedFirst
  cases decodedFirst
  rw [ofV_condBr_cond] at decodedLast
  cases decodedLast
  exact finish

/-- The selected calls of a wide comparison branch on a source parameter and
an encodable constant append exactly `subs xzr, x, #imm` (no definitions) and
`b.cond`; the constant itself is not materialized. -/
theorem Calls.comparison_imm_emission {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : ConditionalCalls.Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0) :
    ∃ producer : MInst,vdefs producer = [] ∧
      next.base = (before.base.emit producer).emit (.condBr calls.yes calls.no (.cond (condOf cc))) := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  obtain ⟨helperFuel,helperTrace,enough,comparison⟩ :=
    comparison_condition_call inv origin calls.conditionEnough conditionRun
  obtain ⟨mi,producer,rawEq,decoded,noDefs,middleBase⟩ :=
    imm_parameter_comparison inv cc wide typeX parameterX constY fits nonzero enough comparison
  have constructRun := calls.constructRun
  rw [rawEq] at constructRun
  have finish := flags_emission calls.constructEnough calls.emitEnough decoded
    (condOf_ne_al cc).1 (condOf_ne_al cc).2 noDefs constructRun calls.emitRun
  rw [middleBase] at finish
  exact ⟨producer,noDefs,finish⟩

end Backend.Stock.Proof.ComparisonBranch

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

/-- The selected wide comparison branch on a source parameter and an
encodable constant preserves both its allocation frontier and its
source-demand extent. -/
theorem Calls.comparison_imm_bounds {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0) :
    next.base.nextVreg = before.base.nextVreg ∧ next.demand.size = before.demand.size := by
  have size := (Extent.apply_demand_size calls.emitRun).trans
    ((Extent.apply_demand_size calls.constructRun).trans (Extent.apply_demand_size calls.conditionRun))
  obtain ⟨producer,_,finish⟩ := ComparisonBranch.Calls.comparison_imm_emission inv calls source origin
    wide typeX parameterX constY fits nonzero
  rw [finish]
  exact ⟨rfl,size⟩

/-- The selected wide comparison branch on a source parameter and an
encodable constant appends exactly two instructions: `subs xzr, x, #imm` and
`b.cond`. -/
theorem Calls.comparison_imm_emitted_size {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0) :
    next.base.emitted.size = before.base.emitted.size+2 := by
  obtain ⟨producer,_,finish⟩ := ComparisonBranch.Calls.comparison_imm_emission inv calls source origin
    wide typeX parameterX constY fits nonzero
  rw [finish]
  simp only [LState.emit,Array.size_push]

/-- The selected wide comparison branch on a source parameter and an
encodable constant derives a complete fragment with no virtual-register
definitions. -/
theorem Calls.comparison_imm_no_defs {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0) :
    ∃ code,Frag before.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  obtain ⟨producer,noDefs,finish⟩ := ComparisonBranch.Calls.comparison_imm_emission inv calls source origin
    wide typeX parameterX constY fits nonzero
  refine ⟨[producer,.condBr calls.yes calls.no (.cond (condOf cc))],?_,?_⟩
  · rw [finish]
    exact (Frag.emit_nodef _ noDefs).append (Frag.emit_nodef _ rfl)
  · intro inst member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact noDefs
    · rfl

end Backend.Stock.Proof.ConditionalCalls

import FV.Backend.Proof.StockComparisonBranchFacts
import FV.Backend.Proof.StockComparisonComputedSelection

/-! Comparison branches on computed operands: emission facts (#140, CB-8).

`Calls.comparison_wide_emission` needs two source parameters to exclude the other rules of
`emit_icmp` (term 652). The zero, 12-bit immediate and odd-predecessor rules (5170-5173, 5165,
5155, 5160) need an operand defined by an `iconst`, and the narrow and i128 rules need other
types. So two wide operands that are not defined by an `iconst` (`NonConstantSource`) select the
register rule 5128 (`stock_cmp_nonconstant_emitter_selected`), with any other definition. The
emission is `subs xzr, x, y` and `b.cond`, with no virtual-register definitions. -/

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

/-- Actual original650 on a direct integer comparison takes rule 4966 and calls emit_icmp with
the original operands. -/
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

/-- Actual 32/64-bit emit_icmp on two nonconstant operands selects the register rule 5128. The
result is a flag-producing `subs xzr` with no definitions, and the compiler state is unchanged
except for operand demand marks. -/
private theorem wide_computed_comparison {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) (wide : Bool) {x y fuel : Nat}
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource ctx x) (constantY : NonConstantSource ctx y) (enough : 300 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) out (next,trace)) :
    ∃ (mi : V) (producer : MInst),out = .data 123 2 [.data 47 1 [mi],.data 96 (condOf cc).idx []] ∧
      MInst.ofV mi = some producer ∧ vdefs producer = [] ∧ next.base = st.base := by
  let sz : OperandSize := if wide then .size64 else .size32
  have bits : sz.bits = (if wide then 64 else 32) := by cases wide <;> rfl
  rw [← bits] at typeX typeY
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_nonconstant_emitter_selected data_program ctx inv cc sz
    (by omega) typeX typeY constantX constantY run
  obtain ⟨n,gas⟩ : ∃ n,fuel=n+100 := ⟨fuel-100,by omega⟩
  rw [gas] at rhs
  obtain ⟨_,_,rx,ry,mappedX,mappedY,output,finish⟩ := stock_cmp_register_rhs_observed data_program ctx rfl
    cc sz rhs
  obtain ⟨kx,rfl⟩ := inv.valueReg x rx mappedX
  obtain ⟨ky,rfl⟩ := inv.valueReg y ry mappedY
  rw [output,finish]
  refine ⟨_,.aluRRR .subS sz .xzr (.vreg kx .int) (.vreg ky .int),rfl,?_,?_,rfl⟩
  · cases wide <;> rfl
  · cases wide <;> rfl

/-- Actual descriptor construction and emission of a flag condition append exactly its producer
and the conditional branch. -/
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

/-- The selected calls of a wide comparison branch on two nonconstant operands append exactly
`subs xzr, a, b` (no definitions) and `b.cond`. -/
theorem Calls.comparison_computed_emission {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : ConditionalCalls.Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat} (origin : ctx.defClif? c = some (.icmp cc ty a b))
    (wide : Bool)
    (typeA : ctx.valueType? a = some (.int (if wide then 64 else 32)))
    (typeB : ctx.valueType? b = some (.int (if wide then 64 else 32)))
    (constantA : NonConstantSource ctx a) (constantB : NonConstantSource ctx b) :
    ∃ producer : MInst,vdefs producer = [] ∧
      next.base = (before.base.emit producer).emit (.condBr calls.yes calls.no (.cond (condOf cc))) := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  obtain ⟨helperFuel,helperTrace,enough,comparison⟩ :=
    comparison_condition_call inv origin calls.conditionEnough conditionRun
  obtain ⟨mi,producer,rawEq,decoded,noDefs,middleBase⟩ :=
    wide_computed_comparison inv cc wide typeA typeB constantA constantB enough comparison
  have constructRun := calls.constructRun
  rw [rawEq] at constructRun
  have finish := flags_emission calls.constructEnough calls.emitEnough decoded
    (condOf_ne_al cc).1 (condOf_ne_al cc).2 noDefs constructRun calls.emitRun
  rw [middleBase] at finish
  exact ⟨producer,noDefs,finish⟩

end Backend.Stock.Proof.ComparisonBranch

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option autoImplicit false

/-- The selected wide comparison branch on two nonconstant operands preserves both its
allocation frontier and its source-demand extent. -/
theorem Calls.comparison_computed_bounds {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat} (origin : ctx.defClif? c = some (.icmp cc ty a b))
    (wide : Bool)
    (typeA : ctx.valueType? a = some (.int (if wide then 64 else 32)))
    (typeB : ctx.valueType? b = some (.int (if wide then 64 else 32)))
    (constantA : NonConstantSource ctx a) (constantB : NonConstantSource ctx b) :
    next.base.nextVreg = before.base.nextVreg ∧ next.demand.size = before.demand.size := by
  have size := (Extent.apply_demand_size calls.emitRun).trans
    ((Extent.apply_demand_size calls.constructRun).trans (Extent.apply_demand_size calls.conditionRun))
  obtain ⟨producer,_,finish⟩ := ComparisonBranch.Calls.comparison_computed_emission inv calls source origin
    wide typeA typeB constantA constantB
  rw [finish]
  exact ⟨rfl,size⟩

/-- The selected wide comparison branch on two nonconstant operands appends exactly two
instructions: `subs xzr, a, b` and `b.cond`. -/
theorem Calls.comparison_computed_emitted_size {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat} (origin : ctx.defClif? c = some (.icmp cc ty a b))
    (wide : Bool)
    (typeA : ctx.valueType? a = some (.int (if wide then 64 else 32)))
    (typeB : ctx.valueType? b = some (.int (if wide then 64 else 32)))
    (constantA : NonConstantSource ctx a) (constantB : NonConstantSource ctx b) :
    next.base.emitted.size = before.base.emitted.size+2 := by
  obtain ⟨producer,_,finish⟩ := ComparisonBranch.Calls.comparison_computed_emission inv calls source origin
    wide typeA typeB constantA constantB
  rw [finish]
  simp only [LState.emit,Array.size_push]

/-- The selected wide comparison branch on two nonconstant operands derives a complete
fragment with no virtual-register definitions. -/
theorem Calls.comparison_computed_no_defs {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat} (origin : ctx.defClif? c = some (.icmp cc ty a b))
    (wide : Bool)
    (typeA : ctx.valueType? a = some (.int (if wide then 64 else 32)))
    (typeB : ctx.valueType? b = some (.int (if wide then 64 else 32)))
    (constantA : NonConstantSource ctx a) (constantB : NonConstantSource ctx b) :
    ∃ code,Frag before.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  obtain ⟨producer,noDefs,finish⟩ := ComparisonBranch.Calls.comparison_computed_emission inv calls source
    origin wide typeA typeB constantA constantB
  refine ⟨[producer,.condBr calls.yes calls.no (.cond (condOf cc))],?_,?_⟩
  · rw [finish]
    exact (Frag.emit_nodef _ noDefs).append (Frag.emit_nodef _ rfl)
  · intro inst member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact noDefs
    · rfl

end Backend.Stock.Proof.ConditionalCalls

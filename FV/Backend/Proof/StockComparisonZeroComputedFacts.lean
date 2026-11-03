import FV.Backend.Proof.StockComparisonZeroFacts
import FV.Backend.Proof.StockComparisonZeroComputedSelection

/-! Zero comparison branches on a computed operand: emission facts (#140, CB-9).

`Calls.comparison_zero_emission` needs a source parameter as the first operand of
`icmp eq|ne x, (iconst 0)`. The parameter is used only to exclude the left-zero rules 5171/5173
of `emit_icmp` (term 652), which need `x` defined by an `iconst`. So a nonconstant `x`
(`NonConstantSource`) selects rule 5170 (`eq`) or 5172 (`ne`)
(`stock_cmp_zero_original_right_emitter_selected`), with any other definition. Their RHS calls
`is_nonzero x` (term 651). Its rules (`aarch64/inst.isle`):

* 4977 (`fits_in_32`): `NotZero (put_in_reg_zext32 x) Size32`, and 4979 (`I64`):
  `NotZero x Size64`. These are the selected rules for an i32 or i64 `x`.
* 4983 (`I128`) and 4988 (`I8`, `tst`): other types.
* 4993, 5013, 5032, 5049, 5058, 5077, 5094: `x` is the second result of `uadd_overflow`,
  `umul_overflow` or `smul_overflow`. The source subset has no such definition
  (`stock_overflow_flags_rule_unreachable` under `MappedCtxInv`).

No `is_nonzero` rule looks through a `band`, `icmp` or other definition of `x`, so
`stock_select_nonzero_wide_emitter_observed` holds for any source definition. The emission is one
`cbz`/`cbnz` on `x`'s register, with no virtual-register definitions. -/

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

/-- Actual 32/64-bit emit_icmp of `eq`/`ne` on a nonconstant operand and an
original zero constant selects the zero rule 5170 (`eq`) or 5172 (`ne`): the
left-zero rules need an `iconst` first operand. Its RHS calls `is_nonzero` on
the operand (rule 4977 at 32 bits, 4979 at 64 bits) and, for `eq`,
`cond_result_invert`. The result is a `Zero` (`eq`) or `NotZero` (`ne`)
condition on the operand's register with no instruction, and the compiler
state is unchanged except for operand demand marks. -/
private theorem zero_computed_comparison {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cc : Clif.IntCC} (equality : cc = .eq ∨ cc = .ne) (wide : Bool)
    {x y fuel : Nat}
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (notConstant : NonConstantSource ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    (zero : k = 0) (enough : 300 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) out (next,trace)) :
    ∃ key,ctx.valueReg? x = some (.vreg key .int) ∧
      out = .data 123 (if cc = .eq then 0 else 1) [.reg (.vreg key .int),.data 93 (if wide then 1 else 0) []] ∧
      next.base = st.base := by
  obtain ⟨j,info,defined,found,data,width⟩ := constant_source inv constY
  have normalized : u64 (imm64OfIconst ty' k) = 0 := by
    rw [u64_imm64OfIconst width,zero]
    rfl
  obtain ⟨n,gas⟩ : ∃ n,fuel = n+240 := ⟨fuel-240,by omega⟩
  rcases equality with rfl | rfl
  · obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_zero_original_right_emitter_selected data_program ctx inv false
      (by omega) notConstant defined found data normalized run
    simp only [Bool.false_eq_true,ite_false] at rhs
    rw [gas] at rhs
    obtain ⟨emitFuel,inverseFuel,raw,middle,middleTrace,enoughEmit,enoughInverse,emitter,inversion⟩ :=
      stock_cmp_zero32_eq_rhs_calls data_program ctx x n rhs
    obtain ⟨_,key,mapped,rawEq,middleEq⟩ :=
      ScalarSelect.stock_select_nonzero_wide_emitter_observed inv wide enoughEmit typeX emitter
    rw [rawEq] at inversion
    obtain ⟨outEq,nextEq⟩ := stock_cmp_zero_invert_observed data_program ctx enoughInverse true
      (.vreg key .int) (.data 93 (if wide then 1 else 0) []) inversion
    simp only [↓reduceIte]
    refine ⟨key,mapped,outEq,?_⟩
    rw [nextEq,middleEq]
    rfl
  · obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_zero_original_right_emitter_selected data_program ctx inv true
      (by omega) notConstant defined found data normalized run
    simp only [ite_true] at rhs
    rw [gas] at rhs
    obtain ⟨emitFuel,enoughEmit,emitter⟩ := stock_cmp_zero32_ne_rhs_calls data_program ctx x n rhs
    obtain ⟨_,key,mapped,rawEq,middleEq⟩ :=
      ScalarSelect.stock_select_nonzero_wide_emitter_observed inv wide enoughEmit typeX emitter
    simp only [reduceCtorEq,↓reduceIte]
    refine ⟨key,mapped,rawEq,?_⟩
    rw [middleEq]
    rfl

/-- Actual descriptor construction and emission of a `Zero`/`NotZero`
condition append exactly one `cbz`/`cbnz`. -/
private theorem zero_emission {ctx : Ctx} {constructFuel emitFuel : Nat}
    (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {cc : Clif.IntCC} (equality : cc = .eq ∨ cc = .ne) (wide : Bool) (key : Nat)
    {descriptor out : V} {yes no : Label} {before middle next : State}
    {trace constructTrace final : Array RuleId}
    (construct : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [.data 123 (if cc = .eq then 0 else 1) [.reg (.vreg key .int),.data 93 (if wide then 1 else 0) []],
        .label yes,.label no] (before,trace) descriptor (middle,constructTrace))
    (emit : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (middle,constructTrace) out (next,final)) :
    next.base = before.base.emit (.condBr yes no (if cc = .eq
      then .zero (.vreg key .int) (if wide then .size64 else .size32)
      else .notZero (.vreg key .int) (if wide then .size64 else .size32))) := by
  have decoded : OperandSize.ofIdx? (if wide then 1 else 0) =
      some (if wide then OperandSize.size64 else .size32) := by
    cases wide <;> rfl
  have projected := BranchHelpers.stock_emit_side_effect_projects ctx {} rfl (emitFuel+1)
    [descriptor] middle constructTrace
  have legacy : ApplyInternal program (Backend.sem ctx) {} emitFuel 13 242
      [descriptor] (middle.base,constructTrace) out (next.base,final) := by
    unfold ApplyInternal at emit ⊢
    rw [emit] at projected
    exact projected.symm
  rcases equality with rfl | rfl
  · simp only [↓reduceIte] at construct ⊢
    have shape : CondShape (.data 123 0 [.reg (.vreg key .int),.data 93 (if wide then 1 else 0) []])
        (fun _ => True) := .inl ⟨key,_,_,rfl,decoded,trivial⟩
    obtain ⟨base,descriptorEq⟩ := ConditionalValues.descriptor_shape rfl enoughConstruct shape construct
    rw [base,descriptorEq] at legacy
    dsimp only [brCondV] at legacy
    obtain ⟨inst,decodedInst,finish,_⟩ := emit_side_effect_inst_ok data_program rfl enoughEmit legacy
    rw [ofV_condBr_zero decoded] at decodedInst
    cases decodedInst
    exact finish
  · simp only [reduceCtorEq,↓reduceIte] at construct ⊢
    have shape : CondShape (.data 123 1 [.reg (.vreg key .int),.data 93 (if wide then 1 else 0) []])
        (fun _ => True) := .inr (.inl ⟨key,_,_,rfl,decoded,trivial⟩)
    obtain ⟨base,descriptorEq⟩ := ConditionalValues.descriptor_shape rfl enoughConstruct shape construct
    rw [base,descriptorEq] at legacy
    dsimp only [brCondV] at legacy
    obtain ⟨inst,decodedInst,finish,_⟩ := emit_side_effect_inst_ok data_program rfl enoughEmit legacy
    rw [ofV_condBr_notZero decoded] at decodedInst
    cases decodedInst
    exact finish

/-- The selected calls of a wide `eq`/`ne` comparison branch of a nonconstant
operand with an original zero constant append exactly one instruction:
`cbz x` for `eq` and `cbnz x` for `ne`, on the operand's register. Neither
the constant nor a flag producer is emitted. -/
theorem Calls.comparison_zero_computed_emission {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : ConditionalCalls.Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0) :
    ∃ key,ctx.valueReg? x = some (.vreg key .int) ∧
      next.base = before.base.emit (.condBr calls.yes calls.no (if cc = .eq
        then .zero (.vreg key .int) (if wide then .size64 else .size32)
        else .notZero (.vreg key .int) (if wide then .size64 else .size32))) := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  obtain ⟨helperFuel,helperTrace,enough,comparison⟩ :=
    comparison_condition_call inv origin calls.conditionEnough conditionRun
  obtain ⟨key,mapped,rawEq,middleBase⟩ :=
    zero_computed_comparison inv equality wide typeX constantX constY zero enough comparison
  have constructRun := calls.constructRun
  rw [rawEq] at constructRun
  have finish := zero_emission calls.constructEnough calls.emitEnough equality wide key
    constructRun calls.emitRun
  rw [middleBase] at finish
  exact ⟨key,mapped,finish⟩

end Backend.Stock.Proof.ComparisonBranch

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option autoImplicit false

/-- The selected wide `eq`/`ne` comparison branch of a nonconstant operand with
an original zero constant preserves both its allocation frontier and its
source-demand extent. -/
theorem Calls.comparison_zero_computed_bounds {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0) :
    next.base.nextVreg = before.base.nextVreg ∧ next.demand.size = before.demand.size := by
  have size := (Extent.apply_demand_size calls.emitRun).trans
    ((Extent.apply_demand_size calls.constructRun).trans (Extent.apply_demand_size calls.conditionRun))
  obtain ⟨key,_,finish⟩ := ComparisonBranch.Calls.comparison_zero_computed_emission inv calls source origin
    wide typeX constantX constY equality zero
  rw [finish]
  exact ⟨rfl,size⟩

/-- The selected wide `eq`/`ne` comparison branch of a nonconstant operand with
an original zero constant appends exactly one instruction (`cbz`/`cbnz`). -/
theorem Calls.comparison_zero_computed_emitted_size {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0) :
    next.base.emitted.size = before.base.emitted.size+1 := by
  obtain ⟨key,_,finish⟩ := ComparisonBranch.Calls.comparison_zero_computed_emission inv calls source origin
    wide typeX constantX constY equality zero
  rw [finish]
  simp only [LState.emit,Array.size_push]

private theorem condBr_no_defs (yes no : Label) (cc : Clif.IntCC) (key : Nat) (size : OperandSize) :
    vdefs (.condBr yes no (if cc = .eq then .zero (.vreg key .int) size
      else .notZero (.vreg key .int) size)) = [] := by
  split <;> rfl

/-- The selected wide `eq`/`ne` comparison branch of a nonconstant operand with
an original zero constant derives a complete fragment with no
virtual-register definitions. -/
theorem Calls.comparison_zero_computed_no_defs {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat} (origin : ctx.defClif? c = some (.icmp cc ty x y))
    (wide : Bool)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0) :
    ∃ code,Frag before.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  obtain ⟨key,_,finish⟩ := ComparisonBranch.Calls.comparison_zero_computed_emission inv calls source origin
    wide typeX constantX constY equality zero
  rw [finish]
  refine ⟨_,Frag.emit_nodef _ (condBr_no_defs _ _ _ _ _),?_⟩
  intro inst member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst member
  exact condBr_no_defs _ _ _ _ _

end Backend.Stock.Proof.ConditionalCalls

import FV.Backend.Lowering.StockComparisonComputedArgsLoopCfg
import FV.Backend.Proof.StockComparisonImmComputedCarry
import FV.Backend.Proof.StockComparisonComputedLoopClass

/-! Source facts of the loop class with computed comparisons and block arguments (#140, CB-9).

`ZeroOperand` states in source syntax that the first operand of a zero comparison is a computed
wide value: a parameter, or a typed result of a statement that is not an `iconst` and, unless the
comparison is `ne`, not a `band` (`ZeroResult`). `ComputedArgsCondition` states that a `brif`
condition is a result of an `icmp` whose operands are in the zero form `eq|ne x, (iconst 0)` with
a `ZeroOperand` `x` (`ZeroOperands`), in the 12-bit immediate form with a computed first operand
(`ImmOperands`), or in a form of `ComputedOperands` (CB-8). `ComputedArgsCondition.metadata`
derives the context metadata `ComputedArgsMetadata` from the syntax, SSA and the built context. `ComputedArgsTerms` are the terminators of the class: a `brif`
may pass any block arguments. The selector `ComparisonComputedArgsLoopCfg.sourceLeafEligible`
derives `ComputedArgsTerms`, the entry kind, the body families and the ABI
(`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.ComparisonComputedArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ComparisonLoopCfg Backend.Stock.Proof.ComparisonComputedLoopCfg
  Backend.Stock.Proof.ComparisonBranch Backend.Stock.Proof.ScalarCmp
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `x` is the result at index `m` of a statement of some block that is not an `iconst` and,
unless `cc` is `ne`, not a `band`, whose result type at `m` is `.i64` when `wide`, else `.i32`. -/
def ZeroResult (f : Clif.Function) (cc : Clif.IntCC) (x : Nat) (wide : Bool) : Prop :=
  ∃ (ibi i m : Nat) (ib : Clif.Block) (stm : Clif.Stmt) (tys : List Clif.Ty),
    f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧ stm.results[m]? = some x ∧
    stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
    tys[m]? = some (if wide then .i64 else .i32) ∧ (∀ (ty : Clif.Ty) (k : BitVec ty.width),stm.inst ≠ .iconst ty k) ∧
    (cc = .ne ∨ ∀ (ty : Clif.Ty) (a b : Nat),stm.inst ≠ .binary .band ty a b)

/-- The first operand of a zero comparison: a wide parameter, or a `ZeroResult`. -/
def ZeroOperand (f : Clif.Function) (cc : Clif.IntCC) (x : Nat) (wide : Bool) : Prop :=
  WideParameter f x wide ∨ ZeroResult f cc x wide

/-- The operands of `icmp cc _ x y` in the zero form: `cc` is `eq` or `ne`, `x` is a
`ZeroOperand`, and `y` is a result of `iconst 0`. -/
def ZeroOperands (f : Clif.Function) (cc : Clif.IntCC) (x y : Nat) : Prop :=
  (cc = .eq ∨ cc = .ne) ∧ (∃ wide,ZeroOperand f cc x wide) ∧
    ∃ (ty' : Clif.Ty) (k : BitVec ty'.width),ConstantResult f y ty' k ∧ k = 0

/-- The operands of `icmp cc _ x y` in the 12-bit immediate form: `x` is a computed wide value
(`ComputedValue`), and `y` is a result of an encodable 12-bit `iconst k`, `k ≠ 0` for
`eq`/`ne`. -/
def ImmOperands (f : Clif.Function) (cc : Clif.IntCC) (x y : Nat) : Prop :=
  ∃ (wide : Bool) (ty' : Clif.Ty) (k : BitVec ty'.width) (imm : Imm12),ComputedValue f x wide ∧
    ConstantResult f y ty' k ∧ Imm12.ofNat? k.toNat = some imm ∧ (cc = .eq ∨ cc = .ne → k ≠ 0)

/-- The operands of `icmp cc _ x y`: the zero or 12-bit immediate form with a computed first
operand, or a form of `ComputedOperands`. -/
def ComputedArgsOperands (f : Clif.Function) (cc : Clif.IntCC) (x y : Nat) : Prop :=
  ZeroOperands f cc x y ∨ ImmOperands f cc x y ∨ ComputedOperands f cc x y

/-- `c` is a result of an `icmp` statement of some block, with operands in
`ComputedArgsOperands`. -/
def ComputedArgsCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (bi j : Nat) (b : Clif.Block) (stm : Clif.Stmt) (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),
    f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧ c ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
    ComputedArgsOperands f cc x y

/-- A branch of the class: any block arguments, and a wide parameter or a comparison as the
condition. -/
def ComputedArgsBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ (ParameterCondition f c ∨ ComputedArgsCondition f c)

/-- Every block jumps, returns, branches as `ComputedArgsBranch`, or ends in `trap`. -/
def ComputedArgsTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ComputedArgsBranch f b ∨ ∃ c,b.term = .trap c

/-- A `ZeroResult` has its width, is nonconstant, and, unless `cc` is `ne`, is not a `band`
result in the built context. -/
theorem ZeroResult.metadata {f : Clif.Function} {cc : Clif.IntCC} {x : Nat} {wide : Bool}
    (computed : ZeroResult f cc x wide) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧ NonConstantSource ctx x ∧
      (cc = .ne ∨ NonBandSource ctx x) := by
  obtain ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,typesEq,typeAt,notConstant,notBand⟩ := computed
  have metadata := ComputedResult.metadata ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,typesEq,typeAt,notConstant⟩
    scope dominated build
  refine ⟨metadata.1,metadata.2,notBand.imp id ?_⟩
  intro notBand j info defined found ty a b band
  have origin := ComparisonLoopCfg.statement_metadata dominated block lookup
    (List.mem_of_getElem? resultAt) build
  have here : ctx.defClif? x = some (.binary .band ty a b) := by
    simp [Ctx.defClif?,defined,found,band]
  rw [origin] at here
  exact notBand ty a b (Option.some.inj here)

/-- A `ZeroOperand` has its width, is nonconstant, and, unless `cc` is `ne`, is not a `band`
result in the built context. -/
theorem ZeroOperand.metadata {f : Clif.Function} {cc : Clif.IntCC} {x : Nat} {wide : Bool}
    (computed : ZeroOperand f cc x wide) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧ NonConstantSource ctx x ∧
      (cc = .ne ∨ NonBandSource ctx x) := by
  rcases computed with parameter | result
  · have metadata := parameter.metadata dominated build
    exact ⟨metadata.1,nonconstant_of_parameter metadata.2,Or.inr (nonband_of_parameter metadata.2)⟩
  · exact result.metadata scope dominated build

/-- **Per-block condition metadata.** The source syntax of a computed comparison condition and
SSA derive the built context's metadata `ComputedArgsMetadata`. -/
theorem ComputedArgsCondition.metadata {f : Clif.Function} {c : Nat}
    (condition : ComputedArgsCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : ComputedArgsMetadata ctx c := by
  obtain ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,operands⟩ := condition
  have origin : ctx.defClif? c = some (.icmp cc ty x y) := by
    rw [← inst]
    exact ComparisonLoopCfg.statement_metadata dominated block lookup result build
  have constant : ∀ {ty' : Clif.Ty} {k : BitVec ty'.width},ConstantResult f y ty' k →
      ctx.defClif? y = some (.iconst ty' k) := by
    intro ty' k defined
    obtain ⟨ibi,i,ib,constant,constantBlock,constantLookup,constantResult,constantInst⟩ := defined
    rw [← constantInst]
    exact ComparisonLoopCfg.statement_metadata dominated constantBlock constantLookup constantResult build
  rcases operands with ⟨equality,⟨wide,operandX⟩,ty',k,constY,zero⟩ |
    ⟨wide,ty',k,imm,computedX,constY,fits,nonzero⟩ | operands
  · obtain ⟨typeX,constantX,bandX⟩ := operandX.metadata scope dominated build
    exact Or.inr (Or.inl ⟨cc,ty,x,y,wide,ty',k,origin,typeX,constantX,bandX,constant constY,equality,zero⟩)
  · obtain ⟨typeX,constantX⟩ := computedX.metadata scope dominated build
    exact Or.inl ⟨cc,ty,x,y,wide,ty',k,imm,origin,typeX,constantX,constant constY,fits,nonzero⟩
  · exact Or.inr (Or.inr (ComputedCondition.metadata ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,operands⟩
      scope dominated build))

/-- **Per-block condition metadata.** A branch condition of the class has, in the built context,
the metadata of a wide parameter or `ComputedArgsMetadata`. -/
theorem condition_metadata {f : Clif.Function} {c : Nat}
    (condition : ParameterCondition f c ∨ ComputedArgsCondition f c) (scope : LowerScope f)
    (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    (ctx.defInst? c = none ∧ (ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64))) ∨
      ComputedArgsMetadata ctx c := by
  rcases condition with parameter | comparison
  · exact Or.inl (parameter_metadata parameter dominated.ssa build)
  · exact Or.inr (comparison.metadata scope dominated build)

end Backend.Stock.Proof.ComparisonComputedArgsLoopCfg

namespace Backend.Stock.ComparisonComputedArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ComparisonLoopCfg
  Backend.Stock.Proof.ComparisonComputedLoopCfg Backend.Stock.Proof.ComparisonComputedArgsLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem parameter_of_sound {f : Clif.Function} {x : Nat} {wide : Bool}
    (checked : ComparisonLoopCfg.parameterOf f x (if wide then .i64 else .i32) = true) :
    Proof.ComparisonLoopCfg.WideParameter f x wide := by
  obtain ⟨pb,member,present⟩ := List.any_eq_true.mp checked
  obtain ⟨pbi,block⟩ := List.mem_iff_getElem?.mp member
  exact ⟨pbi,pb,block,List.contains_iff_mem.mp present⟩

private theorem statement_of_sound {f : Clif.Function} {eligible : Clif.Stmt → Bool}
    (checked : ComparisonLoopCfg.statementOf f eligible = true) :
    ∃ (ibi i : Nat) (ib : Clif.Block) (stm : Clif.Stmt),f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧
      eligible stm = true := by
  obtain ⟨ib,member,present⟩ := List.any_eq_true.mp checked
  obtain ⟨ibi,block⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨stm,statement,good⟩ := List.any_eq_true.mp present
  obtain ⟨i,lookup⟩ := List.mem_iff_getElem?.mp statement
  exact ⟨ibi,i,ib,stm,block,lookup,good⟩

/-- The executable zero check derives the source `iconst 0` fact. -/
private theorem zero_constant_sound {f : Clif.Function} {y : Nat}
    (checked : ComparisonLoopCfg.statementOf f (ComparisonZeroCfg.constantEligible y) = true) :
    ∃ (ty' : Clif.Ty) (k : BitVec ty'.width),Proof.ComparisonLoopCfg.ConstantResult f y ty' k ∧ k = 0 := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [ComparisonZeroCfg.constantEligible,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨result,value⟩ := good
  cases inst : stm.inst <;> simp only [inst] at value
  case iconst ty' k => exact ⟨ty',k,⟨ibi,i,ib,stm,block,lookup,result,inst⟩,beq_iff_eq.mp value⟩
  all_goals cases value

/-- The executable immediate check derives the source `iconst` fact. -/
private theorem imm_constant_sound {f : Clif.Function} {cc : Clif.IntCC} {y : Nat}
    (checked : ComparisonLoopCfg.statementOf f (ComparisonImmCfg.constantEligible cc y) = true) :
    ∃ (ty' : Clif.Ty) (k : BitVec ty'.width) (imm : Imm12),Proof.ComparisonLoopCfg.ConstantResult f y ty' k ∧
      Imm12.ofNat? k.toNat = some imm ∧ (cc = .eq ∨ cc = .ne → k ≠ 0) := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [ComparisonImmCfg.constantEligible,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨result,value⟩ := good
  cases inst : stm.inst <;> simp only [inst] at value
  case iconst ty' k =>
    simp only [Bool.and_eq_true] at value
    obtain ⟨fits,nonzero⟩ := value
    obtain ⟨imm,fits⟩ := Option.isSome_iff_exists.mp fits
    refine ⟨ty',k,imm,⟨ibi,i,ib,stm,block,lookup,result,inst⟩,fits,?_⟩
    intro equality
    rcases equality with rfl | rfl <;> simpa using nonzero
  all_goals cases value

/-- The executable computed-result check derives the source result fact. -/
private theorem computed_result_sound {f : Clif.Function} {x : Nat} {wide : Bool}
    (checked : ComparisonLoopCfg.statementOf f
      (ComparisonComputedLoopCfg.computedResult f x (if wide then .i64 else .i32)) = true) :
    ComputedResult f x wide := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [ComparisonComputedLoopCfg.computedResult,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨notConstant,member⟩ := good
  obtain ⟨m,pair⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨resultAt,typeAt⟩ := List.getElem?_zip_eq_some.mp pair
  cases types : stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | none => simp [ComparisonComputedLoopCfg.resultTypesOf,types] at typeAt
  | some tys =>
    simp only [ComparisonComputedLoopCfg.resultTypesOf,types,Option.getD_some] at typeAt
    refine ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,types,typeAt,?_⟩
    intro ty k constant
    rw [constant] at notConstant
    cases notConstant

private theorem computed_of_sound {f : Clif.Function} {x : Nat} {wide : Bool}
    (checked : ComparisonComputedLoopCfg.computedOf f x (if wide then .i64 else .i32) = true) :
    ComputedValue f x wide := by
  simp only [ComparisonComputedLoopCfg.computedOf,Bool.or_eq_true] at checked
  rcases checked with parameter | result
  · exact Or.inl (parameter_of_sound parameter)
  · exact Or.inr (computed_result_sound result)

/-- The executable immediate comparison check derives the source immediate comparison fact. -/
private theorem imm_sound {f : Clif.Function} {c : Nat} {stm : Clif.Stmt}
    (checked : immEligible f c stm = true) :
    ∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),c ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
      ImmOperands f cc x y := by
  simp only [immEligible,Bool.and_eq_true,List.contains_iff_mem] at checked
  obtain ⟨result,operands⟩ := checked
  cases inst : stm.inst <;> simp only [inst] at operands
  case icmp cc ty x y =>
    refine ⟨cc,ty,x,y,result,rfl,?_⟩
    simp only [Bool.or_eq_true,Bool.and_eq_true] at operands
    obtain ⟨first,immediate⟩ := operands
    obtain ⟨ty',k,imm,constY,fits,nonzero⟩ := imm_constant_sound immediate
    rcases first with narrowX | wideX
    · exact ⟨false,ty',k,imm,computed_of_sound narrowX,constY,fits,nonzero⟩
    · exact ⟨true,ty',k,imm,computed_of_sound wideX,constY,fits,nonzero⟩
  all_goals cases operands

/-- The executable result check derives the source result fact. -/
private theorem zero_result_sound {f : Clif.Function} {cc : Clif.IntCC} {x : Nat} {wide : Bool}
    (checked : ComparisonLoopCfg.statementOf f (zeroResult f cc x (if wide then .i64 else .i32)) = true) :
    ZeroResult f cc x wide := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [zeroResult,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨kind,member⟩ := good
  obtain ⟨m,pair⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨resultAt,typeAt⟩ := List.getElem?_zip_eq_some.mp pair
  cases types : stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | none => simp [ComparisonComputedLoopCfg.resultTypesOf,types] at typeAt
  | some tys =>
    simp only [ComparisonComputedLoopCfg.resultTypesOf,types,Option.getD_some] at typeAt
    refine ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,types,typeAt,?_,?_⟩
    · intro ty k constant
      rw [constant] at kind
      cases kind
    · by_cases band : ∃ (ty : Clif.Ty) (a b : Nat),stm.inst = .binary .band ty a b
      · obtain ⟨ty,a,b,band⟩ := band
        rw [band] at kind
        exact Or.inl (beq_iff_eq.mp kind)
      · exact Or.inr fun ty a b same => band ⟨ty,a,b,same⟩

private theorem zero_operand_sound {f : Clif.Function} {cc : Clif.IntCC} {x : Nat} {wide : Bool}
    (checked : zeroOperandOf f cc x (if wide then .i64 else .i32) = true) : ZeroOperand f cc x wide := by
  simp only [zeroOperandOf,Bool.or_eq_true] at checked
  rcases checked with parameter | result
  · exact Or.inl (parameter_of_sound parameter)
  · exact Or.inr (zero_result_sound result)

/-- The executable zero comparison check derives the source zero comparison fact. -/
private theorem zero_sound {f : Clif.Function} {c : Nat} {stm : Clif.Stmt}
    (checked : zeroEligible f c stm = true) :
    ∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),c ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
      ZeroOperands f cc x y := by
  simp only [zeroEligible,Bool.and_eq_true,List.contains_iff_mem] at checked
  obtain ⟨result,operands⟩ := checked
  cases inst : stm.inst <;> simp only [inst] at operands
  case icmp cc ty x y =>
    refine ⟨cc,ty,x,y,result,rfl,?_⟩
    simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at operands
    obtain ⟨⟨equality,first⟩,zeroCheck⟩ := operands
    obtain ⟨ty',k,constY,zero⟩ := zero_constant_sound zeroCheck
    refine ⟨equality,?_,ty',k,constY,zero⟩
    rcases first with narrowX | wideX
    · exact ⟨false,zero_operand_sound narrowX⟩
    · exact ⟨true,zero_operand_sound wideX⟩
  all_goals cases operands

/-- The executable condition check of block `b` derives a parameter or computed comparison
condition. -/
theorem condition_sound {f : Clif.Function} {bi : Nat} {b : Clif.Block} {c : Nat}
    (block : f.blocks[bi]? = some b) (checked : conditionEligible f b c = true) :
    Proof.ParameterCfg.ParameterCondition f c ∨ ComputedArgsCondition f c := by
  simp only [conditionEligible,Bool.or_eq_true] at checked
  rcases checked with (computed | zero) | immediate
  · rcases ComparisonComputedLoopCfg.condition_sound block computed with parameter | comparison
    · exact Or.inl parameter
    · obtain ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,operands⟩ := comparison
      exact Or.inr ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,Or.inr (Or.inr operands)⟩
  · obtain ⟨stm,member,good⟩ := List.any_eq_true.mp zero
    obtain ⟨j,lookup⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨cc,ty,x,y,result,inst,operands⟩ := zero_sound good
    exact Or.inr ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,Or.inl operands⟩
  · obtain ⟨stm,member,good⟩ := List.any_eq_true.mp immediate
    obtain ⟨j,lookup⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨cc,ty,x,y,result,inst,operands⟩ := imm_sound good
    exact Or.inr ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,Or.inr (Or.inl operands)⟩

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ComputedArgsBranch f b ∨
      (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨condition,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,condition_sound block condition⟩))
  all_goals simp only [controlLeafEligible,controlEligible] at checked; cases checked

/-- **The selector's source facts.** The selector derives the terminators, the entry kind, the
body families and the ABI. -/
theorem source_leaf_eligible_facts {f : Clif.Function} (checked : sourceLeafEligible f = true) :
    ComputedArgsTerms f ∧ (∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c) ∧
    (∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) ∧
    f.sig.params.all Scalar.narrowAbiEligible = true ∧ f.sig.returns.all Scalar.narrowAbiEligible = true := by
  simp only [sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  have each : ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b → controlLeafEligible f bi b b.term = true := by
    intro bi b found
    exact List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  refine ⟨?_,?_,?_,params,returns⟩
  · intro bi b found
    rcases control_leaf_facts found (each bi b found) with jump | ret | branch | ⟨c,trap,_⟩
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)
    · exact Or.inr (Or.inr (Or.inl branch))
    · exact Or.inr (Or.inr (Or.inr ⟨c,trap⟩))
  · intro b found c trap
    rcases control_leaf_facts found (each 0 b found) with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c',yes,no,branch,_⟩ | ⟨c',trap',entry⟩
    · rw [trap] at jump; cases jump
    · rw [trap] at ret; cases ret
    · rw [trap] at branch; cases branch
    · exact entry rfl
  · intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

end Backend.Stock.ComparisonComputedArgsLoopCfg

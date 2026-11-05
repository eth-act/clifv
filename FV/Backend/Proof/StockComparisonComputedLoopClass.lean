import FV.Backend.Lowering.StockComparisonComputedLoopCfg
import FV.Backend.Proof.StockComparisonComputedCarry
import FV.Backend.Proof.StockComparisonLoopClass

/-! Source facts of the computed comparison loop class (#140, CB-8).

`ComputedCondition` states in source syntax that a `brif` condition is a result of an `icmp`
whose operands are two computed values of one wide type (`ComputedValue`: a parameter, or a
typed result of a statement other than `iconst`), or are in one of the three forms of
`ComparisonOperands`. `ComputedCondition.metadata` derives the context metadata
`ComputedMetadata` from the syntax, SSA and the built context. `LoopTerms` are the terminators of
the loop class. The selector `ComparisonComputedLoopCfg.sourceLeafEligible` derives `LoopTerms`,
the entry kind, the body families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.ComparisonComputedLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ParameterCfg
open Backend.Stock.Proof.ScalarCmp
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `x` is the result at index `m` of a statement of some block other than an `iconst`, whose
result type at `m` is `.i64` when `wide`, else `.i32`. -/
def ComputedResult (f : Clif.Function) (x : Nat) (wide : Bool) : Prop :=
  ∃ (ibi i m : Nat) (ib : Clif.Block) (stm : Clif.Stmt) (tys : List Clif.Ty),
    f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧ stm.results[m]? = some x ∧
    stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
    tys[m]? = some (if wide then .i64 else .i32) ∧ ∀ (ty : Clif.Ty) (k : BitVec ty.width),stm.inst ≠ .iconst ty k

/-- `x` is a computed value of one wide type: a parameter of some block, or a typed result of a
statement other than `iconst`. -/
def ComputedValue (f : Clif.Function) (x : Nat) (wide : Bool) : Prop :=
  ComparisonLoopCfg.WideParameter f x wide ∨ ComputedResult f x wide

/-- The operands of `icmp cc _ x y`: two computed values of one wide type, or one of the three
forms of `ComparisonOperands`. -/
def ComputedOperands (f : Clif.Function) (cc : Clif.IntCC) (x y : Nat) : Prop :=
  (∃ wide,ComputedValue f x wide ∧ ComputedValue f y wide) ∨ ComparisonLoopCfg.ComparisonOperands f cc x y

/-- `c` is a result of an `icmp` statement of some block, with operands in `ComputedOperands`. -/
def ComputedCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (bi j : Nat) (b : Clif.Block) (stm : Clif.Stmt) (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),
    f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧ c ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
    ComputedOperands f cc x y

/-- A branch of the loop class: empty arguments, and a wide parameter or a comparison as the
condition. -/
def LoopBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ yes.args = [] ∧ no.args = [] ∧
    (ParameterCondition f c ∨ ComputedCondition f c)

/-- Every block jumps, returns, branches as `LoopBranch`, or ends in `trap`. -/
def LoopTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ LoopBranch f b ∨ ∃ c,b.term = .trap c

/-- A typed result of a statement other than `iconst` has its width and is nonconstant in the
built context. -/
theorem ComputedResult.metadata {f : Clif.Function} {x : Nat} {wide : Bool}
    (computed : ComputedResult f x wide) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧ NonConstantSource ctx x := by
  obtain ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,typesEq,typeAt,notConstant⟩ := computed
  have result : x ∈ stm.results := List.mem_of_getElem? resultAt
  have origin := ComparisonLoopCfg.statement_metadata dominated block lookup result build
  have inv := buildCtx_mappedInv scope build
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨info,originalFound,clif,results⟩ := spec.facts.stmt ibi ib i stm block lookup
  have found : ctx.insts[blockStart f ibi+i]? = some info := by rw [view.insts]; exact originalFound
  obtain ⟨tys',typesEq',resTys,_⟩ := inv.resTys _ info stm.inst found clif
  rw [typesEq] at typesEq'
  cases typesEq'
  have resTypeAt : info.resTys[m]? = some (CTy.ofClif (if wide then .i64 else .i32)) := by
    rw [resTys,List.getElem?_map,typeAt]
    rfl
  have infoResult : info.results[m]? = some x := by rw [results]; exact resultAt
  have typed := (spec.facts.types dominated.ssa).1 _ info originalFound m x _ infoResult resTypeAt
  have width : CTy.ofClif (if wide then .i64 else .i32) = .int (if wide then 64 else 32) := by
    cases wide <;> rfl
  refine ⟨by simpa only [Ctx.valueType?,view.valTy,width] using typed,?_⟩
  intro j info' defined found' ty k constant
  have here : ctx.defClif? x = some (.iconst ty k) := by
    simp [Ctx.defClif?,defined,found',constant]
  rw [origin] at here
  exact notConstant ty k (Option.some.inj here)

/-- A computed value has its width and is nonconstant in the built context. -/
theorem ComputedValue.metadata {f : Clif.Function} {x : Nat} {wide : Bool}
    (computed : ComputedValue f x wide) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧ NonConstantSource ctx x := by
  rcases computed with parameter | result
  · have metadata := parameter.metadata dominated build
    exact ⟨metadata.1,ComparisonBranch.nonconstant_of_parameter metadata.2⟩
  · exact result.metadata scope dominated build

/-- **Per-block condition metadata.** The source syntax of a computed comparison condition and
SSA derive the built context's metadata `ComputedMetadata`. -/
theorem ComputedCondition.metadata {f : Clif.Function} {c : Nat}
    (condition : ComputedCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : ComputedMetadata ctx c := by
  obtain ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,operands⟩ := condition
  rcases operands with ⟨wide,computedX,computedY⟩ | operands
  · have origin : ctx.defClif? c = some (.icmp cc ty x y) := by
      rw [← inst]
      exact ComparisonLoopCfg.statement_metadata dominated block lookup result build
    have metaX := computedX.metadata scope dominated build
    have metaY := computedY.metadata scope dominated build
    exact Or.inl ⟨cc,ty,x,y,wide,origin,metaX.1,metaY.1,metaX.2,metaY.2⟩
  · exact Or.inr (ComparisonLoopCfg.ComparisonCondition.metadata
      ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,operands⟩ dominated build)

end Backend.Stock.Proof.ComparisonComputedLoopCfg

namespace Backend.Stock.ComparisonComputedLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ComparisonComputedLoopCfg
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

/-- The executable comparison check derives the source comparison fact. -/
private theorem legacy_comparison_sound {f : Clif.Function} {c : Nat} {stm : Clif.Stmt}
    (checked : ComparisonLoopCfg.comparisonEligible f c stm = true) :
    ∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),c ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
      Proof.ComparisonLoopCfg.ComparisonOperands f cc x y := by
  simp only [ComparisonLoopCfg.comparisonEligible,Bool.and_eq_true,List.contains_iff_mem] at checked
  obtain ⟨result,operands⟩ := checked
  cases inst : stm.inst <;> simp only [inst] at operands
  case icmp cc ty x y =>
    refine ⟨cc,ty,x,y,result,rfl,?_⟩
    simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at operands
    rcases operands with (⟨narrowX,narrowY⟩ | ⟨wideX,wideY⟩) | ⟨parameter,constants⟩
    · exact Or.inl ⟨false,parameter_of_sound narrowX,parameter_of_sound narrowY⟩
    · exact Or.inl ⟨true,parameter_of_sound wideX,parameter_of_sound wideY⟩
    · have first : ∃ wide,Proof.ComparisonLoopCfg.WideParameter f x wide := by
        rcases parameter with narrowX | wideX
        · exact ⟨false,parameter_of_sound narrowX⟩
        · exact ⟨true,parameter_of_sound wideX⟩
      obtain ⟨wide,parameterX⟩ := first
      rcases constants with immediate | ⟨equality,zeroCheck⟩
      · obtain ⟨ty',k,imm,constY,fits,nonzero⟩ := imm_constant_sound immediate
        exact Or.inr (Or.inl ⟨wide,ty',k,imm,parameterX,constY,fits,nonzero⟩)
      · obtain ⟨ty',k,constY,zero⟩ := zero_constant_sound zeroCheck
        exact Or.inr (Or.inr ⟨wide,ty',k,parameterX,constY,equality,zero⟩)
  all_goals cases operands

/-- The executable result check derives the source result fact. -/
private theorem computed_result_sound {f : Clif.Function} {x : Nat} {wide : Bool}
    (checked : ComparisonLoopCfg.statementOf f (computedResult f x (if wide then .i64 else .i32)) = true) :
    ComputedResult f x wide := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [computedResult,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨notConstant,member⟩ := good
  obtain ⟨m,pair⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨resultAt,typeAt⟩ := List.getElem?_zip_eq_some.mp pair
  cases types : stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | none => simp [resultTypesOf,types] at typeAt
  | some tys =>
    simp only [resultTypesOf,types,Option.getD_some] at typeAt
    refine ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,types,typeAt,?_⟩
    intro ty k constant
    rw [constant] at notConstant
    cases notConstant

private theorem computed_of_sound {f : Clif.Function} {x : Nat} {wide : Bool}
    (checked : computedOf f x (if wide then .i64 else .i32) = true) : ComputedValue f x wide := by
  simp only [computedOf,Bool.or_eq_true] at checked
  rcases checked with parameter | result
  · exact Or.inl (parameter_of_sound parameter)
  · exact Or.inr (computed_result_sound result)

/-- The executable comparison check derives the source comparison fact. -/
private theorem comparison_sound {f : Clif.Function} {c : Nat} {stm : Clif.Stmt}
    (checked : comparisonEligible f c stm = true) :
    ∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),c ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
      ComputedOperands f cc x y := by
  simp only [comparisonEligible,Bool.or_eq_true] at checked
  rcases checked with legacy | computed
  · obtain ⟨cc,ty,x,y,result,inst,operands⟩ := legacy_comparison_sound legacy
    exact ⟨cc,ty,x,y,result,inst,Or.inr operands⟩
  · simp only [Bool.and_eq_true,List.contains_iff_mem] at computed
    obtain ⟨result,operands⟩ := computed
    cases inst : stm.inst <;> simp only [inst] at operands
    case icmp cc ty x y =>
      refine ⟨cc,ty,x,y,result,rfl,Or.inl ?_⟩
      simp only [Bool.or_eq_true,Bool.and_eq_true] at operands
      rcases operands with ⟨narrowX,narrowY⟩ | ⟨wideX,wideY⟩
      · exact ⟨false,computed_of_sound narrowX,computed_of_sound narrowY⟩
      · exact ⟨true,computed_of_sound wideX,computed_of_sound wideY⟩
    all_goals cases operands

private theorem parameter_eligible_sound {f : Clif.Function} {c : Nat}
    (checked : ParameterCfg.parameterEligible f c = true) : Proof.ParameterCfg.ParameterCondition f c := by
  obtain ⟨b,member,eligible⟩ := List.any_eq_true.mp checked
  obtain ⟨bi,block⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨pair,parameter,good⟩ := List.any_eq_true.mp eligible
  obtain ⟨value,ty⟩ := pair
  change (value == c && (ty == .i32 || ty == .i64)) = true at good
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at good
  obtain ⟨same,wide⟩ := good
  subst value
  exact ⟨bi,b,ty,block,parameter,wide⟩

/-- The executable condition check of block `b` derives a parameter or computed comparison
condition. -/
theorem condition_sound {f : Clif.Function} {bi : Nat} {b : Clif.Block} {c : Nat}
    (block : f.blocks[bi]? = some b) (checked : conditionEligible f b c = true) :
    Proof.ParameterCfg.ParameterCondition f c ∨ ComputedCondition f c := by
  simp only [conditionEligible,Bool.or_eq_true] at checked
  rcases checked with parameter | comparison
  · exact Or.inl (parameter_eligible_sound parameter)
  · obtain ⟨stm,member,good⟩ := List.any_eq_true.mp comparison
    obtain ⟨j,lookup⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨cc,ty,x,y,result,inst,operands⟩ := comparison_sound good
    exact Or.inr ⟨bi,j,b,stm,cc,ty,x,y,block,lookup,result,inst,operands⟩

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ LoopBranch f b ∨
      (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,List.isEmpty_iff.mp yesEmpty,List.isEmpty_iff.mp noEmpty,
      condition_sound block condition⟩))
  all_goals simp only [controlLeafEligible,controlEligible] at checked; cases checked

/-- **The selector's source facts.** The computed comparison loop selector derives the
terminators, the entry kind, the body families and the ABI. -/
theorem source_leaf_eligible_facts {f : Clif.Function} (checked : sourceLeafEligible f = true) :
    LoopTerms f ∧ (∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c) ∧
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

end Backend.Stock.ComparisonComputedLoopCfg

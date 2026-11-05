import FV.Backend.Lowering.StockGeneralLoopCfg5
import FV.Backend.Proof.StockBranchCond5Carry
import FV.Backend.Proof.StockGeneralArgsLoopClass4

/-! Source facts of the loop classes with one-bit tests and zero extensions as conditions
(#140, CB-13).

The source syntax of the new conditions: a one-bit test (`TestBitCondition`: `c = band x k`,
`k = iconst imm`, and `imm` has one set bit below the width of a declared type of `x`), a zero
test of a one-bit mask (`TestBitZeroCondition`), a zero extension of a comparison of two wide
parameters of one width (`UextComparisonCondition`), and a plain zero extension
(`UextPlainCondition`: an `i16`, `i32` or `i64` result of `uextend x`, `x` a parameter or a result
of a statement that is not an `icmp`). Their `metadata` theorems derive the context metadata from
the syntax, SSA and the built context: `TestBitMetadata`, `TestBitZeroMetadata`,
`UextComparisonMetadata`, and the plain forms of `GeneralCondMetadata4` (no lowering rule looks
through a plain zero extension). A condition of the classes is a condition of
`GeneralArgsLoopCfg4` or one of the new forms (`GeneralCondition`); `condition_metadata` gives its
`BranchCondMetadata5`.

`GeneralArgsTerms` are the terminators of the split class `GeneralArgsLoopCfg5`, `GeneralTerms`
those of the legacy class `GeneralLoopCfg5`. The selectors derive the terminators, the entry kind,
the body families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.GeneralArgsLoopCfg5
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.PlainBranch
  Backend.Stock.Proof.TestBitBranch Backend.Stock.GeneralArgsLoopCfg5
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `v` is a result of a statement of some block whose instruction is `inst`. -/
def DefinedBy (f : Clif.Function) (v : Nat) (inst : Clif.Inst) : Prop :=
  ∃ (ibi i : Nat) (ib : Clif.Block) (stm : Clif.Stmt),
    f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧ v ∈ stm.results ∧ stm.inst = inst

/-- `v` is a result at index `m` of a statement of some block, of type `ty`. -/
def TypedResult (f : Clif.Function) (v : Nat) (ty : Clif.Ty) (stm : Clif.Stmt) : Prop :=
  ∃ (ibi i m : Nat) (ib : Clif.Block) (tys : List Clif.Ty),
    f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧ stm.results[m]? = some v ∧
    stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
    tys[m]? = some ty

/-- `x` is declared with type `ty`: a parameter of type `ty` of some block, or a result of type `ty`
of a statement of some block. -/
def Declared (f : Clif.Function) (x : Nat) (ty : Clif.Ty) : Prop :=
  (∃ (pbi : Nat) (pb : Clif.Block),f.blocks[pbi]? = some pb ∧ (x,ty) ∈ pb.params) ∨
    ∃ stm,TypedResult f x ty stm

/-- `c` is a one-bit test `band x k` with `k = iconst imm`, and `imm` has the single set bit `bit`
below the width of a declared type of `x`. -/
def TestBitCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (ty : Clif.Ty) (x k : Nat) (ty' : Clif.Ty) (imm : BitVec ty'.width) (tx : Clif.Ty) (bit : Nat),
    DefinedBy f c (.binary .band ty x k) ∧ DefinedBy f k (.iconst ty' imm) ∧ Declared f x tx ∧
    singleBit tx.width ((u64 (imm64OfIconst ty' imm) : Nat) : Int) = some bit

/-- `c` is a zero test `icmp eq y z` of a one-bit test `y`, with `z = iconst 0`. -/
def TestBitZeroCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (tyc : Clif.Ty) (y z : Nat) (ty0 : Clif.Ty) (imm0 : BitVec ty0.width),
    DefinedBy f c (.icmp .eq tyc y z) ∧ TestBitCondition f y ∧ DefinedBy f z (.iconst ty0 imm0) ∧ imm0 = 0

/-- `c` is a zero extension `uextend z` of a comparison `z = icmp cc x, y` of two parameters of one
wide type. -/
def UextComparisonCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (target : Clif.Ty) (z : Nat) (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool),
    DefinedBy f c (.extend .uextend target z) ∧ DefinedBy f z (.icmp cc ty x y) ∧
    ComparisonLoopCfg.WideParameter f x wide ∧ ComparisonLoopCfg.WideParameter f y wide

/-- `x` is a parameter of some block, or a result of a statement that is not an `icmp`. -/
def NonComparisonOperand (f : Clif.Function) (x : Nat) : Prop :=
  (∃ (pbi : Nat) (pb : Clif.Block) (ty : Clif.Ty),f.blocks[pbi]? = some pb ∧ (x,ty) ∈ pb.params) ∨
    ∃ (ibi i : Nat) (ib : Clif.Block) (stm : Clif.Stmt),f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧
      x ∈ stm.results ∧ ∀ (cc : Clif.IntCC) (ty : Clif.Ty) (a b : Nat),stm.inst ≠ .icmp cc ty a b

/-- `c` is a plain zero extension: an `i16`, `i32` or `i64` result of `uextend x` with `x` not a
comparison. -/
def UextPlainCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (stm : Clif.Stmt) (ty target : Clif.Ty) (x : Nat),TypedResult f c ty stm ∧
    (ty = .i16 ∨ ty = .i32 ∨ ty = .i64) ∧ stm.inst = .extend .uextend target x ∧ NonComparisonOperand f x

/-- A condition of the classes: a condition of `GeneralArgsLoopCfg4`, or one of the new forms. -/
def GeneralCondition (f : Clif.Function) (c : Nat) : Prop :=
  GeneralArgsLoopCfg4.GeneralCondition f c ∨ TestBitCondition f c ∨ TestBitZeroCondition f c ∨
    UextComparisonCondition f c ∨ UextPlainCondition f c

/-- A branch of the split class: any block arguments, and a `GeneralCondition`. -/
def GeneralArgsBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ GeneralCondition f c

/-- Every block jumps, returns, branches as `GeneralArgsBranch`, or ends in `trap`. -/
def GeneralArgsTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralArgsBranch f b ∨ ∃ c,b.term = .trap c

/-- A branch of the legacy class: empty arguments, and a `GeneralCondition`. -/
def GeneralBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ yes.args = [] ∧ no.args = [] ∧ GeneralCondition f c

/-- Every block jumps, returns, branches as `GeneralBranch`, or ends in `trap`. -/
def GeneralTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralBranch f b ∨ ∃ c,b.term = .trap c

/-- The terminators of the legacy class are terminators of the split class. -/
theorem GeneralTerms.args {f : Clif.Function} (terms : GeneralTerms f) : GeneralArgsTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | ⟨c,yes,no,term,_,_,condition⟩ | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,condition⟩))
  · exact Or.inr (Or.inr (Or.inr trap))

/-! ## Metadata -/

/-- A statement result is defined in the built context by the statement's instruction. -/
theorem DefinedBy.metadata {f : Clif.Function} {v : Nat} {inst : Clif.Inst}
    (defined : DefinedBy f v inst) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : ctx.defClif? v = some inst := by
  obtain ⟨ibi,i,ib,stm,block,lookup,result,instEq⟩ := defined
  rw [← instEq]
  exact ComparisonLoopCfg.statement_metadata dominated block lookup result build

/-- A typed statement result has its type in the built context. -/
theorem TypedResult.metadata {f : Clif.Function} {v : Nat} {ty : Clif.Ty} {stm : Clif.Stmt}
    (typedResult : TypedResult f v ty stm) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : ctx.valueType? v = some (CTy.ofClif ty) := by
  obtain ⟨ibi,i,m,ib,tys,block,lookup,resultAt,typesEq,typeAt⟩ := typedResult
  have inv := buildCtx_mappedInv scope build
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨info,originalFound,clif,results⟩ := spec.facts.stmt ibi ib i stm block lookup
  have found : ctx.insts[blockStart f ibi+i]? = some info := by rw [view.insts]; exact originalFound
  obtain ⟨tys',typesEq',resTys,_⟩ := inv.resTys _ info stm.inst found clif
  rw [typesEq] at typesEq'
  cases typesEq'
  have resTypeAt : info.resTys[m]? = some (CTy.ofClif ty) := by
    rw [resTys,List.getElem?_map,typeAt]
    rfl
  have infoResult : info.results[m]? = some v := by rw [results]; exact resultAt
  have typed := (spec.facts.types dominated.ssa).1 _ info originalFound m v _ infoResult resTypeAt
  simpa only [Ctx.valueType?,view.valTy] using typed

/-- A declared value has its declared type in the built context. -/
theorem Declared.metadata {f : Clif.Function} {x : Nat} {ty : Clif.Ty}
    (declared : Declared f x ty) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : ctx.valueType? x = some (CTy.ofClif ty) := by
  rcases declared with ⟨pbi,pb,block,member⟩ | ⟨stm,typedResult⟩
  · obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
    have typed := (spec.facts.types dominated.ssa).2 pb (List.mem_of_getElem? block) _ member
    simpa only [Ctx.valueType?,view.valTy] using typed
  · exact typedResult.metadata scope dominated build

/-- The executable bit computation is `tcbc` at the declared type. -/
theorem tcbc_of_single_bit {tx : Clif.Ty} {n : Int} {bit : Nat} (single : singleBit tx.width n = some bit) :
    tcbc (CTy.ofClif tx) n = some bit := by
  unfold tcbc
  unfold singleBit at single
  rw [ofClif_bits_ctl]
  exact single

/-- **Per-block condition metadata.** A one-bit test has the metadata `TestBitMetadata`. -/
theorem TestBitCondition.metadata {f : Clif.Function} {c : Nat}
    (condition : TestBitCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : TestBitMetadata ctx c := by
  obtain ⟨ty,x,k,ty',imm,tx,bit,definedC,definedK,declared,single⟩ := condition
  exact ⟨ty,x,k,ty',imm,CTy.ofClif tx,bit,definedC.metadata dominated build,definedK.metadata dominated build,
    declared.metadata scope dominated build,tcbc_of_single_bit single⟩

/-- **Per-block condition metadata.** A zero test of a one-bit mask has the metadata
`TestBitZeroMetadata`. -/
theorem TestBitZeroCondition.metadata {f : Clif.Function} {c : Nat}
    (condition : TestBitZeroCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : TestBitZeroMetadata ctx c := by
  obtain ⟨tyc,y,z,ty0,imm0,definedC,band,definedZ,zero⟩ := condition
  exact ⟨tyc,y,z,ty0,imm0,definedC.metadata dominated build,band.metadata scope dominated build,
    definedZ.metadata dominated build,zero⟩

/-- **Per-block condition metadata.** A zero extension of a wide comparison has the metadata
`UextComparisonMetadata`. -/
theorem UextComparisonCondition.metadata {f : Clif.Function} {c : Nat}
    (condition : UextComparisonCondition f c) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : UextComparisonMetadata ctx c := by
  obtain ⟨target,z,cc,ty,x,y,wide,definedC,definedZ,parameterX,parameterY⟩ := condition
  have metaX := parameterX.metadata dominated build
  have metaY := parameterY.metadata dominated build
  exact ⟨target,z,cc,ty,x,y,wide,definedC.metadata dominated build,definedZ.metadata dominated build,
    metaX.1,metaY.1,metaX.2,metaY.2⟩

/-- No lowering rule looks through a plain zero extension. -/
theorem UextPlainCondition.plain {f : Clif.Function} {c : Nat}
    {stm : Clif.Stmt} {ty target : Clif.Ty} {x : Nat} (typedResult : TypedResult f c ty stm)
    (inst : stm.inst = .extend .uextend target x) (operand : NonComparisonOperand f x)
    (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : PlainSource ctx c := by
  obtain ⟨ibi,i,m,ib,tys,block,lookup,resultAt,_,_⟩ := typedResult
  have origin : ctx.defClif? c = some (.extend .uextend target x) := by
    rw [← inst]
    exact ComparisonLoopCfg.statement_metadata dominated block lookup (List.mem_of_getElem? resultAt) build
  refine ⟨?_,?_⟩
  · intro j info defined found ty' a b band
    have here : ctx.defClif? c = some (.binary .band ty' a b) := by
      simp [Ctx.defClif?,defined,found,band]
    rw [origin] at here
    cases here
  · intro cc ty' a b comparison
    rcases comparison with direct | ⟨target',z,extended,inner⟩
    · rw [origin] at direct
      cases direct
    · rw [origin] at extended
      simp only [Option.some.injEq,Clif.Inst.extend.injEq] at extended
      obtain ⟨_,_,rfl⟩ := extended
      rcases operand with ⟨pbi,pb,pty,parameterBlock,member⟩ | ⟨xbi,xi,xb,xstm,xBlock,xLookup,xResult,notIcmp⟩
      · obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
        have undefined := defInst_par spec.facts dominated.ssa parameterBlock (List.mem_map.mpr ⟨_,member,rfl⟩)
        have none : ctx.defInst? x = none := by simpa only [Ctx.defInst?,view.valDef] using undefined
        simp [Ctx.defClif?,none] at inner
      · have defined := ComparisonLoopCfg.statement_metadata dominated xBlock xLookup xResult build
        rw [defined] at inner
        exact notIcmp cc ty' a b (Option.some.inj inner)

/-- **Per-block condition metadata.** A plain zero extension has the metadata of a plain `i16` or
plain wide condition, a form of `GeneralCondMetadata4`. -/
theorem UextPlainCondition.metadata {f : Clif.Function} {c : Nat}
    (condition : UextPlainCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : GeneralCondMetadata4 ctx c := by
  obtain ⟨stm,ty,target,x,typedResult,types,inst,operand⟩ := condition
  have plain := UextPlainCondition.plain typedResult inst operand dominated build
  have typed := typedResult.metadata scope dominated build
  rcases types with rfl | rfl | rfl
  · exact Or.inl ⟨plain,typed⟩
  · exact Or.inr (Or.inr (Or.inl ⟨plain,Or.inl typed⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨plain,Or.inr typed⟩))

/-- **Per-block condition metadata.** A condition of the classes has, in the built context, the
metadata `BranchCondMetadata5`. -/
theorem condition_metadata {f : Clif.Function} {c : Nat}
    (condition : GeneralCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : BranchCondMetadata5 ctx c := by
  rcases condition with general | testBit | testBitZero | uext | uextPlain
  · exact Or.inr (Or.inr (GeneralArgsLoopCfg4.condition_metadata general scope dominated build))
  · exact Or.inr (Or.inl (Or.inl (testBit.metadata scope dominated build)))
  · exact Or.inr (Or.inl (Or.inr (testBitZero.metadata scope dominated build)))
  · exact Or.inl (uext.metadata dominated build)
  · exact Or.inr (Or.inr (uextPlain.metadata scope dominated build))

end Backend.Stock.Proof.GeneralArgsLoopCfg5

namespace Backend.Stock.GeneralArgsLoopCfg5
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg5
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem statement_of_sound {f : Clif.Function} {eligible : Clif.Stmt → Bool}
    (checked : ComparisonLoopCfg.statementOf f eligible = true) :
    ∃ (ibi i : Nat) (ib : Clif.Block) (stm : Clif.Stmt),f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧
      eligible stm = true := by
  obtain ⟨ib,member,present⟩ := List.any_eq_true.mp checked
  obtain ⟨ibi,block⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨stm,statement,good⟩ := List.any_eq_true.mp present
  obtain ⟨i,lookup⟩ := List.mem_iff_getElem?.mp statement
  exact ⟨ibi,i,ib,stm,block,lookup,good⟩

private theorem parameter_of_sound {f : Clif.Function} {x : Nat} {ty : Clif.Ty}
    (checked : ComparisonLoopCfg.parameterOf f x ty = true) :
    ∃ (pbi : Nat) (pb : Clif.Block),f.blocks[pbi]? = some pb ∧ (x,ty) ∈ pb.params := by
  obtain ⟨pb,member,present⟩ := List.any_eq_true.mp checked
  obtain ⟨pbi,block⟩ := List.mem_iff_getElem?.mp member
  exact ⟨pbi,pb,block,List.contains_iff_mem.mp present⟩

private theorem wide_parameter_of_sound {f : Clif.Function} {x : Nat} {wide : Bool}
    (checked : ComparisonLoopCfg.parameterOf f x (if wide then .i64 else .i32) = true) :
    ComparisonLoopCfg.WideParameter f x wide :=
  parameter_of_sound checked

private theorem typed_result_sound {f : Clif.Function} {v : Nat} {ty : Clif.Ty} {stm : Clif.Stmt}
    {ibi i : Nat} {ib : Clif.Block} (block : f.blocks[ibi]? = some ib) (lookup : ib.body[i]? = some stm)
    (checked : (stm.results.zip (ComparisonComputedLoopCfg.resultTypesOf f stm)).contains (v,ty) = true) :
    TypedResult f v ty stm := by
  obtain ⟨m,pair⟩ := List.mem_iff_getElem?.mp (List.contains_iff_mem.mp checked)
  obtain ⟨resultAt,typeAt⟩ := List.getElem?_zip_eq_some.mp pair
  cases types : stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | none => simp [ComparisonComputedLoopCfg.resultTypesOf,types] at typeAt
  | some tys =>
    simp only [ComparisonComputedLoopCfg.resultTypesOf,types,Option.getD_some] at typeAt
    exact ⟨ibi,i,m,ib,tys,block,lookup,resultAt,types,typeAt⟩

/-- The executable declared-type check derives the source declaration fact. -/
theorem declared_of_sound {f : Clif.Function} {x : Nat} {ty : Clif.Ty}
    (checked : declaredOf f x ty = true) : Declared f x ty := by
  simp only [declaredOf,Bool.or_eq_true] at checked
  rcases checked with parameter | result
  · exact Or.inl (parameter_of_sound parameter)
  · obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound result
    exact Or.inr ⟨stm,typed_result_sound block lookup good⟩

/-- The executable one-bit test check derives the source one-bit test fact. -/
theorem test_bit_sound {f : Clif.Function} {c : Nat} (checked : testBitEligible f c = true) :
    TestBitCondition f c := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [testBitStatement,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨result,rest⟩ := good
  split at rest
  · rename_i ty x k shape
    obtain ⟨kbi,ki,kb,kstm,kBlock,kLookup,kGood⟩ := statement_of_sound rest
    simp only [maskEligible,Bool.and_eq_true,List.contains_iff_mem] at kGood
    obtain ⟨kResult,kRest⟩ := kGood
    split at kRest
    · rename_i ty' imm kShape
      obtain ⟨tx,_,typed⟩ := List.any_eq_true.mp kRest
      simp only [Bool.and_eq_true] at typed
      obtain ⟨declared,single⟩ := typed
      obtain ⟨bit,bitEq⟩ := Option.isSome_iff_exists.mp single
      exact ⟨ty,x,k,ty',imm,tx,bit,⟨ibi,i,ib,stm,block,lookup,result,shape⟩,
        ⟨kbi,ki,kb,kstm,kBlock,kLookup,kResult,kShape⟩,declared_of_sound declared,bitEq⟩
    · cases kRest
  · cases rest

/-- The executable zero-test check derives the source zero-test fact. -/
theorem test_bit_zero_sound {f : Clif.Function} {c : Nat} (checked : testBitZeroEligible f c = true) :
    TestBitZeroCondition f c := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [testBitZeroStatement,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨result,rest⟩ := good
  split at rest
  · rename_i tyc y z shape
    simp only [Bool.and_eq_true] at rest
    obtain ⟨band,zeroCheck⟩ := rest
    obtain ⟨zbi,zi,zb,zstm,zBlock,zLookup,zGood⟩ := statement_of_sound zeroCheck
    simp only [ComparisonZeroCfg.constantEligible,Bool.and_eq_true,List.contains_iff_mem] at zGood
    obtain ⟨zResult,zValue⟩ := zGood
    cases zInst : zstm.inst <;> simp only [zInst] at zValue
    case iconst ty0 imm0 =>
      exact ⟨tyc,y,z,ty0,imm0,⟨ibi,i,ib,stm,block,lookup,result,shape⟩,test_bit_sound band,
        ⟨zbi,zi,zb,zstm,zBlock,zLookup,zResult,zInst⟩,beq_iff_eq.mp zValue⟩
    all_goals cases zValue
  · cases rest

/-- The executable check of a zero extension of a wide comparison derives its source fact. -/
theorem uext_comparison_sound {f : Clif.Function} {c : Nat} (checked : uextComparisonEligible f c = true) :
    UextComparisonCondition f c := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [uextComparisonStatement,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨result,rest⟩ := good
  split at rest
  · rename_i target z shape
    obtain ⟨zbi,zi,zb,zstm,zBlock,zLookup,zGood⟩ := statement_of_sound rest
    simp only [wideComparisonStatement,Bool.and_eq_true,List.contains_iff_mem] at zGood
    obtain ⟨zResult,zRest⟩ := zGood
    split at zRest
    · rename_i cc ty x y zShape
      simp only [Bool.or_eq_true,Bool.and_eq_true] at zRest
      have definedC : DefinedBy f c (.extend .uextend target z) := ⟨ibi,i,ib,stm,block,lookup,result,shape⟩
      have definedZ : DefinedBy f z (.icmp cc ty x y) := ⟨zbi,zi,zb,zstm,zBlock,zLookup,zResult,zShape⟩
      rcases zRest with ⟨narrowX,narrowY⟩ | ⟨wideX,wideY⟩
      · exact ⟨target,z,cc,ty,x,y,false,definedC,definedZ,wide_parameter_of_sound narrowX,
          wide_parameter_of_sound narrowY⟩
      · exact ⟨target,z,cc,ty,x,y,true,definedC,definedZ,wide_parameter_of_sound wideX,
          wide_parameter_of_sound wideY⟩
    · cases zRest
  · cases rest

private theorem non_comparison_sound {f : Clif.Function} {x : Nat}
    (checked : nonComparisonOperand f x = true) : NonComparisonOperand f x := by
  simp only [nonComparisonOperand,Bool.or_eq_true] at checked
  rcases checked with parameter | result
  · obtain ⟨pb,member,present⟩ := List.any_eq_true.mp parameter
    obtain ⟨pbi,block⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨⟨value,ty⟩,inside,same⟩ := List.any_eq_true.mp present
    simp only [beq_iff_eq] at same
    subst same
    exact Or.inl ⟨pbi,pb,ty,block,inside⟩
  · obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound result
    simp only [Bool.and_eq_true,List.contains_iff_mem] at good
    obtain ⟨inside,kind⟩ := good
    refine Or.inr ⟨ibi,i,ib,stm,block,lookup,inside,?_⟩
    intro cc ty a b same
    rw [same] at kind
    cases kind

/-- The executable plain zero-extension check derives its source fact. -/
theorem uext_plain_sound {f : Clif.Function} {c : Nat} (checked : uextPlainEligible f c = true) :
    UextPlainCondition f c := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [uextPlainStatement] at good
  split at good
  · rename_i target x shape
    simp only [Bool.and_eq_true] at good
    obtain ⟨types,operand⟩ := good
    obtain ⟨ty,member,typed⟩ := List.any_eq_true.mp types
    refine ⟨stm,ty,target,x,typed_result_sound block lookup typed,?_,shape,non_comparison_sound operand⟩
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
  · cases good

/-- The executable condition check of block `b` derives a condition of the classes. -/
theorem condition_sound {f : Clif.Function} {bi : Nat} {b : Clif.Block} {c : Nat}
    (block : f.blocks[bi]? = some b) (checked : conditionEligible f b c = true) : GeneralCondition f c := by
  simp only [conditionEligible,Bool.or_eq_true] at checked
  rcases checked with (((general | testBit) | testBitZero) | uext) | uextPlain
  · exact Or.inl (GeneralArgsLoopCfg4.condition_sound block general)
  · exact Or.inr (Or.inl (test_bit_sound testBit))
  · exact Or.inr (Or.inr (Or.inl (test_bit_zero_sound testBitZero)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (uext_comparison_sound uext))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (uext_plain_sound uextPlain))))

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralArgsBranch f b ∨
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

/-- **The split selector's source facts.** The selector derives the terminators, the entry kind,
the body families and the ABI. -/
theorem source_leaf_eligible_facts {f : Clif.Function} (checked : sourceLeafEligible f = true) :
    GeneralArgsTerms f ∧ (∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c) ∧
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

end Backend.Stock.GeneralArgsLoopCfg5

namespace Backend.Stock.GeneralLoopCfg5
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg5
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralBranch f b ∨
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
      GeneralArgsLoopCfg5.condition_sound block condition⟩))
  all_goals simp only [controlLeafEligible,controlEligible] at checked; cases checked

/-- **The legacy selector's source facts.** The selector derives the terminators, the entry kind,
the body families and the ABI. -/
theorem source_leaf_eligible_facts {f : Clif.Function} (checked : sourceLeafEligible f = true) :
    GeneralTerms f ∧ (∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c) ∧
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

end Backend.Stock.GeneralLoopCfg5

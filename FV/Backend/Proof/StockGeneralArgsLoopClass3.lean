import FV.Backend.Lowering.StockGeneralLoopCfg3
import FV.Backend.Proof.StockNarrowCondCarry
import FV.Backend.Proof.StockGeneralArgsLoopClass2

/-! Source facts of the loop classes with plain `i8` conditions (#140, CB-12).

`NarrowParameterCondition` states in source syntax that a `brif` condition is an `i8` parameter of
some block, and `NarrowResult` that it is an `i8` result of a statement of some block that is not
an `icmp`, a `band` or a `uextend` (`NarrowCondition`). `NarrowCondition.metadata` derives the
context metadata `NarrowCondMetadata` from the syntax, SSA and the built context. A condition of
the classes is a condition of the CB-11 classes (`GeneralArgsLoopCfg2.GeneralCondition`) or a
narrow condition (`GeneralCondition`); `condition_metadata` gives its `GeneralCondMetadata`.

`GeneralArgsTerms` are the terminators of the split class `GeneralArgsLoopCfg3` (a `brif` may pass
any block arguments), `GeneralTerms` those of the legacy class `GeneralLoopCfg3` (a `brif` passes
none); `GeneralTerms.args` forgets the empty arguments. The selectors derive the terminators, the
entry kind, the body families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.GeneralArgsLoopCfg3
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `c` is an `i8` parameter of some block. -/
def NarrowParameterCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (pbi : Nat) (pb : Clif.Block),f.blocks[pbi]? = some pb ∧ (c,.i8) ∈ pb.params

/-- `c` is the result at index `m` of a statement of some block that is not an `icmp`, a `band`
or a `uextend`, whose result type at `m` is `.i8`. -/
def NarrowResult (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (ibi i m : Nat) (ib : Clif.Block) (stm : Clif.Stmt) (tys : List Clif.Ty),
    f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧ stm.results[m]? = some c ∧
    stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
    tys[m]? = some .i8 ∧
    (∀ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),stm.inst ≠ .icmp cc ty x y) ∧
    (∀ (ty : Clif.Ty) (x y : Nat),stm.inst ≠ .binary .band ty x y) ∧
    (∀ (ty : Clif.Ty) (x : Nat),stm.inst ≠ .extend .uextend ty x)

/-- A narrow condition: an `i8` parameter or a `NarrowResult`. -/
def NarrowCondition (f : Clif.Function) (c : Nat) : Prop :=
  NarrowParameterCondition f c ∨ NarrowResult f c

/-- A condition of the classes: a condition of the CB-11 classes, or a narrow condition. -/
def GeneralCondition (f : Clif.Function) (c : Nat) : Prop :=
  GeneralArgsLoopCfg2.GeneralCondition f c ∨ NarrowCondition f c

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

/-- **Per-block condition metadata.** An `i8` parameter has, in the built context, no defining
instruction and the type `i8`. -/
theorem NarrowParameterCondition.metadata {f : Clif.Function} {c : Nat}
    (parameter : NarrowParameterCondition f c) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : NarrowCondMetadata ctx c := by
  obtain ⟨pbi,pb,block,member⟩ := parameter
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  have parameterId : c ∈ pb.params.map (·.1) := List.mem_map.mpr ⟨(c,.i8),member,rfl⟩
  have noDefinition := defInst_par spec.facts dominated.ssa block parameterId
  have originalType := (spec.facts.types dominated.ssa).2 pb (List.mem_of_getElem? block) (c,.i8) member
  have undefined : ctx.defInst? c = none := by
    simpa only [Ctx.defInst?,view.valDef] using noDefinition
  have typed : ctx.valueType? c = some (CTy.ofClif .i8) := by
    simpa only [Ctx.valueType?,view.valTy] using originalType
  exact NarrowCondMetadata.of_parameter undefined typed

/-- **Per-block condition metadata.** A `NarrowResult` has, in the built context, the metadata
`NarrowCondMetadata`: no lowering rule looks through its definition, and it has type `i8`. -/
theorem NarrowResult.metadata {f : Clif.Function} {c : Nat}
    (narrow : NarrowResult f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : NarrowCondMetadata ctx c := by
  obtain ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,typesEq,typeAt,notIcmp,notBand,notUextend⟩ := narrow
  have result : c ∈ stm.results := List.mem_of_getElem? resultAt
  have origin := ComparisonLoopCfg.statement_metadata dominated block lookup result build
  have inv := buildCtx_mappedInv scope build
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨info,originalFound,clif,results⟩ := spec.facts.stmt ibi ib i stm block lookup
  have found : ctx.insts[blockStart f ibi+i]? = some info := by rw [view.insts]; exact originalFound
  obtain ⟨tys',typesEq',resTys,_⟩ := inv.resTys _ info stm.inst found clif
  rw [typesEq] at typesEq'
  cases typesEq'
  have resTypeAt : info.resTys[m]? = some (CTy.ofClif .i8) := by
    rw [resTys,List.getElem?_map,typeAt]
    rfl
  have infoResult : info.results[m]? = some c := by rw [results]; exact resultAt
  have typed := (spec.facts.types dominated.ssa).1 _ info originalFound m c _ infoResult resTypeAt
  have width : CTy.ofClif .i8 = .int 8 := rfl
  have valueType : ctx.valueType? c = some (.int 8) := by
    simpa only [Ctx.valueType?,view.valTy,width] using typed
  refine ⟨⟨?_,?_⟩,valueType⟩
  · intro j info' defined found' ty a b band
    have here : ctx.defClif? c = some (.binary .band ty a b) := by
      simp [Ctx.defClif?,defined,found',band]
    rw [origin] at here
    exact notBand ty a b (Option.some.inj here)
  · intro cc ty a b comparison
    rcases comparison with direct | ⟨target,z,extended,_⟩
    · rw [origin] at direct
      exact notIcmp cc ty a b (Option.some.inj direct)
    · rw [origin] at extended
      exact notUextend target z (Option.some.inj extended)

/-- **Per-block condition metadata.** A narrow condition has the metadata `NarrowCondMetadata`. -/
theorem NarrowCondition.metadata {f : Clif.Function} {c : Nat}
    (narrow : NarrowCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : NarrowCondMetadata ctx c := by
  rcases narrow with parameter | result
  · exact parameter.metadata dominated build
  · exact result.metadata scope dominated build

/-- **Per-block condition metadata.** A condition of the classes has, in the built context, the
metadata `GeneralCondMetadata`. -/
theorem condition_metadata {f : Clif.Function} {c : Nat}
    (condition : GeneralCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : GeneralCondMetadata ctx c := by
  rcases condition with wide | narrow
  · exact Or.inr (GeneralArgsLoopCfg2.condition_metadata wide scope dominated build)
  · exact Or.inl (narrow.metadata scope dominated build)

end Backend.Stock.Proof.GeneralArgsLoopCfg3

namespace Backend.Stock.GeneralArgsLoopCfg3
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg3
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

/-- The executable `i8` parameter check derives the source parameter fact. -/
theorem narrow_parameter_eligible_sound {f : Clif.Function} {c : Nat}
    (checked : narrowParameterEligible f c = true) : NarrowParameterCondition f c := by
  obtain ⟨pb,member,present⟩ := List.any_eq_true.mp checked
  obtain ⟨pbi,block⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨⟨value,ty⟩,parameter,good⟩ := List.any_eq_true.mp present
  simp only [Bool.and_eq_true,beq_iff_eq] at good
  obtain ⟨rfl,rfl⟩ := good
  exact ⟨pbi,pb,block,parameter⟩

/-- The executable `i8` plain-result check derives the source result fact. -/
private theorem narrow_result_sound {f : Clif.Function} {c : Nat}
    (checked : ComparisonLoopCfg.statementOf f (GeneralArgsLoopCfg2.plainResult f c .i8) = true) :
    NarrowResult f c := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [GeneralArgsLoopCfg2.plainResult,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨kind,member⟩ := good
  obtain ⟨m,pair⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨resultAt,typeAt⟩ := List.getElem?_zip_eq_some.mp pair
  cases types : stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | none => simp [ComparisonComputedLoopCfg.resultTypesOf,types] at typeAt
  | some tys =>
    simp only [ComparisonComputedLoopCfg.resultTypesOf,types,Option.getD_some] at typeAt
    refine ⟨ibi,i,m,ib,stm,tys,block,lookup,resultAt,types,typeAt,?_,?_,?_⟩
    · intro cc ty x y same
      rw [same] at kind
      simp [GeneralArgsLoopCfg2.plainInst] at kind
    · intro ty x y same
      rw [same] at kind
      simp [GeneralArgsLoopCfg2.plainInst] at kind
    · intro ty x same
      rw [same] at kind
      simp [GeneralArgsLoopCfg2.plainInst] at kind

/-- The executable narrow condition check derives the source narrow condition fact. -/
theorem narrow_eligible_sound {f : Clif.Function} {c : Nat} (checked : narrowEligible f c = true) :
    NarrowCondition f c := by
  simp only [narrowEligible,Bool.or_eq_true] at checked
  rcases checked with parameter | result
  · exact Or.inl (narrow_parameter_eligible_sound parameter)
  · exact Or.inr (narrow_result_sound result)

/-- The executable condition check of block `b` derives a condition of the classes. -/
theorem condition_sound {f : Clif.Function} {bi : Nat} {b : Clif.Block} {c : Nat}
    (block : f.blocks[bi]? = some b) (checked : conditionEligible f b c = true) : GeneralCondition f c := by
  simp only [conditionEligible,Bool.or_eq_true] at checked
  rcases checked with wide | narrow
  · exact Or.inl (GeneralArgsLoopCfg2.condition_sound block wide)
  · exact Or.inr (narrow_eligible_sound narrow)

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

end Backend.Stock.GeneralArgsLoopCfg3

namespace Backend.Stock.GeneralLoopCfg3
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg3
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
      GeneralArgsLoopCfg3.condition_sound block condition⟩))
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

end Backend.Stock.GeneralLoopCfg3

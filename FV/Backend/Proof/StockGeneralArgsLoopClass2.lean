import FV.Backend.Lowering.StockGeneralLoopCfg2
import FV.Backend.Proof.StockGeneralCondCarry
import FV.Backend.Proof.StockComparisonComputedArgsLoopClass

/-! Source facts of the loop classes with plain computed conditions (#140, CB-11).

`PlainResult` states in source syntax that a `brif` condition is a result of type `i32` or `i64`
of a statement of some block that is not an `icmp`, a `band` or a `uextend`
(`PlainCondition`). `PlainCondition.metadata` derives the context metadata `PlainMetadata` from
the syntax, SSA and the built context. A condition of the classes is a wide parameter, a
comparison in a form of `ComputedArgsCondition` (CB-9), or a plain condition
(`GeneralCondition`); `condition_metadata` gives its `CondMetadata`.

`GeneralArgsTerms` are the terminators of the split class `GeneralArgsLoopCfg2` (a `brif` may pass
any block arguments), `GeneralTerms` those of the legacy class `GeneralLoopCfg2` (a `brif` passes
none); `GeneralTerms.args` forgets the empty arguments. The selectors derive the terminators, the
entry kind, the body families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.GeneralArgsLoopCfg2
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ComparisonComputedArgsLoopCfg Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `c` is the result at index `m` of a statement of some block that is not an `icmp`, a `band`
or a `uextend`, whose result type at `m` is `.i64` when `wide`, else `.i32`. -/
def PlainResult (f : Clif.Function) (c : Nat) (wide : Bool) : Prop :=
  ∃ (ibi i m : Nat) (ib : Clif.Block) (stm : Clif.Stmt) (tys : List Clif.Ty),
    f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧ stm.results[m]? = some c ∧
    stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
    tys[m]? = some (if wide then .i64 else .i32) ∧
    (∀ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),stm.inst ≠ .icmp cc ty x y) ∧
    (∀ (ty : Clif.Ty) (x y : Nat),stm.inst ≠ .binary .band ty x y) ∧
    (∀ (ty : Clif.Ty) (x : Nat),stm.inst ≠ .extend .uextend ty x)

/-- A plain condition: a `PlainResult` of one wide type. -/
def PlainCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ wide,PlainResult f c wide

/-- A condition of the classes: a wide parameter, a comparison in a form of
`ComputedArgsCondition`, or a plain condition. -/
def GeneralCondition (f : Clif.Function) (c : Nat) : Prop :=
  ParameterCondition f c ∨ ComputedArgsCondition f c ∨ PlainCondition f c

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

/-- **Per-block condition metadata.** A plain condition has, in the built context, the metadata
`PlainMetadata`: no lowering rule looks through its definition, and it has its wide type. -/
theorem PlainCondition.metadata {f : Clif.Function} {c : Nat}
    (plain : PlainCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : PlainMetadata ctx c := by
  obtain ⟨wide,ibi,i,m,ib,stm,tys,block,lookup,resultAt,typesEq,typeAt,notIcmp,notBand,notUextend⟩ := plain
  have result : c ∈ stm.results := List.mem_of_getElem? resultAt
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
  have infoResult : info.results[m]? = some c := by rw [results]; exact resultAt
  have typed := (spec.facts.types dominated.ssa).1 _ info originalFound m c _ infoResult resTypeAt
  have width : CTy.ofClif (if wide then .i64 else .i32) = .int (if wide then 64 else 32) := by
    cases wide <;> rfl
  have valueType : ctx.valueType? c = some (.int (if wide then 64 else 32)) := by
    simpa only [Ctx.valueType?,view.valTy,width] using typed
  refine ⟨⟨?_,?_⟩,?_⟩
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
  · cases wide
    · exact Or.inl (by simpa only [Bool.false_eq_true,ite_false] using valueType)
    · exact Or.inr (by simpa only [ite_true] using valueType)

/-- **Per-block condition metadata.** A condition of the classes has, in the built context, the
metadata `CondMetadata`. -/
theorem condition_metadata {f : Clif.Function} {c : Nat}
    (condition : GeneralCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : CondMetadata ctx c := by
  rcases condition with parameter | comparison | plain
  · have metadata := parameter_metadata parameter dominated.ssa build
    exact Or.inl (PlainMetadata.of_parameter metadata.1 metadata.2)
  · exact Or.inr (comparison.metadata scope dominated build)
  · exact Or.inl (plain.metadata scope dominated build)

end Backend.Stock.Proof.GeneralArgsLoopCfg2

namespace Backend.Stock.GeneralArgsLoopCfg2
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg2
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

/-- The executable plain-result check derives the source result fact. -/
private theorem plain_result_sound {f : Clif.Function} {c : Nat} {wide : Bool}
    (checked : ComparisonLoopCfg.statementOf f (plainResult f c (if wide then .i64 else .i32)) = true) :
    PlainResult f c wide := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [plainResult,Bool.and_eq_true,List.contains_iff_mem] at good
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
      simp [plainInst] at kind
    · intro ty x y same
      rw [same] at kind
      simp [plainInst] at kind
    · intro ty x same
      rw [same] at kind
      simp [plainInst] at kind

/-- The executable plain condition check derives the source plain condition fact. -/
theorem plain_eligible_sound {f : Clif.Function} {c : Nat} (checked : plainEligible f c = true) :
    PlainCondition f c := by
  simp only [plainEligible,Bool.or_eq_true] at checked
  rcases checked with narrow | wide
  · exact ⟨false,plain_result_sound narrow⟩
  · exact ⟨true,plain_result_sound wide⟩

/-- The executable condition check of block `b` derives a condition of the classes. -/
theorem condition_sound {f : Clif.Function} {bi : Nat} {b : Clif.Block} {c : Nat}
    (block : f.blocks[bi]? = some b) (checked : conditionEligible f b c = true) : GeneralCondition f c := by
  simp only [conditionEligible,Bool.or_eq_true] at checked
  rcases checked with comparison | plain
  · rcases ComparisonComputedArgsLoopCfg.condition_sound block comparison with parameter | computed
    · exact Or.inl parameter
    · exact Or.inr (Or.inl computed)
  · exact Or.inr (Or.inr (plain_eligible_sound plain))

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

end Backend.Stock.GeneralArgsLoopCfg2

namespace Backend.Stock.GeneralLoopCfg2
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg2
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
      GeneralArgsLoopCfg2.condition_sound block condition⟩))
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

end Backend.Stock.GeneralLoopCfg2

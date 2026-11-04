import FV.Backend.Lowering.StockGeneralLoopCfg7
import FV.Backend.Proof.StockGeneralArgsLoopClass6
import FV.Backend.Proof.StockBranchCond7Carry

/-! Source facts of the loop classes with plain `band` conditions (#140, CB-15).

The source syntax of the new condition: a plain `band` (`PlainBandCondition`: an `i32` or `i64`
result of `band x k`, where the mask `k` is not a one-bit mask of `x`, `NonTestMask`). Its
`metadata` theorem derives `PlainMetadata'` from the syntax, SSA and the built context: the actual
definition of `c` is the `band`, so it is not a comparison origin, and an actual one-bit test
`TestBitMetadata` would make `k` an `iconst` with one set bit below the width of the context type
of `x`, which `NonTestMask` excludes. A condition of the classes is a condition of
`GeneralArgsLoopCfg5` or a plain `band` (`GeneralCondition`); `condition_metadata` gives its
`BranchCondMetadata7`.

`GeneralArgsTerms` are the terminators of the split class `GeneralArgsLoopCfg7`, `GeneralTerms`
those of the legacy class `GeneralLoopCfg7`. The selectors derive the terminators, the entry kind,
the body families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.GeneralArgsLoopCfg7
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.PlainBranch
  Backend.Stock.Proof.TestBitBranch Backend.Stock.Proof.GeneralArgsLoopCfg5 Backend.Stock.GeneralArgsLoopCfg5
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `k` is not a one-bit mask of `x`: a block parameter, a result of a statement that is not an
`iconst`, or a result of `iconst imm` where `imm` does not have exactly one set bit below the width
of a declared type of `x`. -/
def NonTestMask (f : Clif.Function) (x k : Nat) : Prop :=
  (∃ (pbi : Nat) (pb : Clif.Block) (ty : Clif.Ty),f.blocks[pbi]? = some pb ∧ (k,ty) ∈ pb.params) ∨
  (∃ (ibi i : Nat) (ib : Clif.Block) (stm : Clif.Stmt),f.blocks[ibi]? = some ib ∧ ib.body[i]? = some stm ∧
    k ∈ stm.results ∧ ∀ (ty : Clif.Ty) (imm : BitVec ty.width),stm.inst ≠ .iconst ty imm) ∨
  ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (tx : Clif.Ty),DefinedBy f k (.iconst ty imm) ∧ Declared f x tx ∧
    singleBit tx.width ((u64 (imm64OfIconst ty imm) : Nat) : Int) = none

/-- `c` is a plain `band`: an `i32` or `i64` result of `band x k` with `k` not a one-bit mask of
`x`. -/
def PlainBandCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (stm : Clif.Stmt) (ty tyb : Clif.Ty) (x k : Nat),TypedResult f c ty stm ∧ (ty = .i32 ∨ ty = .i64) ∧
    stm.inst = .binary .band tyb x k ∧ NonTestMask f x k

/-- A condition of the classes: a condition of `GeneralArgsLoopCfg5`, or a plain `band`. -/
def GeneralCondition (f : Clif.Function) (c : Nat) : Prop :=
  GeneralArgsLoopCfg5.GeneralCondition f c ∨ PlainBandCondition f c

/-- A branch of the split class: any block arguments, and a `GeneralCondition`. -/
def GeneralArgsBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ GeneralCondition f c

/-- A branch of the legacy class: empty arguments, and a `GeneralCondition`. -/
def GeneralBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ yes.args = [] ∧ no.args = [] ∧ GeneralCondition f c

/-- Every block jumps, returns, branches as `GeneralArgsBranch`, branches as `TableBranch`, or ends
in `trap`. -/
def GeneralArgsTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralArgsBranch f b ∨
      GeneralArgsLoopCfg6.TableBranch f b ∨ ∃ c,b.term = .trap c

/-- Every block jumps, returns, branches as `GeneralBranch`, branches as `EmptyTableBranch`, or ends
in `trap`. -/
def GeneralTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralBranch f b ∨
      GeneralArgsLoopCfg6.EmptyTableBranch f b ∨ ∃ c,b.term = .trap c

/-- The terminators of the legacy class are terminators of the split class. -/
theorem GeneralTerms.args {f : Clif.Function} (terms : GeneralTerms f) : GeneralArgsTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | ⟨c,yes,no,term,_,_,condition⟩ | ⟨x,dc,tbl,term,declared,small,_⟩ | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,condition⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x,dc,tbl,term,declared,small⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr trap)))

/-- The terminators of `GeneralArgsLoopCfg6` are terminators of the split class. -/
theorem general_args_terms_of_cfg6 {f : Clif.Function} (terms : GeneralArgsLoopCfg6.GeneralArgsTerms f) :
    GeneralArgsTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | ⟨c,yes,no,term,condition⟩ | table | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,Or.inl condition⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl table)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr trap)))

/-- The terminators of `GeneralLoopCfg6` are terminators of the legacy class. -/
theorem general_terms_of_cfg6 {f : Clif.Function} (terms : GeneralArgsLoopCfg6.GeneralTerms f) :
    GeneralTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | ⟨c,yes,no,term,yesEmpty,noEmpty,condition⟩ | table | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,yesEmpty,noEmpty,Or.inl condition⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl table)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr trap)))

/-! ## Metadata -/

/-- `tcbc` at a source type is `singleBit` at its width. -/
theorem tcbc_ofClif (tx : Clif.Ty) (n : Int) : tcbc (CTy.ofClif tx) n = singleBit tx.width n := by
  unfold tcbc singleBit
  rw [ofClif_bits_ctl]
  split <;> split <;> simp_all

/-- **Per-block condition metadata.** A plain `band` has the metadata `PlainMetadata'`. -/
theorem PlainBandCondition.metadata {f : Clif.Function} {c : Nat}
    (condition : PlainBandCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : PlainMetadata' ctx c := by
  obtain ⟨stm,ty,tyb,x,k,typedResult,types,inst,mask⟩ := condition
  have typed := typedResult.metadata scope dominated build
  obtain ⟨ibi,i,m,ib,tys,block,lookup,resultAt,_,_⟩ := typedResult
  have origin : ctx.defClif? c = some (.binary .band tyb x k) := by
    rw [← inst]
    exact ComparisonLoopCfg.statement_metadata dominated block lookup (List.mem_of_getElem? resultAt) build
  refine ⟨⟨?_,?_⟩,?_⟩
  · rintro ⟨ty1,a,b,ty',imm,t,bit,band,constant,typeX,bitEq⟩
    rw [origin] at band
    simp only [Option.some.injEq,Clif.Inst.binary.injEq,true_and] at band
    obtain ⟨_,rfl,rfl⟩ := band
    rcases mask with ⟨pbi,pb,pty,parameterBlock,member⟩ |
      ⟨kbi,ki,kb,kstm,kBlock,kLookup,kResult,notConstant⟩ | ⟨ty'',imm'',tx,definedK,declared,none⟩
    · obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
      have undefined := defInst_par spec.facts dominated.ssa parameterBlock (List.mem_map.mpr ⟨_,member,rfl⟩)
      have absent : ctx.defInst? k = none := by simpa only [Ctx.defInst?,view.valDef] using undefined
      simp [Ctx.defClif?,absent] at constant
    · have defined := ComparisonLoopCfg.statement_metadata dominated kBlock kLookup kResult build
      rw [defined] at constant
      exact notConstant ty' imm (Option.some.inj constant)
    · have defined := definedK.metadata dominated build
      rw [defined] at constant
      simp only [Option.some.injEq,Clif.Inst.iconst.injEq] at constant
      obtain ⟨rfl,same⟩ := constant
      cases same
      have declaredType := declared.metadata scope dominated build
      rw [declaredType] at typeX
      cases typeX
      rw [tcbc_ofClif,none] at bitEq
      cases bitEq
  · intro cc ty' a b comparison
    rcases comparison with direct | ⟨target,z,extended,inner⟩
    · rw [origin] at direct
      cases direct
    · rw [origin] at extended
      cases extended
  · rcases types with rfl | rfl
    · exact Or.inl typed
    · exact Or.inr typed

/-- **Per-block condition metadata.** A condition of the classes has, in the built context, the
metadata `BranchCondMetadata7`. -/
theorem condition_metadata {f : Clif.Function} {c : Nat}
    (condition : GeneralCondition f c) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : BranchCondMetadata7 ctx c := by
  rcases condition with general | band
  · exact Or.inr (GeneralArgsLoopCfg5.condition_metadata general scope dominated build)
  · exact Or.inl (band.metadata scope dominated build)

end Backend.Stock.Proof.GeneralArgsLoopCfg7

namespace Backend.Stock.GeneralArgsLoopCfg7
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg7
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

private theorem typed_result_sound {f : Clif.Function} {v : Nat} {ty : Clif.Ty} {stm : Clif.Stmt}
    {ibi i : Nat} {ib : Clif.Block} (block : f.blocks[ibi]? = some ib) (lookup : ib.body[i]? = some stm)
    (checked : (stm.results.zip (ComparisonComputedLoopCfg.resultTypesOf f stm)).contains (v,ty) = true) :
    Proof.GeneralArgsLoopCfg5.TypedResult f v ty stm := by
  obtain ⟨m,pair⟩ := List.mem_iff_getElem?.mp (List.contains_iff_mem.mp checked)
  obtain ⟨resultAt,typeAt⟩ := List.getElem?_zip_eq_some.mp pair
  cases types : stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
  | none => simp [ComparisonComputedLoopCfg.resultTypesOf,types] at typeAt
  | some tys =>
    simp only [ComparisonComputedLoopCfg.resultTypesOf,types,Option.getD_some] at typeAt
    exact ⟨ibi,i,m,ib,tys,block,lookup,resultAt,types,typeAt⟩

/-- The executable mask check derives the source mask fact. -/
theorem non_test_mask_sound {f : Clif.Function} {x k : Nat} (checked : nonTestMask f x k = true) :
    NonTestMask f x k := by
  simp only [nonTestMask,Bool.or_eq_true] at checked
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
    split at kind
    · rename_i ty imm shape
      obtain ⟨tx,_,typed⟩ := List.any_eq_true.mp kind
      simp only [Bool.and_eq_true] at typed
      obtain ⟨declared,none⟩ := typed
      exact Or.inr (Or.inr ⟨ty,imm,tx,⟨ibi,i,ib,stm,block,lookup,inside,shape⟩,
        GeneralArgsLoopCfg5.declared_of_sound declared,Option.isNone_iff_eq_none.mp none⟩)
    · rename_i notConstant
      exact Or.inr (Or.inl ⟨ibi,i,ib,stm,block,lookup,inside,fun ty imm same => notConstant ty imm same⟩)

/-- The executable plain `band` check derives its source fact. -/
theorem plain_band_sound {f : Clif.Function} {c : Nat} (checked : plainBandEligible f c = true) :
    PlainBandCondition f c := by
  obtain ⟨ibi,i,ib,stm,block,lookup,good⟩ := statement_of_sound checked
  simp only [plainBandStatement] at good
  split at good
  · rename_i tyb x k shape
    simp only [Bool.and_eq_true] at good
    obtain ⟨types,mask⟩ := good
    obtain ⟨ty,member,typed⟩ := List.any_eq_true.mp types
    refine ⟨stm,ty,tyb,x,k,typed_result_sound block lookup typed,?_,shape,non_test_mask_sound mask⟩
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
  · cases good

/-- The executable condition check of block `b` derives a condition of the classes. -/
theorem condition_sound {f : Clif.Function} {bi : Nat} {b : Clif.Block} {c : Nat}
    (block : f.blocks[bi]? = some b) (checked : conditionEligible f b c = true) : GeneralCondition f c := by
  simp only [conditionEligible,Bool.or_eq_true] at checked
  rcases checked with general | band
  · exact Or.inl (GeneralArgsLoopCfg5.condition_sound block general)
  · exact Or.inr (plain_band_sound band)

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralArgsBranch f b ∨
      Proof.GeneralArgsLoopCfg6.TableBranch f b ∨ (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩)))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨condition,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,condition_sound block condition⟩))
  case brTable x dc tbl =>
    simp only [controlLeafEligible,controlEligible,GeneralArgsLoopCfg6.controlEligible] at checked
    obtain ⟨declared,small⟩ := GeneralArgsLoopCfg6.table_sound checked
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x,dc,tbl,term,declared,small⟩)))
  all_goals
    simp only [controlLeafEligible,controlEligible,GeneralArgsLoopCfg6.controlEligible,
      GeneralArgsLoopCfg5.controlEligible] at checked
    cases checked

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
    rcases control_leaf_facts found (each bi b found) with jump | ret | branch | table | ⟨c,trap,_⟩
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)
    · exact Or.inr (Or.inr (Or.inl branch))
    · exact Or.inr (Or.inr (Or.inr (Or.inl table)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,trap⟩)))
  · intro b found c trap
    rcases control_leaf_facts found (each 0 b found) with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c',yes,no,branch,_⟩ | ⟨x,dc,tbl,table,_⟩ | ⟨c',trap',entry⟩
    · rw [trap] at jump; cases jump
    · rw [trap] at ret; cases ret
    · rw [trap] at branch; cases branch
    · rw [trap] at table; cases table
    · exact entry rfl
  · intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

end Backend.Stock.GeneralArgsLoopCfg7

namespace Backend.Stock.GeneralLoopCfg7
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg7
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralBranch f b ∨
      Proof.GeneralArgsLoopCfg6.EmptyTableBranch f b ∨ (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩)))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,List.isEmpty_iff.mp yesEmpty,List.isEmpty_iff.mp noEmpty,
      GeneralArgsLoopCfg7.condition_sound block condition⟩))
  case brTable x dc tbl =>
    simp only [controlLeafEligible,controlEligible,GeneralLoopCfg6.controlEligible,Bool.and_eq_true] at checked
    obtain ⟨table,empty⟩ := checked
    obtain ⟨declared,small⟩ := GeneralArgsLoopCfg6.table_sound table
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨x,dc,tbl,term,declared,small,?_⟩)))
    intro bc member
    exact List.isEmpty_iff.mp (List.all_eq_true.mp empty bc member)
  all_goals
    simp only [controlLeafEligible,controlEligible,GeneralLoopCfg6.controlEligible,
      GeneralLoopCfg5.controlEligible] at checked
    cases checked

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
    rcases control_leaf_facts found (each bi b found) with jump | ret | branch | table | ⟨c,trap,_⟩
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)
    · exact Or.inr (Or.inr (Or.inl branch))
    · exact Or.inr (Or.inr (Or.inr (Or.inl table)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,trap⟩)))
  · intro b found c trap
    rcases control_leaf_facts found (each 0 b found) with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c',yes,no,branch,_⟩ | ⟨x,dc,tbl,table,_⟩ | ⟨c',trap',entry⟩
    · rw [trap] at jump; cases jump
    · rw [trap] at ret; cases ret
    · rw [trap] at branch; cases branch
    · rw [trap] at table; cases table
    · exact entry rfl
  · intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

end Backend.Stock.GeneralLoopCfg7

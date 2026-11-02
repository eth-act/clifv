import FV.Backend.Lowering.StockComparisonZeroCfg
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.ComparisonZeroCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Source facts for the zero comparison class with return or trap leaves.
All describe original source syntax; correctness and final-code
compatibility are separate. The condition is a result of an entry
`icmp eq` or `icmp ne` whose first operand is a wide entry parameter and
whose second operand is a result of an entry `iconst` of zero. -/
structure LeafShape (f : Clif.Function) where
  entry : Clif.Block
  condition : Nat
  yes : Clif.BlockCall
  no : Clif.BlockCall
  source : f.blocks[0]? = some entry
  term : entry.term = .brif condition yes no
  comparison : ∃ (j : Nat) (stm : Clif.Stmt) (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool),
    entry.body[j]? = some stm ∧ condition ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
    (cc = .eq ∨ cc = .ne) ∧ (x,if wide then Clif.Ty.i64 else .i32) ∈ entry.params ∧
    ∃ (i : Nat) (constant : Clif.Stmt) (ty' : Clif.Ty) (k : BitVec ty'.width),
      entry.body[i]? = some constant ∧ y ∈ constant.results ∧ constant.inst = .iconst ty' k ∧ k = 0
  targets : ∀ bc,bc = yes ∨ bc = no → bc.args = [] ∧
    ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl
  leaves : ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
    b.params = [] ∧ ((∃ xs,b.term = .ret xs) ∨ ∃ c,b.term = .trap c)
  family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst
  abiParams : f.sig.params.all Scalar.narrowAbiEligible = true
  abiReturns : f.sig.returns.all Scalar.narrowAbiEligible = true

private theorem target_sound {f : Clif.Function} {bc : Clif.BlockCall}
    (checked : ConditionalCfg.targetEligible f bc = true) :
    bc.args = [] ∧ ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl := by
  simp only [ConditionalCfg.targetEligible,Bool.and_eq_true] at checked
  have empty : bc.args = [] := List.isEmpty_iff.mp checked.1
  cases lookup : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp only [lookup] at checked; cases checked.2
  | some tl =>
    simp only [lookup,decide_eq_true_eq] at checked
    exact ⟨empty,tl,lookup,checked.2⟩

/-- The executable constant check derives the source `iconst 0` fact. -/
private theorem constant_sound {y : Nat} {stm : Clif.Stmt}
    (checked : constantEligible y stm = true) :
    y ∈ stm.results ∧ ∃ (ty' : Clif.Ty) (k : BitVec ty'.width),stm.inst = .iconst ty' k ∧ k = 0 := by
  simp only [constantEligible,Bool.and_eq_true,List.contains_iff_mem] at checked
  obtain ⟨result,value⟩ := checked
  cases inst : stm.inst <;> simp only [inst] at value
  case iconst ty' k => exact ⟨result,ty',k,rfl,beq_iff_eq.mp value⟩
  all_goals cases value

/-- The executable comparison check derives the source comparison fact. -/
private theorem comparison_sound {entry : Clif.Block} {condition : Nat}
    (checked : entry.body.any (zeroEligible entry condition) = true) :
    ∃ (j : Nat) (stm : Clif.Stmt) (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool),
      entry.body[j]? = some stm ∧ condition ∈ stm.results ∧ stm.inst = .icmp cc ty x y ∧
      (cc = .eq ∨ cc = .ne) ∧ (x,if wide then Clif.Ty.i64 else .i32) ∈ entry.params ∧
      ∃ (i : Nat) (constant : Clif.Stmt) (ty' : Clif.Ty) (k : BitVec ty'.width),
        entry.body[i]? = some constant ∧ y ∈ constant.results ∧ constant.inst = .iconst ty' k ∧ k = 0 := by
  obtain ⟨stm,member,good⟩ := List.any_eq_true.mp checked
  obtain ⟨j,lookup⟩ := List.mem_iff_getElem?.mp member
  simp only [zeroEligible,Bool.and_eq_true,List.contains_iff_mem] at good
  obtain ⟨result,operands⟩ := good
  cases inst : stm.inst <;> simp only [inst] at operands
  case icmp cc ty x y =>
    simp only [Bool.or_eq_true,Bool.and_eq_true,List.contains_iff_mem,beq_iff_eq] at operands
    obtain ⟨⟨equality,parameter⟩,constants⟩ := operands
    obtain ⟨constant,constantMember,constantGood⟩ := List.any_eq_true.mp constants
    obtain ⟨i,constantLookup⟩ := List.mem_iff_getElem?.mp constantMember
    obtain ⟨defined,ty',k,constantInst,zero⟩ := constant_sound constantGood
    rcases parameter with narrowX | wideX
    · exact ⟨j,stm,cc,ty,x,y,false,lookup,result,inst,equality,narrowX,
        i,constant,ty',k,constantLookup,defined,constantInst,zero⟩
    · exact ⟨j,stm,cc,ty,x,y,true,lookup,result,inst,equality,wideX,
        i,constant,ty',k,constantLookup,defined,constantInst,zero⟩
  all_goals cases operands

/-- The leaf selector derives the leaf source facts, without adding any
machine-code, source-state, selected-rule or semantic-result certificate. -/
theorem leafEligible_shape {f : Clif.Function} (checked : leafEligible f = true) :
    Nonempty (LeafShape f) := by
  cases blocks : f.blocks with
  | nil => simp [leafEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [leafEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨⟨comparison,yesGood⟩,noGood⟩,leaves⟩,bodies⟩,params⟩,returns⟩ := checked
      refine ⟨{
        entry := entry
        condition := c
        yes := yes
        no := no
        source := by simp only [blocks,List.getElem?_cons_zero]
        term := term
        comparison := comparison_sound comparison
        targets := ?_
        leaves := ?_
        family := ?_
        abiParams := params
        abiReturns := returns }⟩
      · intro bc choice
        rcases choice with rfl | rfl
        · exact target_sound yesGood
        · exact target_sound noGood
      · intro bi b found nonentry
        have member : b ∈ rest := by
          cases bi with
          | zero => exact False.elim (nonentry rfl)
          | succ bi =>
            rw [blocks,List.getElem?_cons_succ] at found
            exact List.mem_of_getElem? found
        have good := List.all_eq_true.mp leaves b member
        simp only [Bool.and_eq_true] at good
        refine ⟨List.isEmpty_iff.mp good.1,?_⟩
        cases term : b.term <;> simp only [term] at good
        case ret xs => exact Or.inl ⟨xs,rfl⟩
        case trap c => exact Or.inr ⟨c,rfl⟩
        all_goals cases good.2
      · intro b member stm present
        have member' : b ∈ entry :: rest := by simpa only [blocks] using member
        exact Scalar.maskMixedBodyEligible_sound
          (List.all_eq_true.mp (List.all_eq_true.mp bodies b member') stm present)
    all_goals cases checked

/-- Original entry `icmp` and `iconst` syntax, entry-parameter membership and
SSA derive the real built context's `eq`/`ne` comparison definition,
first-operand parameter status and width, and the constant operand's
`iconst 0` definition. No selected rule or DFG certificate is supplied. -/
theorem LeafShape.condition_metadata {f : Clif.Function} (shape : LeafShape f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool)
      (ty' : Clif.Ty) (k : BitVec ty'.width),
      ctx.defClif? shape.condition = some (.icmp cc ty x y) ∧
      ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧
      ctx.defInst? x = none ∧
      ctx.defClif? y = some (.iconst ty' k) ∧
      (cc = .eq ∨ cc = .ne) ∧ k = 0 := by
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨j,stm,cc,ty,x,y,wide,lookup,result,inst,equality,memberX,
    i,constant,ty',k,constantLookup,constantResult,constantInst,zero⟩ := shape.comparison
  have defined := defInst_res spec.facts dominated.ssa shape.source lookup result
  obtain ⟨info,found,clif,-⟩ := spec.facts.stmt 0 shape.entry j stm shape.source lookup
  have originalClif : original.defClif? shape.condition = some (.icmp cc ty x y) := by
    simp [Ctx.defClif?,defined,found,clif,inst]
  have constantDefined := defInst_res spec.facts dominated.ssa shape.source constantLookup constantResult
  obtain ⟨constantInfo,constantFound,constantClif,-⟩ :=
    spec.facts.stmt 0 shape.entry i constant shape.source constantLookup
  have originalConstant : original.defClif? y = some (.iconst ty' k) := by
    simp [Ctx.defClif?,constantDefined,constantFound,constantClif,constantInst]
  have entryMember := List.mem_of_getElem? shape.source
  have typeX := (spec.facts.types dominated.ssa).2 shape.entry entryMember _ memberX
  have parameterX := defInst_par spec.facts dominated.ssa shape.source (List.mem_map.mpr ⟨_,memberX,rfl⟩)
  have width : CTy.ofClif (if wide then .i64 else .i32) = .int (if wide then 64 else 32) := by
    cases wide <;> rfl
  refine ⟨cc,ty,x,y,wide,ty',k,?_,?_,?_,?_,equality,zero⟩
  · simpa only [Ctx.defClif?,Ctx.defInst?,view.valDef,view.insts] using originalClif
  · simpa only [Ctx.valueType?,view.valTy,width] using typeX
  · simpa only [Ctx.defInst?,view.valDef] using parameterX
  · simpa only [Ctx.defClif?,Ctx.defInst?,view.valDef,view.insts] using originalConstant

end Backend.Stock.ComparisonZeroCfg

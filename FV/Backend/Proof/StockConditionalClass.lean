import FV.Backend.Lowering.StockConditionalCfg
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.ConditionalCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Source facts for the first compatible conditional class. All describe
original source syntax; correctness and final-code compatibility are separate. -/
structure Shape (f : Clif.Function) where
  entry : Clif.Block
  condition : Nat
  yes : Clif.BlockCall
  no : Clif.BlockCall
  source : f.blocks[0]? = some entry
  term : entry.term = .brif condition yes no
  parameter : ∃ ty,(condition,ty) ∈ entry.params ∧ (ty = .i32 ∨ ty = .i64)
  targets : ∀ bc,bc = yes ∨ bc = no → bc.args = [] ∧
    ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl
  leaves : ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
    b.params = [] ∧ ∃ xs,b.term = .ret xs
  family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst
  abiParams : f.sig.params.all Scalar.narrowAbiEligible = true
  abiReturns : f.sig.returns.all Scalar.narrowAbiEligible = true

/-- The same source facts when each nonentry block returns or ends in `trap`. -/
structure LeafShape (f : Clif.Function) where
  entry : Clif.Block
  condition : Nat
  yes : Clif.BlockCall
  no : Clif.BlockCall
  source : f.blocks[0]? = some entry
  term : entry.term = .brif condition yes no
  parameter : ∃ ty,(condition,ty) ∈ entry.params ∧ (ty = .i32 ∨ ty = .i64)
  targets : ∀ bc,bc = yes ∨ bc = no → bc.args = [] ∧
    ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl
  leaves : ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
    b.params = [] ∧ ((∃ xs,b.term = .ret xs) ∨ ∃ c,b.term = .trap c)
  family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst
  abiParams : f.sig.params.all Scalar.narrowAbiEligible = true
  abiReturns : f.sig.returns.all Scalar.narrowAbiEligible = true

/-- Every return-leaf shape is a leaf shape with the same fields. -/
def Shape.toLeafShape {f : Clif.Function} (shape : Shape f) : LeafShape f where
  entry := shape.entry
  condition := shape.condition
  yes := shape.yes
  no := shape.no
  source := shape.source
  term := shape.term
  parameter := shape.parameter
  targets := shape.targets
  leaves := fun bi b found nonentry =>
    have leaf := shape.leaves bi b found nonentry
    ⟨leaf.1,Or.inl leaf.2⟩
  family := shape.family
  abiParams := shape.abiParams
  abiReturns := shape.abiReturns

private theorem target_sound {f : Clif.Function} {bc : Clif.BlockCall}
    (checked : targetEligible f bc = true) :
    bc.args = [] ∧ ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl := by
  simp only [targetEligible,Bool.and_eq_true] at checked
  have empty : bc.args = [] := List.isEmpty_iff.mp checked.1
  cases lookup : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp only [lookup] at checked; cases checked.2
  | some tl =>
    simp only [lookup,decide_eq_true_eq] at checked
    exact ⟨empty,tl,lookup,checked.2⟩

/-- The executable selector derives its source facts, without adding any
machine-code, source-state, selected-rule or semantic-result certificate. -/
theorem eligible_shape {f : Clif.Function} (checked : eligible f = true) : Nonempty (Shape f) := by
  cases blocks : f.blocks with
  | nil => simp [eligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [eligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨⟨parameter,yesGood⟩,noGood⟩,leaves⟩,bodies⟩,params⟩,returns⟩ := checked
      obtain ⟨pair,member,good⟩ := List.any_eq_true.mp parameter
      obtain ⟨value,ty⟩ := pair
      change (value == c && (ty == .i32 || ty == .i64)) = true at good
      simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at good
      obtain ⟨same,wide⟩ := good
      subst value
      refine ⟨{
        entry := entry
        condition := c
        yes := yes
        no := no
        source := by simp only [blocks,List.getElem?_cons_zero]
        term := term
        parameter := ⟨ty,member,wide⟩
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
        case ret xs => exact ⟨xs,rfl⟩
        all_goals cases good.2
      · intro b member stm present
        have member' : b ∈ entry :: rest := by simpa only [blocks] using member
        exact Scalar.maskMixedBodyEligible_sound
          (List.all_eq_true.mp (List.all_eq_true.mp bodies b member') stm present)
    all_goals cases checked

/-- The leaf selector derives the leaf source facts in the same way. -/
theorem leafEligible_shape {f : Clif.Function} (checked : leafEligible f = true) :
    Nonempty (LeafShape f) := by
  cases blocks : f.blocks with
  | nil => simp [leafEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [leafEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨⟨parameter,yesGood⟩,noGood⟩,leaves⟩,bodies⟩,params⟩,returns⟩ := checked
      obtain ⟨pair,member,good⟩ := List.any_eq_true.mp parameter
      obtain ⟨value,ty⟩ := pair
      change (value == c && (ty == .i32 || ty == .i64)) = true at good
      simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at good
      obtain ⟨same,wide⟩ := good
      subst value
      refine ⟨{
        entry := entry
        condition := c
        yes := yes
        no := no
        source := by simp only [blocks,List.getElem?_cons_zero]
        term := term
        parameter := ⟨ty,member,wide⟩
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

/-- Original entry-parameter membership and SSA derive the real built context's
parameter status and width, for every leaf shape. -/
theorem LeafShape.condition_metadata {f : Clif.Function} (shape : LeafShape f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.defInst? shape.condition = none ∧
      (ctx.valueType? shape.condition = some (.int 32) ∨ ctx.valueType? shape.condition = some (.int 64)) := by
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨ty,parameter,wide⟩ := shape.parameter
  have parameterId : shape.condition ∈ shape.entry.params.map (·.1) :=
    List.mem_map.mpr ⟨(shape.condition,ty),parameter,rfl⟩
  have noDefinition := defInst_par spec.facts dominated.ssa shape.source parameterId
  have originalType := (spec.facts.types dominated.ssa).2 shape.entry (List.mem_of_getElem? shape.source)
    (shape.condition,ty) parameter
  refine ⟨?_,?_⟩
  · simpa only [Ctx.defInst?,view.valDef] using noDefinition
  · have typed : ctx.valueType? shape.condition = some (CTy.ofClif ty) := by
      simpa only [Ctx.valueType?,view.valTy] using originalType
    rcases wide with rfl | rfl
    · exact Or.inl typed
    · exact Or.inr typed

/-- Original entry-parameter membership and SSA derive the real built context's
parameter status and width. No selected rule or DFG certificate is supplied. -/
theorem Shape.condition_metadata {f : Clif.Function} (shape : Shape f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.defInst? shape.condition = none ∧
      (ctx.valueType? shape.condition = some (.int 32) ∨ ctx.valueType? shape.condition = some (.int 64)) := by
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨ty,parameter,wide⟩ := shape.parameter
  have parameterId : shape.condition ∈ shape.entry.params.map (·.1) :=
    List.mem_map.mpr ⟨(shape.condition,ty),parameter,rfl⟩
  have noDefinition := defInst_par spec.facts dominated.ssa shape.source parameterId
  have originalType := (spec.facts.types dominated.ssa).2 shape.entry (List.mem_of_getElem? shape.source)
    (shape.condition,ty) parameter
  refine ⟨?_,?_⟩
  · simpa only [Ctx.defInst?,view.valDef] using noDefinition
  · have typed : ctx.valueType? shape.condition = some (CTy.ofClif ty) := by
      simpa only [Ctx.valueType?,view.valTy] using originalType
    rcases wide with rfl | rfl
    · exact Or.inl typed
    · exact Or.inr typed

end Backend.Stock.ConditionalCfg

import FV.Backend.Lowering.StockConditionalArgsCfg
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.ConditionalArgsCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Source facts for the conditional class whose branch may pass block arguments. All describe
original source syntax and the source-only block order. -/
structure ArgsLeafShape (f : Clif.Function) where
  entry : Clif.Block
  condition : Nat
  yes : Clif.BlockCall
  no : Clif.BlockCall
  source : f.blocks[0]? = some entry
  term : entry.term = .brif condition yes no
  parameter : ∃ ty,(condition,ty) ∈ entry.params ∧ (ty = .i32 ∨ ty = .i64)
  leaves : ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 → (∃ xs,b.term = .ret xs) ∨ ∃ c,b.term = .trap c
  family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst
  abiParams : f.sig.params.all Scalar.narrowAbiEligible = true
  abiReturns : f.sig.returns.all Scalar.narrowAbiEligible = true
  original : ∀ order,blockOrder f = .ok order → ∀ (label : Nat) (node : Node),order.nodes[label]? = some node →
    ∃ bi,node = .original bi

theorem originalOrder_sound {f : Clif.Function} (checked : originalOrder f = true) :
    ∀ order,blockOrder f = .ok order → ∀ (label : Nat) (node : Node),order.nodes[label]? = some node →
      ∃ bi,node = .original bi := by
  intro order run label node found
  simp only [originalOrder,run] at checked
  have good := (Array.all_eq_true_iff_forall_mem.mp checked) node (Array.mem_of_getElem? found)
  cases node with
  | original bi => exact ⟨bi,rfl⟩
  | edge => cases good

/-- The executable selector derives its source facts, without adding any machine-code,
source-state, selected-rule or semantic-result certificate. -/
theorem leafEligible_shape {f : Clif.Function} (checked : leafEligible f = true) :
    Nonempty (ArgsLeafShape f) := by
  cases blocks : f.blocks with
  | nil => simp [leafEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [leafEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨parameter,leaves⟩,bodies⟩,params⟩,returns⟩,ordered⟩ := checked
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
        leaves := ?_
        family := ?_
        abiParams := params
        abiReturns := returns
        original := originalOrder_sound ordered }⟩
      · intro bi b found nonentry
        have member : b ∈ rest := by
          cases bi with
          | zero => exact False.elim (nonentry rfl)
          | succ bi =>
            rw [blocks,List.getElem?_cons_succ] at found
            exact List.mem_of_getElem? found
        have good := List.all_eq_true.mp leaves b member
        cases term : b.term <;> simp only [term] at good
        case ret xs => exact Or.inl ⟨xs,rfl⟩
        case trap c => exact Or.inr ⟨c,rfl⟩
        all_goals cases good
      · intro b member stm present
        have member' : b ∈ entry :: rest := by simpa only [blocks] using member
        exact Scalar.maskMixedBodyEligible_sound
          (List.all_eq_true.mp (List.all_eq_true.mp bodies b member') stm present)
    all_goals cases checked

/-- Original entry-parameter membership and SSA derive the real built context's parameter
status and width. -/
theorem ArgsLeafShape.condition_metadata {f : Clif.Function} (shape : ArgsLeafShape f)
    (dominated : Dominated f) {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
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

end Backend.Stock.ConditionalArgsCfg

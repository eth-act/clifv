import FV.Backend.Proof.StockForwardReturn
import FV.Backend.Proof.StockForwardLeaf

namespace Backend.Stock.ConditionalCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original conditional entry with arbitrary ranked scalar jump/return tails. -/
structure RankedShape (f : Clif.Function) where
  entry : Clif.Block
  condition : Nat
  yes : Clif.BlockCall
  no : Clif.BlockCall
  source : f.blocks[0]? = some entry
  term : entry.term = .brif condition yes no
  parameter : ∃ ty,(condition,ty) ∈ entry.params ∧ (ty = .i32 ∨ ty = .i64)
  targets : ∀ bc,bc = yes ∨ bc = no → bc.args = [] ∧
    ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl
  tails : ForwardSource.NonentryJumpReturnBlocks f
  ranked : ForwardSource.Ranked f id
  family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst

/-- Original entry-parameter membership and SSA derive the real built context's
parameter status and width. No selected rule or DFG certificate is supplied. -/
theorem RankedShape.condition_metadata {f : Clif.Function} (shape : RankedShape f) (dominated : Dominated f)
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

/-- The same source facts when tail blocks may also end in `trap`. -/
structure RankedLeafShape (f : Clif.Function) where
  entry : Clif.Block
  condition : Nat
  yes : Clif.BlockCall
  no : Clif.BlockCall
  source : f.blocks[0]? = some entry
  term : entry.term = .brif condition yes no
  parameter : ∃ ty,(condition,ty) ∈ entry.params ∧ (ty = .i32 ∨ ty = .i64)
  targets : ∀ bc,bc = yes ∨ bc = no → bc.args = [] ∧
    ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl
  tails : ForwardSource.NonentryJumpLeafBlocks f
  ranked : ForwardSource.Ranked f id
  family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst

/-- Every return-tail shape is a leaf shape with the same fields. -/
def RankedShape.toLeaf {f : Clif.Function} (shape : RankedShape f) : RankedLeafShape f where
  entry := shape.entry
  condition := shape.condition
  yes := shape.yes
  no := shape.no
  source := shape.source
  term := shape.term
  parameter := shape.parameter
  targets := shape.targets
  tails := shape.tails.toLeaf
  ranked := shape.ranked
  family := shape.family

/-- Original entry-parameter membership and SSA derive the real built context's
parameter status and width. No selected rule or DFG certificate is supplied. -/
theorem RankedLeafShape.condition_metadata {f : Clif.Function} (shape : RankedLeafShape f) (dominated : Dominated f)
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

import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.LowerCertBase

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Original SSA gives parameter-branch metadata for any source block. -/
theorem parameter_condition_metadata_ssa {f : Clif.Function} {bi : Nat}
    {b : Clif.Block} {c : Nat} {ty : Clif.Ty}
    (ssa : (valueDefs f).Nodup) (block : f.blocks[bi]? = some b)
    (parameter : (c,ty) ∈ b.params) (wide : ty = .i32 ∨ ty = .i64)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.defInst? c = none ∧
      (ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64)) := by
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  have parameterId : c ∈ b.params.map (·.1) := List.mem_map.mpr ⟨(c,ty),parameter,rfl⟩
  have noDefinition := defInst_par spec.facts ssa block parameterId
  have originalType := (spec.facts.types ssa).2 b (List.mem_of_getElem? block) (c,ty) parameter
  refine ⟨?_,?_⟩
  · simpa only [Ctx.defInst?,view.valDef] using noDefinition
  · have typed : ctx.valueType? c = some (CTy.ofClif ty) := by
      simpa only [Ctx.valueType?,view.valTy] using originalType
    rcases wide with rfl | rfl
    · exact Or.inl typed
    · exact Or.inr typed

/-- The original-input variant remains available. -/
theorem parameter_condition_metadata {f : Clif.Function} {bi : Nat}
    {b : Clif.Block} {c : Nat} {ty : Clif.Ty}
    (dominated : Dominated f) (block : f.blocks[bi]? = some b)
    (parameter : (c,ty) ∈ b.params) (wide : ty = .i32 ∨ ty = .i64)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.defInst? c = none ∧
      (ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64)) :=
  parameter_condition_metadata_ssa dominated.ssa block parameter wide build


end Backend.Stock.Proof.ParameterCfg

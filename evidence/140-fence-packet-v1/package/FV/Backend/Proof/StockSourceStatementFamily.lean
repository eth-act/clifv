import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Every original source instruction visible in an actual scan belongs to the
original function's statement family. Synthetic placeholders cannot supply an
original instruction. This derives family-based pattern exclusions from syntax. -/
theorem stock_lower_source_statement_family {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (P : Clif.Inst → Prop)
    (family : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, P stm.inst)
    {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[i]? = some info) (clif : info.clif = some inst) : P inst := by
  have globalSource := (stock_lower_record_context run scope events).2.2 _ _ _ source clif
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨model,_,_,_⟩ := buildCtx_model oldBuild
  have table : (ctxModel f (maxVOf f)).2.2.1 = (instsOf f f.blocks).toArray := by
    unfold ctxModel
    rw [blockFold]
    simp only [Array.empty_append]
  have originalSource : original.insts[i]? = some info := by
    rw [← view.insts]; exact globalSource
  rw [congrArg Ctx.insts model,table] at originalSource
  have member : info ∈ instsOf f f.blocks := by
    exact List.mem_of_getElem? (by simpa using originalSource)
  rcases instsOf_mem member with rfl | ⟨b,block,stm,statement,rfl⟩
  · cases clif
  · have same : stm.inst = inst := Option.some.inj clif
    rw [← same]
    exact family b block stm statement
end Backend.Stock.Proof

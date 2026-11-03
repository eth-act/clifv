import FV.Backend.Proof.StockAcquireSourceValuePersistence

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem source_steps_cons_inv {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {inst : Nat} {indices : List Nat} {before after : Clif.Frame × Clif.Mem}
    (steps : SourceSteps (SourceInstResult env p ctx) (inst::indices) before after) :
    ∃ middle,SourceInstResult env p ctx inst before middle ∧
      SourceSteps (SourceInstResult env p ctx) indices middle after := by
  cases steps with
  | cons head tail => exact ⟨_,head,tail⟩

/-- Actual atomic binding and original SSA preserve the loaded value across the entire source suffix. -/
theorem source_atomic_loaded_prefix {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (ssa : (valueDefs f).Nodup)
    {bi j value : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (result : value ∈ stm.results) {info : IInfo} {ty : Clif.Ty} {flags : Clif.MemFlags} {pointer : Nat}
    (defined : ctx.defInst? value = some (blockStart f bi+j))
    (installed : ctx.insts[blockStart f bi+j]? = some info)
    (source : info.clif = some (.atomicLoad ty flags pointer)) (little : flags.endianness ≠ some .big)
    {env : Clif.Env} {p : Clif.Program} {indices : List Nat} {before after : Clif.Frame × Clif.Mem}
    (body : before.1.body = block.body.drop j)
    (steps : SourceSteps (SourceInstResult env p ctx) ((blockStart f bi+j)::indices) before after) :
    ∃ small,Clif.evalInst before.1 before.2 (.atomicLoad ty flags pointer) = .ok ([small],before.2) ∧
      after.1.regs value = some small := by
  obtain ⟨middle,head,tail⟩ := source_steps_cons_inv steps
  have results := mapped_atomic_result_singleton mapped defined installed source
  obtain ⟨small,executed,loaded,memory⟩ := source_atomic_result_value installed source results little head
  have safe := ssa_value_unwritten_after_definition ssa blockAt statement result
  obtain ⟨actualInfo,actual,values,regs,rest,found,original,remaining,evaluated,updated,frame⟩ := head
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have stmEq := (List.getElem?_eq_some_iff.mp statement).2
  have expected : before.1.body = stm::block.body.drop (j+1) := by
    rw [body,List.drop_eq_getElem_cons inside,stmEq]
  have tailEq := (List.cons.inj (remaining.symm.trans expected)).2
  have middleBody : middle.1.body = block.body.drop (j+1) := by rw [frame,tailEq]
  have kept := source_steps_pointer_frame (pointer := value) tail (by rw [middleBody];exact safe)
  refine ⟨small,?_,kept.1.trans loaded⟩
  simpa only [memory] using executed

end Backend.Stock.Proof.Acquire810

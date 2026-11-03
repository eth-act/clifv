import FV.Backend.Proof.StockAcquirePositionedSourceTrap

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original SSA prevents any later source statement from replacing the selected value. -/
theorem ssa_value_unwritten_after_definition {f : Clif.Function}
    (ssa : (valueDefs f).Nodup) {bi j value : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (result : value ∈ stm.results) : PointerUnwritten value (block.body.drop (j+1)) := by
  intro later member written
  obtain ⟨offset,found⟩ := List.mem_iff_getElem?.mp member
  rw [List.getElem?_drop] at found
  have unique := (res_unique ssa blockAt statement result blockAt found written).2
  omega

/-- Actual source result binding preserves the original frame slots through any successful prefix. -/
theorem source_steps_slots_frame {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {indices : List Nat} {before after : Clif.Frame × Clif.Mem}
    (steps : SourceSteps (SourceInstResult env p ctx) indices before after) : after.1.slots = before.1.slots := by
  induction steps with
  | nil state => rfl
  | cons head tail ih =>
    obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,updated,frame⟩ := head
    exact ih.trans (congrArg Clif.Frame.slots frame)

/-- Original atomic typing and its actual definition derive the single named result internally. -/
theorem mapped_atomic_result_singleton {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {producer value : Nat} {info : IInfo}
    {ty : Clif.Ty} {flags : Clif.MemFlags} {pointer : Nat}
    (defined : ctx.defInst? value = some producer) (installed : ctx.insts[producer]? = some info)
    (source : info.clif = some (.atomicLoad ty flags pointer)) : info.results = [value] := by
  obtain ⟨tys,types,resultTypes,length⟩ := mapped.resTys producer info _ installed source
  have tysEq : tys = [ty] := by simpa only [Clif.Inst.resultTypes,Option.some.injEq] using types.symm
  rw [tysEq] at length
  obtain ⟨actual,found,member⟩ := mapped.defInst value producer defined
  have equal := Option.some.inj (found.symm.trans installed)
  rw [equal] at member
  obtain ⟨result,results⟩ := List.length_eq_one.mp length
  rw [results] at member
  have same : value = result := List.mem_singleton.mp member
  simpa only [same] using results

/-- Actual atomic execution binds the loaded bits and preserves memory at the original source step. -/
theorem source_atomic_result_value {ctx : Ctx} {producer value : Nat} {info : IInfo}
    {ty : Clif.Ty} {flags : Clif.MemFlags} {pointer : Nat} {env : Clif.Env} {p : Clif.Program}
    (installed : ctx.insts[producer]? = some info) (source : info.clif = some (.atomicLoad ty flags pointer))
    (results : info.results = [value]) (little : flags.endianness ≠ some .big)
    {before after : Clif.Frame × Clif.Mem}
    (step : SourceInstResult env p ctx producer before after) :
    ∃ (small : Clif.Val),Clif.evalInst before.1 before.2 (.atomicLoad ty flags pointer) = .ok ([small],after.2) ∧
      after.1.regs value = some small ∧ after.2 = before.2 := by
  obtain ⟨actual,inst,values,regs,rest,found,original,body,evaluated,updated,frame⟩ := step
  have infoEq := Option.some.inj (found.symm.trans installed)
  subst actual
  have instEq := Option.some.inj (original.symm.trans source)
  subst inst
  change Clif.evalInst before.1 before.2 (.atomicLoad ty flags pointer) = .ok (values,after.2) at evaluated
  obtain ⟨pv,raw,pointerValue,valid,read,valuesEq,memory⟩ := evalInst_atomicLoad_inv little evaluated
  have bound := setMany_nodup updated (by simp only [results,List.nodup_singleton]) 0 value ⟨ty,raw⟩
    (by simp only [results,List.getElem?_cons_zero]) (by simp only [valuesEq,List.getElem?_cons_zero])
  refine ⟨⟨ty,raw⟩,?_,?_,memory⟩
  · simpa only [valuesEq] using evaluated
  · rw [frame]
    exact bound

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockAcquireSelectedSingleton
import FV.Backend.Proof.StockAcquireForwardFrontiers
import FV.Backend.Proof.StockAcquireSourcePointerFrame
import FV.Backend.Proof.IselAtomic

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual successful atomic source execution exposes its read and leaves memory unchanged. -/
theorem atomic_source_step_read {ctx : Ctx} {producer pointer : Nat} {info : IInfo}
    {ty : Clif.Ty} {flags : Clif.MemFlags} {env : Clif.Env} {p : Clif.Program}
    (installed : ctx.insts[producer]? = some info)
    (original : info.clif = some (.atomicLoad ty flags pointer))
    (little : flags.endianness ≠ some .big)
    {before after : Clif.Frame × Clif.Mem}
    (step : SourceInstResult env p ctx producer before after) :
    ∃ pv raw,before.1.regs pointer = some pv ∧
      before.2.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      before.2.readBits false (Clif.effAddr pv 0) ty.bytes ty.width = some raw ∧
      after.2 = before.2 := by
  obtain ⟨actualInfo,inst,values,regs,rest,found,source,body,evaluated,updated,frame⟩ := step
  have same : actualInfo = info := Option.some.inj (found.symm.trans installed)
  subst actualInfo
  have instruction : inst = .atomicLoad ty flags pointer := Option.some.inj (source.symm.trans original)
  subst inst
  change Clif.evalInst before.1 before.2 (.atomicLoad ty flags pointer) = .ok (values,after.2) at evaluated
  obtain ⟨pv,raw,pointerValue,valid,read,valuesEq,memory⟩ := evalInst_atomicLoad_inv little evaluated
  exact ⟨pv,raw,pointerValue,valid,read,memory⟩

/-- Retained root810 selection derives the original atomic source read contract internally. -/
theorem stock_lower_acquire_selected_source_read {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (value producer : Nat) (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      event.ctx.defInst? value = some producer ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ eTy ty = true ∧ flags.endianness ≠ some .big ∧
      ∀ (env : Clif.Env) (p : Clif.Program) (before after : Clif.Frame × Clif.Mem),
        SourceInstResult env p event.ctx producer before after →
        ∃ pv raw,before.1.regs pointer = some pv ∧
          before.2.valid (Clif.effAddr pv 0) ty.bytes = true ∧
          before.2.readBits false (Clif.effAddr pv 0) ty.bytes ty.width = some raw ∧ after.2 = before.2 := by
  obtain ⟨value,producer,info,ty,flags,pointer,out,next,fired,
    defined,once,installed,source,integer,little,root,pending,sunk,color⟩ :=
    stock_lower_acquire_selected_singleton run scope events records recorded emitted selectedId
  refine ⟨value,producer,info,ty,flags,pointer,defined,installed,source,integer,little,?_⟩
  intro env p before after executed
  exact atomic_source_step_read installed source little executed

end Backend.Stock.Proof.Acquire810

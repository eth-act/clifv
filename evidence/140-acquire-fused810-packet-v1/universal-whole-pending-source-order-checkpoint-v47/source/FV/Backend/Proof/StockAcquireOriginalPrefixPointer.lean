import FV.Backend.Proof.StockAcquireSourcePointerFrame
import FV.Backend.Proof.StockAcquireOriginalStatement

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual selection and original dominance derive pointer equality across the producer's source prefix. -/
theorem stock_lower_acquire_original_prefix_pointer {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (value producer bi : Nat) (block : Clif.Block) (j : Nat) (stm : Clif.Stmt)
      (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      f.blocks[bi]? = some block ∧ block.body[j]? = some stm ∧ value ∈ stm.results ∧
      producer = blockStart f bi+j ∧ stm.inst = .atomicLoad ty flags pointer ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      ∀ (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (indices : List Nat)
        (before after : Clif.Frame × Clif.Mem),
        before.1.body = block.body.drop j →
        SourceSteps (SourceInstResult env p ctx) indices before after →
        after.1.regs pointer = before.1.regs pointer := by
  obtain ⟨value,producer,bi,block,j,stm,ty,flags,pointer,blockAt,statement,valueResult,
    position,source,integer,little⟩ :=
    stock_lower_acquire_selected_original_statement run scope events records recorded emitted selectedId
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeIndex,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have pointerUse : pointer ∈ Driver.instArgs stm.inst := by
    rw [source]
    simp only [Driver.instArgs,List.mem_singleton]
  have available := (dominated.uses original ranges st0 oldBuild bi block blockAt).1
    j stm statement pointer pointerUse
  refine ⟨value,producer,bi,block,j,stm,ty,flags,pointer,blockAt,statement,valueResult,
    position,source,integer,little,?_⟩
  intro env p ctx indices initialState finalState body steps
  exact available_source_prefix_pointer blockAt available body steps

end Backend.Stock.Proof.Acquire810

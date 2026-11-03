import FV.Backend.Proof.StockAcquireBareSourceSlice

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual successful bare source execution derives interval memory equality from retained acquire selection. -/
theorem stock_lower_acquire_actual_successful_slice_memory {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (value producer : Nat) (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      event.ctx.defInst? value = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      ∀ (bi start count : Nat) (block : Clif.Block),f.blocks[bi]? = some block →
        start+count ≤ block.body.length → producer ≤ blockStart f bi+start →
        blockStart f bi+(start+count) ≤ record.inst →
        ∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (values : List Clif.Val) (memory : Clif.Mem),
          s.frame.body = block.body.drop start →
          Clif.runLoop env {funcs := []} fuel s = .returned values memory →
          ∃ t left,left+count = fuel ∧ Clif.runLoop env {funcs := []} left t = .returned values memory ∧
            t.frame.body = block.body.drop (start+count) ∧ t.mem = s.mem := by
  obtain ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,
    integer,little,frames⟩ := stock_lower_acquire_between_statement_read_frames run scope events records recorded emitted selectedId
  have view := stock_lower_event_build_source_slots run scope events built
  refine ⟨value,producer,info,ty,flags,pointer,defined,installed,source,integer,little,?_⟩
  intro bi start count block blockAt inside lower upper env fuel s values memory remaining returned
  have slots : ∀ j stm,block.body[j]? = some stm →
      ∃ actualInfo,event.ctx.insts[blockStart f bi+j]? = some actualInfo ∧
        actualInfo.clif = some stm.inst ∧ actualInfo.results = stm.results := by
    intro j stm statement
    obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of built).facts.stmt bi block j stm blockAt statement
    exact ⟨actualInfo,view _ actualInfo stm.inst present actualSource,actualSource,results⟩
  obtain ⟨t,left,total,ends,body,steps⟩ := bare_returned_source_slice slots count inside remaining returned
  refine ⟨t,left,total,ends,body,?_⟩
  apply source_steps_read_memory steps
  intro slot member
  obtain ⟨offset,offsetBound,equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  have statementBound : start+offset < block.body.length := by omega
  have statement : block.body[start+offset]? = some block.body[start+offset] := List.getElem?_eq_getElem statementBound
  have read := frames bi (start+offset) block block.body[start+offset] blockAt statement (by omega) (by omega)
  simpa only [equal,Nat.add_assoc] using read

end Backend.Stock.Proof.Acquire810

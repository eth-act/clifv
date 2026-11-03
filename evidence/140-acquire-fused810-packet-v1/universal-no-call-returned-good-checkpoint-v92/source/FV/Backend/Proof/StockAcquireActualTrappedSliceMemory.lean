import FV.Backend.Proof.StockAcquireBareTrappedSlice

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Retained selection derives unchanged memory at the first source fault or exact slice continuation. -/
theorem stock_lower_acquire_actual_trapped_slice_memory {f : Clif.Function} {result : Result}
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
        ∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode),
          s.frame.body = block.body.drop start →
          Clif.runLoop env {funcs := []} fuel s = .trapped code →
          (∃ (front : List Nat) (slot : Nat) (suffix : List Nat) (atFault : Clif.Frame × Clif.Mem),
            List.range' (blockStart f bi+start) count = front++slot::suffix ∧
            SourceSteps (SourceInstResult env {funcs := []} event.ctx) front (s.frame,s.mem) atFault ∧
            SourceInstFault env {funcs := []} event.ctx slot atFault code ∧ atFault.2 = s.mem) ∨
          ∃ t left,left+count = fuel ∧ Clif.runLoop env {funcs := []} left t = .trapped code ∧
            t.frame.body = block.body.drop (start+count) ∧ t.mem = s.mem := by
  obtain ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,
    integer,little,frames⟩ := stock_lower_acquire_between_statement_read_frames run scope events records recorded emitted selectedId
  have view := stock_lower_event_build_source_slots run scope events built
  refine ⟨value,producer,info,ty,flags,pointer,defined,installed,source,integer,little,?_⟩
  intro bi start count block blockAt inside lower upper env fuel s code remaining trapped
  have slots : ∀ j stm,block.body[j]? = some stm →
      ∃ actualInfo,event.ctx.insts[blockStart f bi+j]? = some actualInfo ∧
        actualInfo.clif = some stm.inst ∧ actualInfo.results = stm.results := by
    intro j stm statement
    obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of built).facts.stmt bi block j stm blockAt statement
    exact ⟨actualInfo,view _ actualInfo stm.inst present actualSource,actualSource,results⟩
  have reads : ∀ slot ∈ List.range' (blockStart f bi+start) count,SourceReadFrame event.ctx slot := by
    intro slot member
    obtain ⟨offset,offsetBound,equal⟩ := List.mem_range'.mp member
    simp only [Nat.one_mul] at equal
    have statementBound : start+offset < block.body.length := by omega
    have statement : block.body[start+offset]? = some block.body[start+offset] := List.getElem?_eq_getElem statementBound
    have read := frames bi (start+offset) block block.body[start+offset] blockAt statement (by omega) (by omega)
    simpa only [equal,Nat.add_assoc] using read
  rcases bare_trapped_source_slice slots count inside remaining trapped with early | ⟨t,left,total,ends,body,steps⟩
  · exact Or.inl (source_first_trap_read_memory early reads)
  · exact Or.inr ⟨t,left,total,ends,body,source_steps_read_memory steps reads⟩

end Backend.Stock.Proof.Acquire810

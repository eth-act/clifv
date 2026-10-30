import FV.Backend.Proof.StockEntrySeed
import FV.Backend.Proof.StockEntryABI
import FV.Backend.Proof.StockEntryCode
import FV.Backend.Proof.StockCoreScanOrigin

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
attribute [local irreducible] Stock.runTerm Isle.Aarch64.program branchArgs emitBranch collectOutgoing scanBlock

private theorem core_scan_suffix {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    ∃ after, core.code = core.scan.output.code ++ after := by
  unfold lowerBlockCore at run
  dsimp only at run
  split at run
  all_goals
    obtain ⟨branch,branchRun,rest⟩ := Except.bind_ok run
    obtain ⟨pair,edgeRun,rest⟩ := Except.bind_ok rest
    rcases pair with ⟨next,outgoing⟩
    obtain ⟨scan,scanRun,rest⟩ := Except.bind_ok rest
    cases rest
    exact ⟨_,rfl⟩

/-- Successful original entry and actual Stock construction derive execution
of the emitted block-zero ABI prelude. All source values survive, including
unused parameters. No entry-code, per-row ABI or initial-value certificate is
supplied by the caller; the initial virtual file is selected inside the proof. -/
theorem stock_lower_entry_prelude_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ (event : BlockScanEvent) (block : VBlock) (prelude body : Array MInst)
      (ρ' : Nat → CV) (w' : Arm.ArmState),
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧
      result.code.blocks[0]? = some block ∧ block.insts = prelude ++ body ∧
      seqRun isem prelude.toList (entrySeed event.ctx fr) w = some (.fall ρ' w') ∧
      MR fr.slots cm w' ∧ ValuesHeld (fun _ => True) event.ctx fr ρ' ∧ SameWorld F w' w ∧
      ∃ after, body = event.output.code.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ after := by
  obtain ⟨ranges,bytes,before,data,core,raw,block,sizes,build,coreRun,assembled,events,
    atBlock,blockCode⟩ := stock_lower_entry_assembly run scope
  have inv := buildCtx_mappedInv scope build
  have entryFacts := entered
  obtain ⟨b,regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have sourceBlock : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  have blockValue : f.blocks[0]! = b := by
    rw [List.getElem!_eq_getElem?_getD,sourceBlock]
    rfl
  rw [blockValue] at assembled
  obtain ⟨locs,stack,rows,locations,mapped,ordered,lookups,rawCode⟩ :=
    assemble_entry_source_rows assembled
  let prelude := entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have fixed : prelude.map (·.mapRegs resolve) = prelude := by
    apply mapped_entry_prelude_fixed resolve
    intro row member
    have original : row.input ∈ (b.params.zip locs).zip bytes :=
      ordered.subset (List.mem_map.mpr ⟨row,member,rfl⟩)
    have parameter : row.input.1.1.1 ∈ b.params.map (·.1) :=
      List.mem_map.mpr ⟨row.input.1.1,(List.of_mem_zip (List.of_mem_zip original).1).1,rfl⟩
    obtain ⟨rowReg,rowMap⟩ := mapped_entry_reg inv mapped member
    have alias := stock_lower_parameter_resolves run dominated.ssa sourceBlock parameter rowMap
    rw [rowReg]
    change Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
      (.vreg (entryRowKey row) .int) = .vreg (entryRowKey row) .int
    rw [resolve_vreg]
    change Reg.vreg (aliasNum result.final.alias (entryRowKey row)) .int = _
    rw [alias]
  have maps := (stock_lower_record_context run scope events).2.1
  have held : ValuesHeld (fun _ => True) result.ctx fr (entrySeed core.scan.ctx fr) := by
    intro x _ v found
    obtain ⟨key,mapped,value⟩ := entrySeed_entered_values_frame run scope dominated events entered x trivial v found
    exact ⟨key,by rwa [maps] at mapped,value⟩
  obtain ⟨ρ',w',execution,mem,values,same⟩ := mapped_entry_prelude_preserves_frame inv entered
    dominated.ssa sourceBlock locations sizes mapped driver memorySem stable held memory arguments
  refine ⟨core.scan,block,prelude,core.code.map (·.mapRegs resolve),ρ',w',events,
    (stock_lowerBlockCore_scanOrigin coreRun).2.2.1,atBlock,?_,execution,mem,?_,same,?_⟩
  · rw [blockCode,rawCode]
    change (prelude ++ core.code).map (·.mapRegs resolve) = _
    rw [Array.map_append,fixed]
  · intro x _ v found
    obtain ⟨key,mapped,value⟩ := values x trivial v found
    exact ⟨key,by rwa [← maps] at mapped,value⟩
  · obtain ⟨after,pieces⟩ := core_scan_suffix coreRun
    exact ⟨after.map (·.mapRegs resolve),by rw [pieces,Array.map_append]⟩

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem stock_lower_entry_prelude_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ (event : BlockScanEvent) (block : VBlock) (prelude body : Array MInst)
      (ρ' : Nat → CV) (w' : Arm.ArmState),
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧
      result.code.blocks[0]? = some block ∧ block.insts = prelude ++ body ∧
      seqRun isem prelude.toList (entrySeed event.ctx fr) w = some (.fall ρ' w') ∧
      MR fr.slots cm w' ∧ ValuesHeld (fun _ => True) event.ctx fr ρ' ∧ SameWorld F w' w ∧
      ∃ after, body = event.output.code.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ after := by
  exact stock_lower_entry_prelude_refines_frame run scope dominated (SourceEntry.of_enterFunc entered) driver memorySem stable memory arguments

/-- The source relation after ABI materialization follows from ordinary entered
values. Final aliases fix original parameters, so callers need no resolved-value
certificate for the later body simulation. -/
theorem stock_lower_entered_values_guarded_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {ρ : Nat → CV} (held : ValuesHeld (fun _ => True) event.ctx fr ρ)
    (st : State) {MR : MemRelT} (w : Arm.ArmState) (memory : MR fr.slots cm w) :
    GuardedScanRel f result event.ctx event.block MR st (0,fr,cm) ρ w := by
  have entryFacts := entered
  obtain ⟨b,regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have frameRegs : fr.regs = regs := congrArg (fun frame : Clif.Frame => frame.regs) frame
  have block : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  refine ⟨congrArg (fun frame : Clif.Frame => frame.func) frame,
    stock_lower_entered_restrict_dfg_frame run dominated events entered _,memory,?_⟩
  intro x _ v found
  obtain ⟨key,mapped,value⟩ := held x trivial v found
  have parameter : x ∈ b.params.map (·.1) := by
    by_cases member : x ∈ b.params.map (·.1)
    · exact member
    · have lookup : regs x = some v := by simpa only [frameRegs] using found
      rw [setMany_other set member] at lookup
      cases lookup
  have resultMap : result.ctx.valueReg? x = some (.vreg key .int) := by
    rw [← (stock_lower_record_context run scope events).2.1 x]
    exact mapped
  have fixed := stock_lower_parameter_resolves run dominated.ssa block parameter resultMap
  refine ⟨key,mapped,?_⟩
  dsimp only
  rw [fixed]
  exact value

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem stock_lower_entered_values_guarded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    {ρ : Nat → CV} (held : ValuesHeld (fun _ => True) event.ctx fr ρ)
    (st : State) {MR : MemRelT} (w : Arm.ArmState) (memory : MR fr.slots cm w) :
    GuardedScanRel f result event.ctx event.block MR st (0,fr,cm) ρ w := by
  exact stock_lower_entered_values_guarded_frame run scope dominated events (SourceEntry.of_enterFunc entered) held st w memory

end Backend.Stock.Proof

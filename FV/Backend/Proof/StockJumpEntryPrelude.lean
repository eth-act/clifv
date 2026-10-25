import FV.Backend.Proof.StockEntryPrelude
import FV.Backend.Proof.StockJumpBodyRefines
import FV.Backend.Proof.PerEdgeSeq

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Execute the ABI prelude of the very same canonical entry core used by
the body/jump proof. Its actual assembly, source parameter aliases and entry
values establish the body guard at the exact instruction offset. -/
theorem jump_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {bc : Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b 0 0 bc isem MR env cp)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w',Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨0,0,entrySeed spec.core.scan.ctx fr,w⟩)
      (.run ⟨0,spec.preludeCode.size,ρ',w'⟩) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
        spec.core.scan.output.state (0,fr,cm) ρ' w' ∧
      ValuesHeld (fun _ => True) spec.core.scan.ctx fr
        (fun key => ρ' (aliasNum result.final.alias key)) ∧ SameWorld F w' w := by
  have inv := buildCtx_mappedInv scope spec.build
  have sourceBlock : f.blocks[0]? = some b := by simpa only [spec.atBlock] using spec.split.block
  obtain ⟨locs,stack,rows,locations,mapped,ordered,lookups,rawCode⟩ :=
    assemble_entry_source_rows spec.assembled
  let prelude := entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have fixed : prelude.map (·.mapRegs resolve) = prelude := by
    apply mapped_entry_prelude_fixed resolve
    intro row member
    have original : row.input ∈ (b.params.zip locs).zip spec.params :=
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
  have maps := (stock_lower_record_context run scope spec.events).2.1
  have held : ValuesHeld (fun _ => True) result.ctx fr (entrySeed spec.core.scan.ctx fr) := by
    intro x _ v found
    obtain ⟨key,mapped,value⟩ := entrySeed_entered_values_frame run scope dominated spec.events entered x trivial v found
    exact ⟨key,by rwa [maps] at mapped,value⟩
  obtain ⟨ρ',w',execution,mem,values,same⟩ := mapped_entry_prelude_preserves_frame inv entered
    dominated.ssa sourceBlock locations spec.sizes mapped driver memorySem stable held memory arguments
  have preludeEq : spec.preludeCode = prelude :=
    (Array.append_left_inj spec.core.code).mp (spec.rawCode.symm.trans (congrArg VBlock.insts rawCode))
  let vb : VBlock := {spec.raw with
    insts := spec.raw.insts.map (·.mapRegs resolve)
    params := spec.raw.params.map resolve
    branchArgs := spec.raw.branchArgs.map resolve}
  have parts : vb.insts = prelude ++ spec.core.code.map (·.mapRegs resolve) := by
    dsimp only [vb]
    rw [rawCode]
    change (prelude ++ spec.core.code).map (·.mapRegs resolve) = _
    rw [Array.map_append,fixed]
  have segment : SegAt vb 0 prelude.toList := by
    intro k hk
    have bound : k < prelude.size := by simpa using hk
    simp only [Nat.zero_add,parts]
    rw [Array.getElem?_append_left bound]
    simp [bound]
  have room : 0+prelude.toList.length < vb.insts.size := by
    simp only [parts,spec.bodyCode,Array.length_toList,Array.size_append,Array.size_map,Array.size_singleton]
    omega
  have path := seqRun_fall_starAt (edges := result.edgeArgs) spec.placed segment room execution
  have values' : ValuesHeld (fun _ => True) spec.core.scan.ctx fr ρ' := by
    intro x needed v found
    obtain ⟨key,mapped,value⟩ := values x needed v found
    exact ⟨key,by rwa [← maps] at mapped,value⟩
  have resolvedValues : ValuesHeld (fun _ => True) spec.core.scan.ctx fr
      (fun key => ρ' (aliasNum result.final.alias key)) := by
    obtain ⟨sourceB,regs,entry,argTypes,paramTypes,set,frame⟩ := entered
    have sourceAt : f.blocks[0]? = some sourceB := by
      simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
    cases Option.some.inj (sourceAt.symm.trans sourceBlock)
    intro x needed v read
    obtain ⟨key,mapped,value⟩ := values' x needed v read
    have parameter : x ∈ b.params.map (·.1) := by
      by_cases member : x ∈ b.params.map (·.1)
      · exact member
      · have frameRegs : fr.regs = regs := congrArg (fun frame : Clif.Frame => frame.regs) frame
        have lookup : regs x = some v := by rwa [← frameRegs]
        rw [setMany_other set member] at lookup
        cases lookup
    have resultMap : result.ctx.valueReg? x = some (.vreg key .int) := by
      rwa [← maps]
    have alias := stock_lower_parameter_resolves run dominated.ssa sourceBlock parameter resultMap
    refine ⟨key,mapped,?_⟩
    dsimp only
    rw [alias]
    exact value
  refine ⟨ρ',w',?_,stock_lower_entered_values_guarded_frame run scope dominated spec.events entered
    values' spec.core.scan.output.state w' mem,resolvedValues,same⟩
  simpa only [preludeEq,Nat.zero_add,Array.length_toList] using path

theorem source_defined_entry_frame {f : Clif.Function} (dominated : Dominated f) (ctx : Ctx)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) : SourceDefinedAt f ctx 0 0 fr := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  simp only [Clif.Function.entry?,List.head?_eq_getElem?] at entry
  have nodup : (b.params.map (·.1)).Nodup := (List.nodup_append.mp (block_nodup dominated.ssa entry)).1
  intro x available
  obtain ⟨present,_⟩ := (mem_av entry).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · obtain ⟨_,v,_,_,value⟩ := setMany_mem set nodup x parameter
    refine ⟨v,?_⟩
    rw [frame]
    exact value
  · have bound := (inFix_fixOk (f := f) (ctx := ctx) (gn := id)).cand 0 x incoming
    omega
  · omega

end Backend.Stock.Proof.Control

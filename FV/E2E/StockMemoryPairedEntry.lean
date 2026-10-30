import FV.E2E.StockMemoryRegisterPrelude

namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
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

/-- Actual Stock entry assembly derives the paired register prelude and its
shared virtual file from original ABI argument agreement. -/
theorem stock_lower_entry_prelude_paired_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    ∃ (event : BlockScanEvent) (block : VBlock) (prelude body : Array MInst)
      (ρ' : Nat → CV),
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧
      result.code.blocks[0]? = some block ∧ block.insts = prelude ++ body ∧
      seqRun (pairSem (csem Γ.F fc X)) prelude.toList (entrySeed event.ctx fr) (w,w') = some (.fall ρ' (w,w')) ∧
      ValuesHeld (fun _ => True) event.ctx fr ρ' ∧
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
  obtain ⟨ρ',execution,values⟩ := mapped_entry_register_prelude_paired_frame inv entered
    dominated.ssa sourceBlock locations sizes mapped registerOnly slot symbols held memory arguments otherArguments registers
  refine ⟨core.scan,block,prelude,core.code.map (·.mapRegs resolve),ρ',events,
    (stock_lowerBlockCore_scanOrigin coreRun).2.2.1,atBlock,?_,execution,?_,?_⟩
  · rw [blockCode,rawCode]
    change (prelude ++ core.code).map (·.mapRegs resolve) = _
    rw [Array.map_append,fixed]
  · intro x _ v found
    obtain ⟨key,mapped,value⟩ := values x trivial v found
    exact ⟨key,by rwa [← maps] at mapped,value⟩
  · obtain ⟨after,pieces⟩ := core_scan_suffix coreRun
    exact ⟨after.map (·.mapRegs resolve),by rw [pieces,Array.map_append]⟩


end E2E.StockMemory

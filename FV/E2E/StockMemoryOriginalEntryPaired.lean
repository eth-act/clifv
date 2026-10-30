import FV.Backend.Proof.StockOriginalEntryPrelude
import FV.E2E.StockMemoryPairedEntry

namespace E2E.StockMemory
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof Backend.Stock.Proof.Control
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The chosen actual entry core supplies its paired ABI prefix and guarded values.
Both worlds execute the same prefix with one shared virtual register file. -/
theorem original_entry_prelude_paired {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (spec : EntryCoreSpec f result b)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    ∃ ρ',Star (VStepAt result.code result.edgeArgs (pairSem (csem Γ.F fc X)))
      (.run ⟨0,0,entrySeed spec.core.scan.ctx fr,(w,w')⟩)
      (.run ⟨0,spec.preludeCode.size,ρ',(w,w')⟩) ∧
      PairedScanRel f result spec.core.scan.ctx spec.core.scan.block Γ c D
        spec.core.scan.output.state (0,fr,cm) ρ' (w,w') := by
  have inv := buildCtx_mappedInv scope spec.build
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
    have alias := stock_lower_parameter_resolves run dominated.ssa spec.block parameter rowMap
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
  obtain ⟨ρ',execution,values⟩ := mapped_entry_register_prelude_paired_frame inv entered dominated.ssa
    spec.block locations spec.sizes mapped registerOnly slot symbols held memory arguments otherArguments registers
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
    simp only [parts,Array.length_toList,Array.size_append,Array.size_map]
    have nonempty := spec.nonempty
    omega
  have path := seqRun_fall_starAt (edges := result.edgeArgs) spec.placed segment room execution
  have values' : ValuesHeld (fun _ => True) spec.core.scan.ctx fr ρ' := by
    intro x needed v found
    obtain ⟨key,mapped,value⟩ := values x needed v found
    exact ⟨key,by rwa [← maps] at mapped,value⟩
  refine ⟨ρ',?_,stock_lower_entered_values_guarded_frame run scope dominated spec.events entered
    values' spec.core.scan.output.state w memory.1,
    stock_lower_entered_values_guarded_frame run scope dominated spec.events entered
    values' spec.core.scan.output.state w' memory.2.1,memory.2.2⟩
  simpa only [preludeEq,Nat.zero_add,Array.length_toList] using path

end E2E.StockMemory

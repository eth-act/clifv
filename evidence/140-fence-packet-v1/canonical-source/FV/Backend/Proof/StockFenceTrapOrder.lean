import FV.Backend.Proof.StockFenceSemantics

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- Actual fence code falls through with unchanged virtual registers.
The machine world satisfies the original refinement contract. -/
theorem stock_lower_fence_execute {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) (w : Arm.ArmState) :
    ∃ world, seqRun isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ w = some (.fall ρ world) ∧
      SameWorld F world w := by
  obtain ⟨step,recorded,emitted,results,last,code,frame⟩ :=
    stock_lower_fence_record_exact run scope events records found source
  obtain ⟨world,executed,same⟩ := refines .fence [] w [] w (ctl := .next) rfl
  have machine := seqRun_isem_one (i := .fence) (ops := #[]) (ρ := ρ) rfl executed rfl
  refine ⟨world,?_,same⟩
  rw [code]
  exact machine

/-- A real fence prefix preserves a later first trap at the resulting world.
The theorem makes no claim that unresolved surrounding effects are pure. -/
theorem stock_lower_fence_first_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) (w : Arm.ArmState) :
    ∃ world, SameWorld F world w ∧ ∀ (rest : List MInst) (code : Clif.TrapCode),
      TrapRun isem rest ρ world code →
      TrapRun isem ((record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ++ rest) ρ w code := by
  obtain ⟨world,executed,same⟩ := stock_lower_fence_execute run scope events records found source
    refines aliases ρ w
  exact ⟨world,same,fun _ _ trapped => trapRun_seq_prefix executed trapped⟩

end Backend.Stock.Proof

import FV.Backend.Proof.StockAcquireConstantFreshRun
import FV.E2E.StockAcquirePureModelPaired

namespace E2E.StockAcquirePending
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
open Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual constant chunks derive paired execution for arbitrary worlds and virtual registers.
The proof retains the unchanged Refines contract and evaluates no future source instruction. -/
theorem stock_lower_constant_paired_fresh_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F Z : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (includes : ∀ addr,F addr → Z addr)
    (regs : Nat → CV) (worlds : W2) (related : SameWorld Z worlds.1 worlds.2) :
    (∀ inst ∈ record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs inst,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg) ∧
    ∃ nextRegs after,seqRun (pairSem isem) (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
      regs worlds = some (.fall nextRegs after) ∧
      SameWorld F after.1 worlds.1 ∧ SameWorld F after.2 worlds.2 ∧ SameWorld Z after.1 after.2 := by
  have self : Refines F ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have semantics : ∀ aliases inst,ispec (inst.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1))) = ispec inst := by
    intro aliases inst
    funext uses world
    apply ispec_mapRegs
    refine ⟨fun n cls => resolve_vreg aliases _ n cls,?_⟩
    intro reg real
    cases reg with
    | vreg n cls => exact False.elim (real n cls rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  obtain ⟨definitions,execute⟩ := stock_lower_constant_fresh_run run scope events records source clif results
    mapped recorded emitted self semantics
  obtain ⟨nextRegs,model⟩ := execute regs
  obtain ⟨after,executed,leftFrame,rightFrame,agreement⟩ := prun_ispec_paired refines includes model related
  exact ⟨definitions,nextRegs,after,executed,leftFrame,rightFrame,agreement⟩

end E2E.StockAcquirePending

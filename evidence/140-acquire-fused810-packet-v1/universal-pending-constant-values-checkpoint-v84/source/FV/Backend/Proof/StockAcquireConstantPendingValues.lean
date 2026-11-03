import FV.Backend.Proof.StockAcquireConstantRecordNeededValues

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- An actual constant record preserves every required nonsuspended value.
The original full capture history stays unchanged. -/
theorem stock_lower_constant_pending_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty0 : Clif.Ty} {imm0 : BitVec ty0.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty0 imm0))
    (results : stm.results = [x]) (infoResults : info.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
    {env : Clif.Env} {cp : Clif.Program}
    (snapshots : List (Acquire810.SunkReadSnapshot event.ctx env cp)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (d : Nat),
      Clif.Inst.iconst ty0 imm0 = .iconst ty imm ∧ aliasNum result.final.alias a = d ∧
      record.output.state.demand = record.input.demand ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV),
        Acquire810.PendingValuesHeld snapshots (fun y => Demanded record.output.state y ∧
          y ∈ availOf f (availIn f result.ctx) bi j) fr
            (fun k => ρ (aliasNum result.final.alias k)) →
        ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
          VHolds ⟨ty, imm⟩ (ρ' d) ∧
          Acquire810.PendingValuesHeld snapshots (fun y => Demanded record.input y ∧
            y ∈ availOf f (availIn f result.ctx) bi (j + 1))
              (withValue fr x ⟨ty, imm⟩) (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨ty,imm,d,constant,resolved,demands,execute⟩ := stock_lower_constant_record_needed_values
    run scope dominated events records block statement current source clif results infoResults
    mapped recorded emitted refines semantics
    (fun y => Demanded record.input y ∧ ¬Acquire810.SuspendedReadResult snapshots y)
  refine ⟨ty,imm,d,constant,resolved,demands,?_⟩
  intro fr regs held
  have before : ValuesHeld (fun y => (Demanded record.input y ∧
      ¬Acquire810.SuspendedReadResult snapshots y) ∧ y ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => regs (aliasNum result.final.alias k)) := by
    intro y required
    apply held y ⟨?_,required.2⟩ required.1.2
    simpa only [Demanded,demands] using required.1.1
  obtain ⟨next,runCode,value,post⟩ := execute fr regs before
  refine ⟨next,runCode,value,?_⟩
  intro y required notSuspended
  exact post y ⟨⟨required.1,notSuspended⟩,required.2⟩

end Backend.Stock.Proof

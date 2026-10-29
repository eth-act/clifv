module

public import FV.Backend.Proof.StockConstantDispatch

@[expose] public section

namespace Backend.Stock.Proof.ConstantComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual retained integer constants refine their original source step. Matching,
RHS fuel and result binding come from the successful whole-driver execution.
The original demanded-and-available guard and arbitrary stable memory relation remain. -/
theorem record_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : stm.results = [x]) (infoResults : info.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
 :
    ∀ (clifEnv : Clif.Env) (cp : Clif.Program) (MR : Clif.Mem → Arm.ArmState → Prop),
        (∀ cm w w', SameWorld F w' w → MR cm w → MR cm w') →
        ∀ (fr fr' : Clif.Frame) (cm cm' : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
          SourceInstResult clifEnv cp event.ctx record.inst (fr, cm) (fr', cm') →
          MR cm w →
          ValuesHeld (fun y => Demanded record.output.state y ∧
            y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr
              (fun k => ρ (aliasNum result.final.alias k)) →
          ∃ ρ' w', seqRun isem (record.output.emitted.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
              some (.fall ρ' w') ∧ MR cm' w' ∧
            ValuesHeld (fun y => Demanded record.input y ∧
              y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx fr'
                (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := selected_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := receipt.selected.fuelBound
  have matched := receipt.selected.matchedRun
  have evaluated := receipt.selected.rhsRun
  rw [chosen] at matched evaluated
  obtain ⟨_,_,_,transfer⟩ := stock_lower_constant_available_source run scope dominated events records block statement current
    source clif results infoResults mapped recorded emitted refines semantics
    (by omega) (by decide) matched evaluated receipt.rootRun
  exact transfer

end Backend.Stock.Proof.ConstantComplete

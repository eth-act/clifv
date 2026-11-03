import FV.Backend.Proof.StockAcquireConstantNeededValues
import FV.Backend.Proof.StockConstantDispatch

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- Actual selection supplies the constant matcher and interpreter execution internally.
An arbitrary required set preserves suspended values without requiring their machine bindings. -/
theorem stock_lower_constant_record_needed_values {f : Clif.Function} {result : Result}
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
    (needed : Nat → Prop) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (d : Nat),
      Clif.Inst.iconst ty0 imm0 = .iconst ty imm ∧ aliasNum result.final.alias a = d ∧
      record.output.state.demand = record.input.demand ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV),
        ValuesHeld (fun y => needed y ∧
          y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr
            (fun k => ρ (aliasNum result.final.alias k)) →
        ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
          VHolds ⟨ty, imm⟩ (ρ' d) ∧
          ValuesHeld (fun y => needed y ∧
            y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
              (withValue fr x ⟨ty, imm⟩) (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := ConstantComplete.selected_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686];rfl
  have enough := receipt.selected.fuelBound
  have matched := receipt.selected.matchedRun
  have evaluated := receipt.selected.rhsRun
  rw [chosen] at matched evaluated
  exact stock_lower_constant_needed_values run scope dominated events records block statement current
    source clif results infoResults mapped recorded emitted refines semantics
    (by omega) (by decide) matched evaluated needed receipt.rootRun

end Backend.Stock.Proof

import FV.Backend.Proof.StockConditionalCompatibility
import FV.Backend.Proof.StockConditionalClass
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.StockConditionalEmptyFixture
import FV.Backend.Proof.StockConditionalEmptyTrapFixture

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Both a returning source and a reachable-divide-by-zero source inhabit the
initial compatible selector under the original input conditions and actual
Stock compilation. This is eligibility evidence, not domain soundness. -/
theorem compatible_conditional_sources_witness : ∃ returning trapping,
    ∃ (returnShape : Stock.ConditionalCfg.Shape EmptyFixture.function)
      (trapShape : Stock.ConditionalCfg.Shape EmptyTrapFixture.function),
    ∃ returnCtx trapCtx returnRanges trapRanges returnInitial trapInitial,
    Stock.buildCtx EmptyFixture.function = .ok (returnCtx,returnRanges,returnInitial) ∧
    Stock.buildCtx EmptyTrapFixture.function = .ok (trapCtx,trapRanges,trapInitial) ∧
    returnCtx.defInst? returnShape.condition = none ∧
    (returnCtx.valueType? returnShape.condition = some (.int 32) ∨
      returnCtx.valueType? returnShape.condition = some (.int 64)) ∧
    trapCtx.defInst? trapShape.condition = none ∧
    (trapCtx.valueType? trapShape.condition = some (.int 32) ∨
      trapCtx.valueType? trapShape.condition = some (.int 64)) ∧
    Stock.lower EmptyFixture.function = .ok returning ∧
    Stock.lower EmptyTrapFixture.function = .ok trapping ∧
    LowerScope EmptyFixture.function ∧ Dominated EmptyFixture.function ∧
    LowerScope EmptyTrapFixture.function ∧ Dominated EmptyTrapFixture.function ∧
    Stock.ConditionalCfg.eligible EmptyFixture.function = true ∧
    Stock.ConditionalCfg.eligible EmptyTrapFixture.function = true := by
  obtain ⟨returning,returnRun,returnScope,returnDom,rest⟩ := EmptyFixture.driver_witness
  obtain ⟨trapping,trapRun,trapScope,trapDom,more⟩ := EmptyTrapFixture.driver_witness
  have returnEligible : Stock.ConditionalCfg.eligible EmptyFixture.function = true := by decide +kernel
  have trapEligible : Stock.ConditionalCfg.eligible EmptyTrapFixture.function = true := by decide +kernel
  obtain ⟨returnShape⟩ := Stock.ConditionalCfg.eligible_shape returnEligible
  obtain ⟨trapShape⟩ := Stock.ConditionalCfg.eligible_shape trapEligible
  let returnBuilt := (Stock.buildCtx EmptyFixture.function).toOption.getD (sinkCtx,#[],sinkState)
  let trapBuilt := (Stock.buildCtx EmptyTrapFixture.function).toOption.getD (sinkCtx,#[],sinkState)
  have returnBuild : Stock.buildCtx EmptyFixture.function = .ok returnBuilt := rfl
  have trapBuild : Stock.buildCtx EmptyTrapFixture.function = .ok trapBuilt := rfl
  have returnMeta := returnShape.condition_metadata returnDom returnBuild
  have trapMeta := trapShape.condition_metadata trapDom trapBuild
  exact ⟨returning,trapping,returnShape,trapShape,returnBuilt.1,trapBuilt.1,
    returnBuilt.2.1,trapBuilt.2.1,returnBuilt.2.2,trapBuilt.2.2,returnBuild,trapBuild,
    returnMeta.1,returnMeta.2,trapMeta.1,trapMeta.2,returnRun,trapRun,
    returnScope,returnDom,trapScope,trapDom,returnEligible,trapEligible⟩

/-- Actual lowering, original source conditions and the source selector inhabit
the derived legacy-compatibility proof on a complete conditional program. -/
theorem compatible_conditional_code_witness (X : ExtSem) :
    ∃ result,∃ (shape : Stock.ConditionalCfg.Shape EmptyFixture.function),
    ∃ (spec : ConditionalBodySpec EmptyFixture.function result shape.entry 0 0 shape.condition
      shape.yes shape.no (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
    Stock.lower EmptyFixture.function = .ok result ∧ LowerScope EmptyFixture.function ∧
    Dominated EmptyFixture.function ∧ Stock.ConditionalCfg.eligible EmptyFixture.function = true ∧
    EdgeLegacyCompatible result.code result.edgeArgs := by
  obtain ⟨result,run,scope,dominated,entered,returned⟩ := EmptyFixture.driver_witness
  have eligible : Stock.ConditionalCfg.eligible EmptyFixture.function = true := by decide +kernel
  obtain ⟨shape⟩ := Stock.ConditionalCfg.eligible_shape eligible
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated shape.family tag shape.source shape.term
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  exact ⟨result,shape,spec,run,scope,dominated,eligible,shape.legacy_compatible run scope dominated spec⟩

end Backend.Stock.Proof.ConditionalValues

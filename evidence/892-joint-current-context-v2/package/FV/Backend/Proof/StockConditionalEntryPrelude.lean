import FV.Backend.Proof.StockOriginalEntryPrelude
import FV.Backend.Proof.StockConditionalBodyCalls
import FV.Backend.Proof.StockConditionalWideAllocation

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Control
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Conditional entry reuses the shared ABI prelude proof; actual parameter
branch emission derives nonempty core code, rather than asking for a code fact. -/
theorem conditional_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b 0 0 c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
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
  have block : f.blocks[0]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have parameterHere : spec.core.scan.ctx.defInst? c = none := by rw [ctxEq]; exact parameter
  obtain ⟨calls,source⟩ := spec.parameter_calls block termShape parameter
  have count : spec.origin.emission.code.size = 1 := by
    rw [spec.origin.emitted]
    rcases conditionTy with narrow | wide
    · have typed : spec.core.scan.ctx.valueType? c = some (.int 32) := by rw [ctxEq]; exact narrow
      have actual := calls.parameter_wide_emitted_size inv source false typed parameterHere
      simpa only [Array.size_empty,Nat.zero_add] using actual
    · have typed : spec.core.scan.ctx.valueType? c = some (.int 64) := by rw [ctxEq]; exact wide
      have actual := calls.parameter_wide_emitted_size inv source true typed parameterHere
      simpa only [Array.size_empty,Nat.zero_add] using actual
  have nonempty : 0 < spec.core.code.size := by
    rw [spec.bodyCode]
    simp only [Array.size_append,count]
    omega
  let entry : EntryCoreSpec f result b := {
    ranges := spec.ranges
    params := spec.params
    core := spec.core
    raw := spec.raw
    preludeCode := spec.preludeCode
    build := spec.build
    sizes := spec.sizes
    assembled := spec.assembled
    events := spec.events
    block := block
    rawCode := spec.rawCode
    placed := spec.placed
    nonempty := nonempty }
  exact original_entry_prelude run scope dominated entry entered driver memorySem stable memory arguments

end Backend.Stock.Proof.ConditionalValues

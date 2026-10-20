import FV.Backend.Proof.StockTryAliasWitness
import FV.Backend.Proof.StockBindingClassWitness

namespace Backend.Stock.Proof.HelperAliasWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.HelperAliasClassDraft Backend.Stock.Proof.OperandClassDraft
open Backend.Stock.Proof.EmissionAliasClassDraft Backend.Stock.Proof.ScanAliasClassDraft Backend.Stock.Proof.Coverage
open Backend.Stock.Proof.EmissionCoverageFixture
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower Stock.externCtor

/-- A complete original constant/return pipeline derives all alias, reservation,
class and no-opportunity inputs internally. Actual nonempty statement/return
emissions and full scans preserve them, including every record endpoint. -/
theorem stock_complete_scan_alias_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (ranges : Array (Nat × Nat))
      (statement terminal : Emission) (scan : Scan) (body : BlockScan) (i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧ AliasClasses result.initial ∧
      emitInstruction result.ctx 0 result.initial = .ok statement ∧ statement.code ≠ #[] ∧
      AliasClasses statement.state ∧ ReservedClasses result.ctx statement.state ∧
      emitInstruction (TerminalDraftObservation.context result) 1 (TerminalDraftObservation.before result) = .ok terminal ∧
      terminal.code ≠ #[] ∧ AliasClasses terminal.state ∧
      scanInstruction (TerminalDraftObservation.context result) 0 1 1 false result.initial = .ok scan ∧ AliasClasses scan.state ∧
      scanBlock (TerminalDraftObservation.context result) 0 1 false [1,0] result.initial = .ok body ∧
      AliasClasses body.state ∧ ReservedClasses (TerminalDraftObservation.context result) body.state ∧ NoOpportunity body.state ∧
      (∀ record ∈ body.records,AliasClasses record.input ∧ AliasClasses record.output.state) ∧
      i ∈ body.code.toList ∧ i.isCtl = false := by
  rcases TerminalDraftWitness.stock_complete_terminal_scan_form_witness with
    ⟨result,p,rf,af,ranges,out,after,trace,terminal,scan,body,i,
      lowered,scope,dominated,arity,prepared,fallback,checked,physical,build,
      mapped,clean,slot,data,named,hasOut,since,emissionRun,emitted,covered,
      scanRun,scanned,scanCoverage,scanSlot,bodyRun,bodyCoverage,member,ordinary,icov,ivalid⟩
  have inputs := stock_build_alias_class_inputs build
  have reserved : ReservedClasses (TerminalDraftObservation.context result) result.initial :=
    inputs.2.2 1 TerminalDraftObservation.termDataValue
  have initial := stock_build_term_classInvariant build 1 TerminalDraftObservation.termDataValue
  have resetAliases : AliasClasses (TerminalDraftObservation.before result) := by
    unfold TerminalDraftObservation.before scanState
    dsimp only
    split <;> exact inputs.1
  have resetReserved : ReservedClasses (TerminalDraftObservation.context result) (TerminalDraftObservation.before result) := by
    unfold TerminalDraftObservation.before scanState
    dsimp only
    split <;> exact reserved
  have terminalClasses := stock_emit_empty_results_alias_classes slot rfl resetReserved resetAliases emissionRun
  have empty := buildCtx_noOpportunity build
  have scanAliases := stock_scan_slot_alias_classes mapped clean scanSlot initial reserved inputs.1 empty scanRun
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have block : (function false).blocks[0]? = some (function false).blocks[0]! := rfl
  have rangeRun : ranges[0]? = some (0,2) := spec.ranges 0 _ block
  have indices : ((Array.range 2).map (0 + ·)).reverse.toList = [1,0] := by decide +kernel
  have slots : ∀ j ∈ [1,0],ScanSlot (TerminalDraftObservation.context result) j 1 false := by
    have sourceSlots := built_scan_slots build scope block rangeRun
      (data := TerminalDraftObservation.termDataValue) (by rfl) result.initial.tryRegs[1]!
    change (∀ j ∈ ((Array.range 2).map (0 + ·)).reverse.toList,
      ScanSlot (TerminalDraftObservation.context result) j 1 false) at sourceSlots
    rw [indices] at sourceSlots
    exact sourceSlots
  have bodyAliases := stock_scanBlock_alias_classes mapped clean slots initial reserved inputs.1 empty bodyRun
  rcases BindingClassWitnessDraft.stock_complete_binding_classes_witness with
    ⟨result2,p2,rf2,af2,ranges2,statement,info,i2,lowered2,_,_,_,_,_,_,_,build2,
      mapped2,clean2,source,clif,results,invariant,emptyBuffer,statementRun,statementNonempty,more⟩
  have same : result2 = result := Except.ok.inj (lowered2.symm.trans lowered)
  subst result2
  have statementAliases := stock_emitInstruction_alias_classes mapped2 clean2 source clif invariant inputs.2.1 inputs.1 statementRun
  exact ⟨result,p,rf,af,ranges,statement,terminal,scan,body,i,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    build,inputs.1,statementRun,statementNonempty,statementAliases.1,statementAliases.2,emissionRun,emitted,terminalClasses.1,
    scanRun,scanAliases.1,bodyRun,bodyAliases.1,bodyAliases.2.1,bodyAliases.2.2.1,bodyAliases.2.2.2,member,ordinary⟩

end Backend.Stock.Proof.HelperAliasWitnessDraft

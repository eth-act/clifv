import FV.Backend.Proof.StockBodyScanRefines
import FV.Backend.Proof.StockBodyScanOrigin

/-! Instantiate ordinary-body semantic composition from the actual whole-driver
split. The remaining syntactic family partition is explicit until every original
family, sunk record and effect has a concrete semantic proof. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- Actual successful Stock lowering supplies the body scan and retained-record
premises internally. Select/omission family execution is then composed without
caller-provided scan, source-position or machine-execution certificates. -/
theorem stock_lower_actual_select_omitted_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ b term body, SourceBodySplit f event b term body ∧
      ((∀ r ∈ body.records, SelectOrOmittedRecord f event.ctx event.block r) →
        ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
          ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
          ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
            seqRun isem (body.code.toList.map (·.mapRegs
              (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
              some (.fall ρ' w') ∧
            GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w') := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  refine ⟨b,term,body,split,?_⟩
  intro families s s' source ρ w held
  apply stock_lower_select_omitted_body_fall_refines run scope dominated events
    split.scanned split.retained families refines stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held
end Backend.Stock.Proof

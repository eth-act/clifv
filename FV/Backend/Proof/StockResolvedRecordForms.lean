import FV.Backend.Proof.StockScanContextCoverage
import FV.Backend.Proof.LowerCover
import FV.Backend.Proof.LowerAlias

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill
open Isle Isle.Interp Isle.Aarch64

private theorem final_renaming (aliases : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve aliases (aliases.size+1))
      (fun n => chaseF (fun k => (aliases[k]?).join) (aliases.size+1) n) := by
  refine ⟨fun n c => resolve_vreg aliases _ n c,?_⟩
  intro r notVirtual
  cases r with
  | vreg n c => exact False.elim (notVirtual n c rfl)
  | _ => simp [Backend.lowerFunction.resolve]

/-- The actual final alias resolver preserves the covered forms and ordinary
spill-static facts of every retained source-statement record. No injectivity,
alias acyclicity or producer certificate is added to the original inputs. -/
theorem stock_lower_resolved_source_record_form_coverage
    {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} (source : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some inst) :
    ∀ i ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  intro i member
  obtain ⟨raw,retained,rfl⟩ := List.mem_map.mp member
  have forms := stock_lower_source_record_form_coverage_original run scope events records source original
  have covered : Covered (raw.mapRegs (Backend.lowerFunction.resolve result.final.alias
      (result.final.alias.size+1))) = true := by
    rw [covered_mapRegs (final_renaming result.final.alias)]
    exact (forms raw retained).1
  refine ⟨covered,?_⟩
  intro ordinary
  apply spillInstOk_of_formOk (ctx := default)
  simpa only [Covered,ordinary,Bool.false_or] using covered

end Backend.Stock.Proof.Coverage.Result

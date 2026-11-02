import FV.Backend.Proof.StockFenceSourceRefines
import FV.Backend.Proof.StockLocalSourceTrap

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The actual source fence cannot be the first source trap.
Earlier and later trapping source instructions keep their separate obligations. -/
theorem stock_lower_fence_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some .fence)
    {isem : Backend.Proof.Sem} {env : Clif.Env} {cp : Clif.Program} {MR : MemRelT} :
    LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record := by
  intro s code trapped ρ w held
  obtain ⟨index,actual,inst,rest,present,source,remaining,outcome⟩ := trapped
  have same : actual = info := Option.some.inj (present.symm.trans found)
  subst actual
  have fence : inst = .fence := Option.some.inj (source.symm.trans original)
  subst inst
  change Clif.Res.ok ([],s.2.2) = Clif.Res.trap code at outcome
  cases outcome

end Backend.Stock.Proof

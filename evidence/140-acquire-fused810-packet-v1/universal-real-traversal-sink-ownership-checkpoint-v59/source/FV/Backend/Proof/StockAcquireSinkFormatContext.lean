import FV.Backend.Proof.StockAcquireSinkFormatSources
import FV.Backend.Proof.StockCoreScanOrigin

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- Actual terminator installation preserves original sink sources at every source slot. -/
theorem SinkFormatSources.termCtx {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    (ti : Nat) (data : V)
    (dataSafe : ∀ fmt fields,fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields)) :
    SinkFormatSources f (Driver.termCtx ctx ti data) := by
  intro i info found fmt fields format decoded
  by_cases same : i = ti
  · subst i
    by_cases inside : ti < ctx.insts.size
    · have old : ∃ installed,ctx.insts[ti]? = some installed :=
        ⟨ctx.insts[ti],Array.getElem?_eq_getElem inside⟩
      obtain ⟨installed,old⟩ := old
      rw [termCtx_insts_self old data] at found
      cases found
      exact False.elim (dataSafe fmt fields format decoded)
    · have outside : (Driver.termCtx ctx ti data).insts[ti]? = none := by
        apply Array.getElem?_eq_none
        simpa [Driver.termCtx] using Nat.le_of_not_gt inside
      rw [outside] at found
      cases found
  · rw [termCtx_insts_ne same data] at found
    exact sources i info found fmt fields format decoded

/-- Exception reservations do not change the original source data. -/
theorem SinkFormatSources.withTryRegs {f : Clif.Function} {ctx : Ctx}
    (sources : SinkFormatSources f ctx) (reservations : List Reg × List Reg) :
    SinkFormatSources f {ctx with tryRegs := reservations} := by
  intro i info found fmt fields format decoded
  exact sources i info found fmt fields format decoded

/-- Every actual block scan inherits source existence from successful context construction. -/
theorem blockCore_scan_sink_format_sources {f : Clif.Function} {ctx : Ctx}
    (sources : SinkFormatSources f ctx) {order : Order} {block : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (dataSafe : ∀ fmt fields,fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields))
    (run : lowerBlockCore ctx order f block bi start stop data targets input = .ok output) :
    SinkFormatSources f output.scan.ctx := by
  rw [(stock_lowerBlockCore_scanOrigin run).2.1]
  exact (sources.termCtx (stop-1) data dataSafe).withTryRegs _

end Backend.Stock.Proof.Acquire810

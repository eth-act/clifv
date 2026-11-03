import FV.Backend.Proof.StockAcquireSinkFormatNode
import FV.Backend.Proof.StockAcquireSinkSourceMemory

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] lowerNode

private theorem nodes_sources {ctx : Ctx} {f : Clif.Function}
    (sources : SinkFormatSources f ctx) {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {indices : List Nat} {before after : DriverState}
    (prior : DriverSinkFormatSources f before)
    (run : indices.foldlM (fun input label => lowerNode ctx ranges order f params label input) before = .ok after) :
    DriverSinkFormatSources f after := by
  induction indices generalizing before with
  | nil => cases run; exact prior
  | cons label indices ih =>
    rw [List.foldlM_cons] at run
    cases called : lowerNode ctx ranges order f params label before with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [called,bind,Except.bind] at run
      exact ih (lowerNode_sink_format_sources sources prior called) run

/-- Every actual Stock scan derives the original source-data property from construction and node execution. -/
theorem stock_lower_sink_format_sources {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∀ event ∈ result.blockScans.toList,SinkFormatSources f event.ctx := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  exact nodes_sources (buildCtx_sink_format_sources hbuild) (by simp [DriverSinkFormatSources]) hdriver

/-- Actual retained contexts discharge the source-data premise of delayed successful read steps internally. -/
theorem stock_lower_sink_format_source_memory {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {producer : Nat} {info : IInfo}
    {fmt : Nat} {fields : List V} (installed : event.ctx.insts[producer]? = some info)
    (format : fmt = 16 ∨ fmt = 17)
    (decoded : (Backend.sem event.ctx).unData 152 info.data = some (fmt,fields))
    {env : Clif.Env} {p : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    (executed : SourceInstResult env p event.ctx producer before after) : after.2 = before.2 :=
  sink_format_source_step_memory (stock_lower_sink_format_sources run event events)
    installed format decoded executed

end Backend.Stock.Proof.Acquire810

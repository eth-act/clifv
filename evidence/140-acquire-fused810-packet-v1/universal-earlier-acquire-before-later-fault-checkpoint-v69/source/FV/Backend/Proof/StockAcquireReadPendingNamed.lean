import FV.Backend.Proof.StockAcquireReadPendingInterpreter

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem named_read_frame {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    {name : String} {args : List V} {before after : State} {out : Option V} {trace : List RuleId}
    (allowed : ∀ term,program.termByName? name = some term → termCtorFree program SinkRules.blocked term.id = true)
    (run : Stock.runTerm ctx name args before = .ok (out,after,trace)) : ReadPendingExecution ctx before after := by
  unfold Stock.runTerm at run
  cases executed : Isle.Interp.run program (Stock.sem ctx) {} name args before with
  | error message => rw [executed] at run; cases run
  | ok result =>
    rw [executed] at run
    cases run
    unfold Isle.Interp.run at executed
    cases lookup : program.termByName? name with
    | none => simp only [lookup] at executed; cases executed
    | some term =>
      simp only [lookup] at executed
      cases call : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          term.ret term.id args).run (before,#[]) with
      | error message => simp only [call,bind,Except.bind] at executed; cases executed
      | ok result =>
        obtain ⟨value,next,trace⟩ := result
        simp only [call,bind,Except.bind,pure,Except.pure] at executed
        cases executed
        exact (read_pending_interpreter_frames sources _).apply _ _ _ _ _ _ _ _ (allowed term lookup) call

/-- The complete actual lower helper derives its general original read frontier. -/
theorem stock_lower_helper_read_pending {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    {args : List V} {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" args before = .ok (out,after,trace)) : ReadPendingExecution ctx before after := by
  apply named_read_frame sources ?_ run
  intro term lookup
  rw [program_termByName_lower] at lookup
  cases lookup
  rw [SinkRules.term_guard]
  decide +kernel

/-- The complete branch helper retains the same read classification through nested evaluator calls. -/
theorem stock_branch_helper_read_pending {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    {args : List V} {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" args before = .ok (out,after,trace)) : ReadPendingExecution ctx before after := by
  apply named_read_frame sources ?_ run
  intro term lookup
  rw [program_termByName_lower_branch] at lookup
  cases lookup
  rw [SinkRules.term_guard]
  decide +kernel

end Backend.Stock.Proof.Acquire810

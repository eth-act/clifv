import FV.Backend.Proof.StockAcquirePendingMarksFrame
import FV.Backend.Proof.StockAcquirePendingTrace
import FV.Backend.Proof.StockAcquirePendingFrame
import FV.Backend.Proof.StockPureUnsunk

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- The actual interpreter supplies the pending list internally. -/
def PendingMarksExecution (ctx : Ctx) (before after : State) : Prop :=
  ∃ pending,PendingMarks ctx before pending after

private theorem marks_refl (ctx : Ctx) (state : State) : PendingMarksExecution ctx state state :=
  ⟨[],.nil state⟩

private theorem marks_trans {ctx : Ctx} {before middle after : State}
    (first : PendingMarksExecution ctx before middle) (second : PendingMarksExecution ctx middle after) :
    PendingMarksExecution ctx before after := by
  obtain ⟨left,first⟩ := first
  obtain ⟨right,second⟩ := second
  exact ⟨left++right,first.append second⟩

/-- Every successful real constructor either adds its actual sink or retains the frontier. -/
theorem stock_ctor_pending_marks_execution {ctx : Ctx} {term : Term} {args : List V}
    {before after : State} {out : V}
    (run : Stock.externCtor ctx term args before = .ok (out,after)) :
    PendingMarksExecution ctx before after := by
  by_cases shape : term.id = TId.sink_inst ∧ ∃ producer,args = [.inst producer]
  · obtain ⟨idEq,producer,rfl⟩ := shape
    have actual : Stock.externCtor ctx T.sink_inst [.inst producer] before = .ok (out,after) := by
      rw [sink_ctor_eq]
      simpa only [Stock.externCtor,idEq] using run
    have output := (sink_accepted actual).2.2.2.1
    rw [output] at actual
    exact ⟨[producer],.sink actual (.nil after)⟩
  · exact ⟨[],.frame (stock_ctor_entryColor run) (stock_ctor_color_without_sink shape run)
      (stock_ctor_sunk_without_sink_shape shape run) (.nil after)⟩

/-- Full successful helper evaluation derives an ordered pending list, including nested sinks.
The theorem does not require a quiet source interval or a caller execution certificate. -/
theorem stock_apply_pending_marks_execution {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty term : Nat} {args : List V} {before after : State} {out : Option V}
    {trace resultTrace : Array RuleId}
    (run : (applyTerm p (Stock.sem ctx) cfg n ty term args).run (before,trace) =
      .ok (out,after,resultTrace)) : PendingMarksExecution ctx before after :=
  (presAt (marks_refl ctx) (fun _ _ _ => marks_trans)
    (fun _ _ _ _ _ h => stock_ctor_pending_marks_execution h) n).apply ty term args before trace out after resultTrace run

/-- Actual named Stock execution derives its pending effects without a supplied list. -/
theorem stock_runTerm_pending_marks_execution {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out,next,trace)) : PendingMarksExecution ctx st next := by
  unfold Stock.runTerm at h
  cases hr : Isle.Interp.run program (Stock.sem ctx) {} term args st with
  | error e => rw [hr] at h; cases h
  | ok result =>
    rw [hr] at h
    cases h
    unfold Isle.Interp.run at hr
    cases ht : program.termByName? term with
    | none => simp only [ht] at hr; cases hr
    | some t =>
      simp only [ht] at hr
      cases ha : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          t.ret t.id args).run (st,#[]) with
      | error e => simp only [ha,bind,Except.bind] at hr; cases hr
      | ok result =>
        rcases result with ⟨out,next,trace⟩
        simp only [ha,bind,Except.bind,pure,Except.pure] at hr
        cases hr
        exact stock_apply_pending_marks_execution ha

/-- Actual stronger execution retains all existing pending execution guarantees. -/
theorem PendingMarksExecution.forget {ctx : Ctx} {before after : State}
    (run : PendingMarksExecution ctx before after) : PendingExecution ctx before after := by
  obtain ⟨pending,trace⟩ := run
  exact ⟨pending,trace.forget⟩

end Backend.Stock.Proof.Acquire810

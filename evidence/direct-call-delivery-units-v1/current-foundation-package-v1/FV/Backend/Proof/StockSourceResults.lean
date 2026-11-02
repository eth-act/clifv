import FV.Backend.Proof.StockSourceDefined

/-! Source-definedness through successful result binding, including extern
call continuation and restoration of an actual saved caller after a return.
Memory effects are retained explicitly rather than assumed absent. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem source_defined_setMany {f : Clif.Function} (ssa : (valueDefs f).Nodup) (ctx : Ctx)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    {fr fr' : Clif.Frame} {vals : List Clif.Val} {regs : Clif.Regs}
    (defined : SourceDefinedAt f ctx bi j fr) (set : fr.regs.setMany stm.results vals = some regs)
    (updated : fr'.regs = regs) : SourceDefinedAt f ctx bi (j+1) fr' := by
  intro x available
  rw [updated]
  by_cases fresh : x ∈ stm.results
  · obtain ⟨_,value,_,_,lookup⟩ := setMany_mem set (stmt_nodup ssa block statement) x fresh
    exact ⟨value,lookup⟩
  · obtain ⟨value,lookup⟩ := defined x (available_before_of_after_not_result block statement available fresh)
    exact ⟨value,by rw [setMany_other set fresh]; exact lookup⟩

/-- Actual successful result continuation preserves the source frame's static
fields and callers while carrying the returned memory, including call effects. -/
theorem source_defined_continueWith {f : Clif.Function} (ssa : (valueDefs f).Nodup) (ctx : Ctx)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    {s next : Clif.State} {rest : List Clif.Stmt} {vals : List Clif.Val} {cm : Clif.Mem}
    (defined : SourceDefinedAt f ctx bi j s.frame)
    (step : Clif.continueWith s rest stm.results vals cm = .next next) :
    SourceDefinedAt f ctx bi (j+1) next.frame ∧ next.frame.func = s.frame.func ∧
      next.frame.slots = s.frame.slots ∧ next.frame.body = rest ∧ next.frame.term = s.frame.term ∧
      next.callers = s.callers ∧ next.mem = cm := by
  unfold Clif.continueWith at step
  cases set : s.frame.regs.setMany stm.results vals with
  | none => rw [set] at step; cases step
  | some regs =>
    rw [set] at step
    cases step
    exact ⟨source_defined_setMany ssa ctx block statement defined set rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- An actual callee return restores source-definedness in its saved caller.
The callee's stack deallocation and activation leave are retained exactly. -/
theorem source_defined_returnValues {f : Clif.Function} (ssa : (valueDefs f).Nodup) (ctx : Ctx)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    {s next : Clif.State} {caller : Clif.Frame} {tail : List (Clif.Frame × List Clif.ValueId)}
    {vals : List Clif.Val} {cm : Clif.Mem} (callers : s.callers = (caller,stm.results) :: tail)
    (defined : SourceDefinedAt f ctx bi j caller) (step : Clif.returnValues s vals cm = .next next) :
    SourceDefinedAt f ctx bi (j+1) next.frame ∧ next.frame.func = caller.func ∧
      next.frame.slots = caller.slots ∧ next.frame.body = caller.body ∧ next.frame.term = caller.term ∧
      next.callers = tail ∧ next.mem = (cm.free (s.frame.slots.map (·.2))).leave := by
  unfold Clif.returnValues at step
  rw [callers] at step
  unfold Clif.StepResult.ofRes at step
  split at step
  · dsimp only at step
    cases set : caller.regs.setMany stm.results vals with
    | none => rw [set] at step; cases step
    | some regs =>
      rw [set] at step
      cases step
      exact ⟨source_defined_setMany ssa ctx block statement defined set rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · cases step
  · cases step
end Backend.Stock.Proof

import FV.Backend.Proof.StockAcquireCapturedEntryMarks
import FV.Backend.Proof.StockAcquirePairedReadFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual retained captures cannot remain pending at their block's original scan input.
Inherited marks from other blocks remain unrestricted. -/
theorem stock_lower_entry_pending_exhausted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {program : Clif.Program} (frontier : ReadEffectFrontier event.ctx env program)
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier event.input) : frontier.pending = [] := by
  cases pending : frontier.pending with
  | nil => rfl
  | cons captured rest =>
    have member : captured ∈ frontier.pending := by rw [pending];exact List.mem_cons_self ..
    have history : captured ∈ frontier.history := by
      rw [frontier.split]
      exact List.mem_append_right _ member
    have present := marked captured member
    have absent := stock_lower_captured_entry_unmarked run scope events captured (retained captured history)
    rw [absent] at present
    cases present

/-- The actual entry-mark boundary recovers both complete original guarded relations.
The whole traversal must construct the prior frontier and its retired-value field. -/
theorem stock_lower_paired_entry_guarded_recovery {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {Z : BitVec 64 → Prop}
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {point : SourcePoint}
    {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env program MR Z entry prefixRecords event.input point regs worlds) :
    prior.frontier.pending = [] ∧
      GuardedScanRel f result event.ctx event.block MR event.input point regs worlds.1 ∧
      GuardedScanRel f result event.ctx event.block MR event.input point regs worlds.2 ∧
      SameWorld Z worlds.1 worlds.2 := by
  have finished := stock_lower_entry_pending_exhausted run scope events prior.frontier prior.retained prior.pending
  exact ⟨finished,frontier_final_guarded prior.left prior.retiredValues finished,
    frontier_final_guarded prior.right prior.retiredValues finished,prior.agreement⟩

end Backend.Stock.Proof.Acquire810

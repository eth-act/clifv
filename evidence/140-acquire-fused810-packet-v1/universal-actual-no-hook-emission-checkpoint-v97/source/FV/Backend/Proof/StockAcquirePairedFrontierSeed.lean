import FV.Backend.Proof.StockAcquirePairedReadFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Complete original guarded relations construct a fresh shared frontier at any source boundary.
This internal constructor imposes no argument-location restriction and clears no static compiler marks. -/
theorem paired_frontier_of_guarded {f : Clif.Function} {result : Result} {event : BlockScanEvent}
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {Z : BitVec 64 → Prop}
    {state : State} {point : SourcePoint} {regs : Nat → CV} {worlds : W2}
    (left : GuardedScanRel f result event.ctx event.block MR state point regs worlds.1)
    (right : GuardedScanRel f result event.ctx event.block MR state point regs worlds.2)
    (agreement : SameWorld Z worlds.1 worlds.2) :
    ∃ prior : PairedReadFrontierAt f result event env program MR Z point.2 [] state point regs worlds,
      prior.frontier.history = [] ∧ prior.frontier.retired = [] ∧ prior.frontier.pending = [] := by
  let frontier := ReadEffectFrontier.empty event.ctx env program
  have leftHeld : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history
      state point regs worlds.1 := pending_guarded_nil.mpr left
  have rightHeld : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history
      state point regs worlds.2 := pending_guarded_nil.mpr right
  exact ⟨⟨frontier,.nil point.2,(by intro captured member;cases member),
    (by intro captured member;cases member),(by intro captured member;cases member),
    (by intro captured member;cases member),leftHeld,rightHeld,agreement⟩,rfl,rfl,rfl⟩

end Backend.Stock.Proof.Acquire810

import FV.E2E.StockAcquireEmitNoRelocHelpers

namespace Backend.Proof
open Backend E2E Backend.Proof.UnwindTables Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual emission of a non-hook instruction family produces no relocation. -/
theorem lines_no_reloc {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) (hm : NoHookInst m) :
    ∀ l ∈ ls, l.noRelocB = true := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals (try simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead, List.cons_append,
    List.nil_append, List.append_assoc, List.mem_nil_iff, false_implies, implies_true,
    and_true])
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl
    | (simp [NoHookInst] at hm; done)
    | exact memFinalize_no_relocs ‹_›
    | exact addOff_no_relocs _ _ _
    | exact kinsn_no_relocs _ _ _
    | exact casLoopCmp_no_relocs _ _
    | exact rmwLoopMid_no_relocs _ _
    | (cases h; done)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
    | (intro _ _; rfl)
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at *; done)

end Backend.Proof

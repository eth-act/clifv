import FV.E2E.RegLevelCallSite
import FV.Backend.Proof.StockAcquirePrepareNoHooks

namespace Backend.Proof
open Backend E2E Backend.Proof.UnwindTables
set_option autoImplicit false
set_option Elab.async false

/-- The emitted line does not invoke a model hook. Labels and data words need no hook. -/
def _root_.Backend.Line.noHookB : Line → Bool
  | .ins inst _ => !inst.hooked
  | _ => true

theorem loadConst64_no_hooks (rd : Reg) (v : Nat) : ∀ l ∈ loadConst64 rd v, l.noHookB = true := by
  intro l hl
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at hl
  rcases hl with rfl | ⟨j, _, hj⟩
  · rfl
  · split at hj
    · cases hj; rfl
    · cases hj

theorem memFinalize_no_hooks {c : FnCtx} {m : AMode} {n : Nat} {v : List Line × AMode}
    (h : memFinalize c m n = .ok v) : ∀ l ∈ v.1, l.noHookB = true := by
  obtain ⟨pre, m'⟩ := v
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, throw, throwThe, MonadExceptOf.throw,
    reduceCtorEq] at h
  all_goals (repeat' split at h)
  all_goals (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)
  all_goals first | exact loadConst64_no_hooks _ _ | simp [Line.noHookB,Insn.hooked]

theorem addOff_no_hooks (rd rn : Reg) (off : Int) :
    ∀ l ∈ MInst.lines.addOff rd rn off, l.noHookB = true := by
  unfold MInst.lines.addOff
  repeat' split
  all_goals simp [Line.noHookB, Insn.hooked]

theorem kinsn_no_hooks (k : CondBrKind) (l : Lbl) (t : Option Clif.TrapCode) :
    (Line.ins (k.insn l) t).noHookB = true := by
  cases k <;> rfl

theorem rmwLoopCmp_no_hooks (op : AtomicRmwLoopOp) (bits : Nat) (t : Option Clif.TrapCode) :
    (Line.ins (rmwLoopCmp op bits) t).noHookB = true := by
  unfold rmwLoopCmp; split <;> rfl

theorem casLoopCmp_no_hooks (bits : Nat) (t : Option Clif.TrapCode) :
    (Line.ins (casLoopCmp bits) t).noHookB = true := by
  unfold casLoopCmp; split <;> rfl

theorem rmwLoopMid_no_hooks (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, (Line.ins i none).noHookB = true := by
  have hs : ∀ i ∈ rmwLoopSext bits, (Line.ins i none).noHookB = true := by
    unfold rmwLoopSext; split <;> simp [Line.noHookB, Insn.hooked]
  cases op <;> simp only [rmwLoopMid, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
  all_goals intro i hi
  all_goals first
    | (rcases hi with rfl | rfl <;> first | rfl | exact rmwLoopCmp_no_hooks _ _ _)
    | (rcases hi with hi | rfl | rfl <;> first | exact hs i hi | rfl | exact rmwLoopCmp_no_hooks _ _ _)
    | (subst hi; rfl)
    | simp at hi

end Backend.Proof

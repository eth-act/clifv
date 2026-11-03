import FV.E2E.RegLevelCallSite
import FV.Backend.Proof.StockAcquirePrepareNoHooks

namespace Backend.Proof
open Backend E2E Backend.Proof.UnwindTables
set_option autoImplicit false
set_option Elab.async false

/-- The emitted line has no relocation. Labels and data words have no relocation. -/
def _root_.Backend.Line.noRelocB : Line → Bool
  | .ins inst _ => inst.reloc?.isNone
  | _ => true

theorem loadConst64_no_relocs (rd : Reg) (v : Nat) : ∀ l ∈ loadConst64 rd v, l.noRelocB = true := by
  intro l hl
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at hl
  rcases hl with rfl | ⟨j, _, hj⟩
  · rfl
  · split at hj
    · cases hj; rfl
    · cases hj

theorem memFinalize_no_relocs {c : FnCtx} {m : AMode} {n : Nat} {v : List Line × AMode}
    (h : memFinalize c m n = .ok v) : ∀ l ∈ v.1, l.noRelocB = true := by
  obtain ⟨pre, m'⟩ := v
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, throw, throwThe, MonadExceptOf.throw,
    reduceCtorEq] at h
  all_goals (repeat' split at h)
  all_goals (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)
  all_goals first | exact loadConst64_no_relocs _ _ | simp [Line.noRelocB,Insn.reloc?]

theorem addOff_no_relocs (rd rn : Reg) (off : Int) :
    ∀ l ∈ MInst.lines.addOff rd rn off, l.noRelocB = true := by
  unfold MInst.lines.addOff
  repeat' split
  all_goals simp [Line.noRelocB, Insn.reloc?]

theorem kinsn_no_relocs (k : CondBrKind) (l : Lbl) (t : Option Clif.TrapCode) :
    (Line.ins (k.insn l) t).noRelocB = true := by
  cases k <;> rfl

theorem rmwLoopCmp_no_relocs (op : AtomicRmwLoopOp) (bits : Nat) (t : Option Clif.TrapCode) :
    (Line.ins (rmwLoopCmp op bits) t).noRelocB = true := by
  unfold rmwLoopCmp; split <;> rfl

theorem casLoopCmp_no_relocs (bits : Nat) (t : Option Clif.TrapCode) :
    (Line.ins (casLoopCmp bits) t).noRelocB = true := by
  unfold casLoopCmp; split <;> rfl

theorem rmwLoopMid_no_relocs (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, (Line.ins i none).noRelocB = true := by
  have hs : ∀ i ∈ rmwLoopSext bits, (Line.ins i none).noRelocB = true := by
    unfold rmwLoopSext; split <;> simp [Line.noRelocB, Insn.reloc?]
  cases op <;> simp only [rmwLoopMid, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
  all_goals intro i hi
  all_goals first
    | (rcases hi with rfl | rfl <;> first | rfl | exact rmwLoopCmp_no_relocs _ _ _)
    | (rcases hi with hi | rfl | rfl <;> first | exact hs i hi | rfl | exact rmwLoopCmp_no_relocs _ _ _)
    | (subst hi; rfl)
    | simp at hi

end Backend.Proof

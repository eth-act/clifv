import FV.E2E.Lockstep
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.RefinesCSem

/-! # The guarded semantics (agent/link-widen, stage 2)

`csemG F ctx X Rd`: `csem` where the memory accesses have the forms the memory rules use and
every byte read satisfies `Rd` (`GuardR`), undefined elsewhere. It satisfies the rule contracts
with guarded reads — `Refines`, `MemRefinesR Rd`, `CallsRefine`, `IndCallsRefine` — so the
memory rules (`MemRulesCorrectR`) and the other rules instantiated with it, per CLIF step with
`Rd := ¬ Z` (`Z`: the bytes where two worlds may differ that the step's CLIF memory has not
initialised), give a VCode run whose reads avoid `Z`; `csemG_lockstep` then runs the same
instructions on the second world (`csem_lockstep`). Still needed for the product driver: the
call and `try_call` rules under `MemRefinesR` (they only store), the LL/SC loops, `try_call`
and `Args` in the lockstep (`docs/contracts/e2e.md`, "Widening" item 2). -/

namespace E2E
open Backend Backend.Proof

/-- The guard of the guarded semantics `csemG`: the memory accesses in the forms the memory rules
use (an addressing mode with an address, avoiding the frame `F`), every byte read satisfying
`Rd`. -/
def GuardR (F Rd : BitVec 64 → Prop) (sb : Nat) : MInst → List CV → Arm.ArmState → Prop
  | .load op (.vreg _ .int) am _, us, w => op ≠ .fpuLoad128 ∧
      ∃ a, amodeAddr sb am op.bytes us w = some a ∧ Avoids F op.bytes a ∧
        ∀ k < op.bytes, Rd (a + BitVec.ofNat 64 k)
  | .store op (.vreg _ .int) am _, _ :: us, w => op ≠ .fpuStore128 ∧
      ∃ a, amodeAddr sb am op.bytes us w = some a ∧ Avoids F op.bytes a
  | .loadAcquire ty (.vreg _ .int) (.vreg _ .int) _, [u], _ =>
      AtomTy ty ∧ Avoids F ty.bytes (lo64 u) ∧ ∀ k < ty.bytes, Rd (lo64 u + BitVec.ofNat 64 k)
  | .storeRelease ty (.vreg _ .int) (.vreg _ .int) _, [u, _], _ =>
      AtomTy ty ∧ Avoids F ty.bytes (lo64 u)
  | .atomicRmwLoop ty .., u :: _, _ => ∀ k < ty.bytes, Rd (lo64 u + BitVec.ofNat 64 k)
  | .atomicCasLoop ty .., u :: _, _ => ∀ k < ty.bytes, Rd (lo64 u + BitVec.ofNat 64 k)
  | .load .., _, _ | .store .., _, _ | .loadAcquire .., _, _ | .storeRelease .., _, _ => False
  | _, _, _ => True

open Classical in
/-- **The guarded semantics**: `csem` where `GuardR` holds, undefined elsewhere. -/
noncomputable def csemG (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (Rd : BitVec 64 → Prop) :
    Sem := fun i us w => if GuardR F Rd ctx.slotBase i us w then csem F ctx X i us w else none

variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}

theorem csemG_of {i : MInst} {us : List CV} {w : Arm.ArmState}
    (h : GuardR F Rd ctx.slotBase i us w) : csemG F ctx X Rd i us w = csem F ctx X i us w := by
  simp [csemG, h]

theorem csemG_sub {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemG F ctx X Rd i us w = some r) :
    GuardR F Rd ctx.slotBase i us w ∧ csem F ctx X i us w = some r := by
  unfold csemG at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- The guard with `Rd` the complement of `Z` is the lockstep's guard (outside the forms it does
not cover). -/
theorem lockGuard_of {Z : BitVec 64 → Prop} {i : MInst} {us : List CV} {w : Arm.ArmState}
    (h : GuardR F (fun b => ¬ Z b) ctx.slotBase i us w)
    (hl : ∀ ty op fl a b c d e, i ≠ .atomicRmwLoop ty op fl a b c d e)
    (hc : ∀ ty fl a b c d e, i ≠ .atomicCasLoop ty fl a b c d e)
    (ht : ∀ info ti, i ≠ .tryCall info ti) (ha : ∀ ds, i ≠ .args ds) :
    LockGuard F Z ctx.slotBase i us w := by
  unfold GuardR at h
  unfold LockGuard
  split at h
  all_goals first
    | exact h
    | exact h.elim
    | (exfalso; exact hl _ _ _ _ _ _ _ _ rfl)
    | (exfalso; exact hc _ _ _ _ _ _ _ rfl)
    | (split
       all_goals first
         | trivial
         | (exfalso; solve_by_elim)
         | (exfalso; exact hl _ _ _ _ _ _ _ _ rfl)
         | (exfalso; exact hc _ _ _ _ _ _ _ rfl)
         | (exfalso; exact ht _ _ rfl)
         | (exfalso; exact ha _ rfl))


/-- **The guarded semantics refines the memory forms with guarded reads** (`MemRefinesR Rd`). -/
theorem memRefinesR_csemG {sb : Nat} {syms : String → Option Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefinesR Rd F sb syms (csemG F ctx X Rd) := by
  have hM := memRefines_csem (F := F) (ctx := ctx) X hsb hsym
  subst hsb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op d am fl uses w a hop ha hav hrd
    have hg : GuardR F Rd ctx.slotBase (.load op (.vreg d .int) am fl) uses w :=
      ⟨hop, a, ha, hav, hrd⟩
    rw [csemG_of hg]
    exact hM.1 op d am fl uses w a hop ha hav
  · intro op d am fl v uses w a hop ha hav
    have hg : GuardR F Rd ctx.slotBase (.store op (.vreg d .int) am fl) (v :: uses) w :=
      ⟨hop, a, ha, hav⟩
    rw [csemG_of hg]
    exact hM.2.1 op d am fl v uses w a hop ha hav
  · intro d off w
    rw [csemG_of (by simp [GuardR])]
    exact hM.2.2.1 d off w
  · intro d n b w hb
    rw [csemG_of (by simp [GuardR])]
    exact hM.2.2.2.1 d n b w hb
  · intro ty d r fl u w hty hav hrd
    have hg : GuardR F Rd ctx.slotBase (.loadAcquire ty (.vreg d .int) (.vreg r .int) fl) [u] w :=
      ⟨hty, hav, hrd⟩
    rw [csemG_of hg]
    exact hM.2.2.2.2.1 ty d r fl u w hty hav
  · intro ty d r fl u v w hty hav
    have hg : GuardR F Rd ctx.slotBase (.storeRelease ty (.vreg d .int) (.vreg r .int) fl) [u, v] w :=
      ⟨hty, hav⟩
    rw [csemG_of hg]
    exact hM.2.2.2.2.2.1 ty d r fl u v w hty hav
  · intro ty op fl ra ro rd r1 r2 u x w hty hav hrd
    have hg : GuardR F Rd ctx.slotBase (.atomicRmwLoop ty op fl (.vreg ra .int) (.vreg ro .int)
      (.vreg rd .int) (.vreg r1 .int) (.vreg r2 .int)) [u, x] w := hrd
    rw [csemG_of hg]
    exact hM.2.2.2.2.2.2.1 ty op fl ra ro rd r1 r2 u x w hty hav
  · intro ty fl ra re rx rd r1 u e x w hty hav hrd
    have hg : GuardR F Rd ctx.slotBase (.atomicCasLoop ty fl (.vreg ra .int) (.vreg re .int)
      (.vreg rx .int) (.vreg rd .int) (.vreg r1 .int)) [u, e, x] w := hrd
    rw [csemG_of hg]
    exact hM.2.2.2.2.2.2.2.1 ty fl ra re rx rd r1 u e x w hty hav
  · intro d t n b w hb
    rw [csemG_of (by simp [GuardR])]
    exact hM.2.2.2.2.2.2.2.2 d t n b w hb

/-- The forms `ispec` specifies are not memory forms: the guard holds there. -/
theorem guardR_of_ispec {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : ispec i us w = some r) (sb : Nat) : GuardR F Rd sb i us w := by
  unfold GuardR
  split
  all_goals first
    | trivial
    | (simp [ispec] at h)
    | (exfalso; revert h; simp [ispec])

theorem refines_csemG : Refines F (csemG F ctx X Rd) := by
  intro i us w outs w' ctl h
  rw [csemG_of (guardR_of_ispec h _)]
  exact refines_csem F ctx X i us w outs w' h

theorem callsRefine_csemG {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) : CallsRefine F env exts MR (csemG F ctx X Rd) := by
  obtain ⟨sym, h1, h2, h3⟩ := callsRefine_csem (F := F) (ctx := ctx) hX
  refine ⟨sym, fun rd n w => ?_, fun ext hin g sl cm w dest us ds uses args vals rvals cm' a1 a2 a3
    a4 a5 a6 a7 => ?_, fun ext hin g sl cm w dest us ds ti uses args vals rvals cm' a1 a2 a3 a4 a5 a6
    a7 => ?_⟩
  · rw [csemG_of (by simp [GuardR])]; exact h1 rd n w
  · rw [csemG_of (by simp [GuardR])]; exact h2 ext hin g sl cm w dest us ds uses args vals rvals cm'
      a1 a2 a3 a4 a5 a6 a7
  · rw [csemG_of (by simp [GuardR])]; exact h3 ext hin g sl cm w dest us ds ti uses args vals rvals cm'
      a1 a2 a3 a4 a5 a6 a7

theorem indCallsRefine_csemG {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    {syms : String → Option Nat} (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms) :
    IndCallsRefine env sigs MR (csemG F ctx X Rd) := by
  obtain ⟨h1, h2⟩ := indCallsRefine_csem (F := F) (ctx := ctx) hX hsym hMRs
  refine ⟨fun sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 => ?_,
    fun sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 => ?_⟩
  · rw [csemG_of (by simp [GuardR])]
    exact h1 sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9
  · rw [csemG_of (by simp [GuardR])]
    exact h2 sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9


/-- **One step of the guarded semantics, in lockstep**: where `csemG` with the reads guarded by
`¬ Z` runs an instruction on `w` (the LL/SC loops, `try_call` and `Args` aside), `csem` runs it
on any `w'` that agrees with `w` outside `Z ⊇ F`, with the same outputs and control (under the
callee and TLSDESC premises of `csem_lockstep`). -/
theorem csemG_lockstep {Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {i : MInst} {us : List CV}
    {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (hl : ∀ ty op fl a b c d e, i ≠ .atomicRmwLoop ty op fl a b c d e)
    (hc : ∀ ty fl a b c d e, i ≠ .atomicCasLoop ty fl a b c d e)
    (ht : ∀ info ti, i ≠ .tryCall info ti) (ha : ∀ ds, i ≠ .args ds)
    (hX : ∀ d o x, X.call d us w = some (o, x) →
      ∃ x', X.call d us w' = some (o, x') ∧ SameWorld Z x x')
    (hT : ∀ n, X.tlsFlags n w = X.tlsFlags n w')
    {o : List CV} {w₁ : Arm.ArmState} {c : Ctl}
    (h : csemG F ctx X (fun b => ¬ Z b) i us w = some (o, w₁, c)) :
    csem F ctx X i us w = some (o, w₁, c) ∧ ∃ w₁', csem F ctx X i us w' = some (o, w₁', c) ∧
      SameWorld (fun b => Z b ∧ ¬ WriteSet ctx.slotBase i us w b) w₁ w₁' := by
  obtain ⟨hg, hs⟩ := csemG_sub h
  exact ⟨hs, csem_lockstep hFZ hw (lockGuard_of hg hl hc ht ha) hX hT hs⟩

end E2E

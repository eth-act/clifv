import FV.Concurrency.ArmAllocPause
import FV.Concurrency.CallLoadResume

/-!
# Layer 4b pausing at calls: witness (T2j follow-up, #473)

The compiled caller of `atomic_load` (`CallLoadData`, `RC`: `args`, `call`, `rets`) is in the
scope with calls (`MemScopeLSC`) but not in `MemScopeLS`; `caller_lsC`: `arm_alloc_refines_lsC`
on its runs from the body entry after the prologue. Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSeg.WitnessC

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessL CallThread

/-- An `args`, a `call` or a `rets`. -/
def callerFormB : MInst → Bool
  | .args _ | .rets _ | .call _ => true
  | _ => false

/-- Every instruction of the caller is an `args`, a `call` or a `rets` (as a check). -/
def scopeCB : Bool := vcpC.blocks.all (·.insts.all callerFormB)

theorem scopeCB_eq : scopeCB = true := by native_decide

/-- **The caller is in the scope with calls.** -/
theorem scopeRC : MemScopeLSC RC := by
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp scopeCB_eq) b hb'
  have h2 : callerFormB RC.vc.blocks[b].insts[k] = true := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize RC.vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | args ds => exact .inl (.inl (.inl (.inr (.inl ⟨ds, rfl⟩))))
  | rets us => exact .inl (.inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩)))))
  | call info => exact .inr (.inr (.inr ⟨info, rfl⟩))
  | _ => simp [callerFormB] at h2

/-- **The caller is outside `MemScopeLS`** (its `call`). -/
theorem not_scopeLS_RC : ¬ MemScopeLS RC := by
  intro h
  obtain ⟨info, hinfo⟩ := callC1
  exact (ThreadProgress.coveredCode_of_ls h 0 _ 1 _ vb0C hinfo).1 info rfl

/-- **Non-vacuity of `arm_alloc_refines_lsC`**: the compiled caller of `atomic_load` (a call, so
outside `MemScopeLS`), on its runs from the body entry after the prologue: realized entirely, or
up to a state related to where its allocated code is done or pauses at its call or its return. -/
theorem caller_lsC {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RC.step (OkPriv RC)
      (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize RC.af.isCaller).length RC.s0, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun RC.vc RC.rf RC.sem ckeep (cEvs RC.F RC.ctx)
        (MConf.init RC.rf (locVal RC.fr (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize RC.af.isCaller).length
          RC.s0)) w₀C) trS cE ∧
      ThreadRefine.Refines (· = ·) (PrivA RC) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ ∃ tE, PRun Policy.arm RC.step (OkPriv RC)
        (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize RC.af.isCaller).length RC.s0, mon) (ls.take n) tE ∧
        RelQ RC tE cE ∧ Pause RC cE) := by
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  exact arm_alloc_refines_lsC wfRC scopeRC hq hA hr

end Concurrency.CallSeg.WitnessC

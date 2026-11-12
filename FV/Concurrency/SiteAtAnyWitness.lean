import FV.Concurrency.ArmAllocWitness
import FV.E2E.RegLevelUTry
import FV.Clif.Parse
import FV.Backend.Isel
import FV.Backend.SpillAlloc

/-!
# Non-vacuity of `siteAt_any` (#622, #553)

`Backend.Proof.siteAt_any` gives the call-site bridge `SiteAt` for every well-formed activation,
without `siteAt_of_check`'s check of the last block's calls (`lastCallsOk`). Witness: the CLIF
`%f(i64) -> i64 { fn0 = colocated %g(i64) -> i64; v1 = call fn0(v0); return v1 }` (`fS`) as the
pipeline compiles it (`lowerFunction`, `prepare`, `spillAlloc`, then `act`'s `lowerRFunc`,
`emitFunc`, `layout`), as the activation `RS` (`ArmAllocThread.Witness.act`): `RS.Wf` holds, the
last block of `RS.af` contains a call (the block the removed check was about), and so
`SiteAt RS` (`siteAt_any_witness`).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.SiteAtAny.Witness

open Backend Backend.Proof
open ArmAllocThread.Witness (act wf_of)

/-- The caller. -/
def srcS : String := "function %f(i64) -> i64 {
    fn0 = colocated %g(i64) -> i64

block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
"

def fS : Clif.Function :=
  match Clif.parse srcS with
  | .ok p => p.funcs.headD default
  | .error _ => default

def vcS : VCode := match lowerFunction fS with
  | .ok vc => vc
  | .error _ => default

def vcpS : VCode := match Backend.prepare vcS with
  | .ok vcp => vcp
  | .error _ => default

def rfS : RFunc := spillAlloc vcpS

/-- **The activation** of the compiled `fS` (module doc). -/
abbrev RS : RL := act vcpS rfS

theorem factsS : (checkAlloc vcpS rfS).isOk = true ∧ (lowerRFunc vcpS rfS).toBool = true ∧
    (emitFunc 0 (act vcpS rfS).af).toBool = true ∧ (act vcpS rfS).fa.k = 0 ∧
    (act vcpS rfS).fa.layout.toBool = true ∧
    (labelOffsets (act vcpS rfS).fa.lines).toBool = true ∧
    4 * (act vcpS rfS).fb.words.size ≤ 2 ^ 64 ∧ (act vcpS rfS).af.frameSize ≤ 0x100 ∧
    4 * (act vcpS rfS).fb.words.size ≤ 0x10000 ∧
    (emitPlan (act vcpS rfS).fa.k (act vcpS rfS).af).toBool = true := by
  native_decide

theorem allocS : checkAlloc vcpS rfS = .ok () := by
  have h := factsS.1
  revert h
  cases checkAlloc vcpS rfS with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem wfRS : RS.Wf := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := factsS
  exact wf_of allocS h1 h2 h3 h4 h5 h6 h7 h8 h9

/-- The last block of `RS.af` contains a call. -/
theorem lastCallS : ∃ blk, RS.af.blocks.back? = some blk ∧ blockCalls blk ≠ [] := by
  have h : (RS.af.blocks.back?.any fun blk => !(blockCalls blk).isEmpty) = true := by
    native_decide
  cases hb : RS.af.blocks.back? with
  | none => rw [hb] at h; cases h
  | some blk =>
    rw [hb] at h
    refine ⟨blk, rfl, fun he => ?_⟩
    simp [he] at h

/-- **Non-vacuity of `siteAt_any`**: the compiled `fS` (`RS`) is a well-formed activation whose
last block contains a call, and the call-site bridge holds for it without the `lastCallsOk`
check. -/
theorem siteAt_any_witness :
    RS.Wf ∧ (∃ blk, RS.af.blocks.back? = some blk ∧ blockCalls blk ≠ []) ∧ SiteAt RS :=
  ⟨wfRS, lastCallS, siteAt_any wfRS⟩

end Concurrency.SiteAtAny.Witness

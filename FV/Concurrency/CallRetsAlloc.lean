import FV.E2E.RegLevelCorrect
import FV.Concurrency.CallResumeLayers

/-!
# The return of an allocated activation on the machine (#473, (1))

**`rets_alloc`**: at a `rets` item of the allocated code, with layer 4b's `Q` and the
allocation checker's relation (`MatchRun`) to a VCode configuration, the epilogue and the `ret`
(`RegLevelFrame.ret_machine`) reach the return address with `sp` as at entry and the memory
kept, the returned VCode values (the `rets`' uses) in their fixed registers, and every
callee-saved register holding, up to `ckeep` (the low halves of v8–v15), the checker's entry
value `r₀` (the checker's `.ret` relation after the allocated `rets` step,
`RegallocSound.sim_step_at`, as in `regLevelCorrect_world_atX`).
-/

namespace Concurrency.CallRetsAlloc

open Arm ArmThread Backend Backend.Proof E2E VCodeThread

/-- **The allocated activation's return on the machine** (module doc). -/
theorem rets_alloc {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {c : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt R.vc R.rf c ins a0) {r₀ : Reg → CV}
    {s : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vs : VState CV ArmState}
    (hm : MatchRun c ins ckeep r₀ ⟨b, .op k allocs :: its, m, w⟩ vs) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n ops, (MInst.rets us).operands = .ok ops ∧ (∀ i < n, R.GoodX (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ (iterN R.step n s).mem = s.mem ∧
      (iterN R.step n s).program = s.program ∧
      (∀ r ∈ calleeSaved, ckeep r (regVal (iterN R.step n s) r) = ckeep r (r₀ r)) ∧
      ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) → (vuses ops vs.ρ)[j]? = some x →
        regVal (iterN R.step n s) p = x := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
  obtain ⟨b', k', ρ, w''⟩ := vs
  have hm' := hm
  obtain ⟨hb, hw, vb', a, out, hvb', hrun, -, -⟩ := hm'
  simp only at hb hw hvb' hrun
  subst hb hw
  obtain ⟨-, hk, -⟩ := runItems_op hrun
  subst hk
  have hvbV : R.vc.blocks[b]? = some vb' := by rw [← hc.vc_eq]; exact hvb'
  rw [hvbV] at hvb; cases hvb
  -- the VCode `rets` step and the allocated one
  have h1 : VStep R.vc R.sem (.run ⟨b, k, ρ, w⟩)
      (.ret (vuses (retOpsC ns).toArray ρ) w) := by
    refine VStep.step hvbV hi (operands_retsC ns) (outs := []) ?_ ?_ (VNext.ret rfl)
    · simp [RL.sem, csemV, csem]
    · rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
  obtain ⟨c', hms⟩ := sim_progress_at R.sem ckeep hc hm h1
  rcases sim_step_at R.sem ckeep hc hm hms with ⟨ms', rfl, -, -⟩ | ⟨v', hv, hM⟩
  · exfalso
    cases hms with
    | op hvb1 hi1 hops1 _ hsem2 _ _ _ hn =>
      rw [hvbV] at hvb1; cases hvb1
      rw [hi] at hi1; cases hi1
      rw [operands_retsC] at hops1; cases hops1
      simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem2
      obtain ⟨rfl, rfl, rfl⟩ := hsem2
      cases hn
  obtain rfl := Concurrency.IselStep.vstep_det hv h1
  cases c' with
  | run => exact hM.elim
  | halt => exact hM.elim
  | ret uses m' w2 =>
    obtain ⟨huses, -, hks⟩ := hM
    cases hms with
    | op hvb1 hi1 hops1 hsz hsem2 hlen2 hho hcl hn =>
      rw [hvbV] at hvb1; cases hvb1
      rw [hi] at hi1; cases hi1
      rw [operands_retsC] at hops1; cases hops1
      have hsem3 := hsem2
      simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
      obtain ⟨rfl, rfl, rfl⟩ := hsem3
      cases hn with
      | ret _ =>
      rw [Backend.Proof.rets_store hlen2 rfl hho hcl] at hks
      have hst := q_stRel hq
      obtain ⟨n, ht, hpc, herr, hsp, -, hregs, hmem, -, hprogF, hvalsM⟩ :=
        ret_machine hR hent hq hvbV hi
      refine ⟨n, _, operands_retsC ns, ht, hpc, herr, hsp, hmem, hprogF, fun r hr => ?_,
        fun j v p x hj hx => ?_⟩
      · have hal := CallResumeL.calleeSaved_allocatable r hr
        have hs1 : m (.reg r) = regVal s r :=
          hst.store (.reg r) (fun r' e => by cases e; exact hal) trivial
        rw [hregs r hal, ← hs1]
        exact hks r hr
      · rw [← huses] at hx
        exact hvalsM _ (operands_retsC ns) j v p x hj hx

end Concurrency.CallRetsAlloc

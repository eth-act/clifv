import FV.E2E.RegLevelCorrect
import FV.Backend.Proof.SpillLocal
import FV.Concurrency.CallResumeLayers
import FV.E2E.PairDriver

/-!
# The return of an allocated activation on the machine (#473, (1))

**`rets_alloc`**: at a `rets` item of the allocated code, with layer 4b's relation (`QA`: `Q`,
or a return tail whose callee restores ran at the level of the allocated code only) and the
allocation checker's relation (`MatchRun`) to a VCode configuration, Cranelift's epilogue and the
`ret` (`RegLevelFrame.ret_machine`) reach the return address with `sp` as at entry and the memory
kept, the returned VCode values (the `rets`' uses) in their fixed registers, and every
callee-saved register holding, up to `ckeep` (the low halves of v8–v15), the checker's entry
value `r₀` (the checker's `.ret` relation after the allocated `rets` step,
`RegallocSound.sim_step_at`, as in `regLevelCorrect_world_atX`, for the registers the function
does not save; the epilogue's pops, for the ones it saves, give their values at entry, which are
`r₀`'s by `hr₀`).
-/

namespace Concurrency.CallRetsAlloc

open Arm ArmThread Backend Backend.Proof E2E VCodeThread

/-- Equal 8-byte slot values give equal callee-preserved parts. -/
theorem ckeep_regVal_of_slotVal {t u : ArmState} {r : Reg} (h : slotVal t r = slotVal u r)
    (hr : r ∈ calleeSaved) : ckeep r (regVal t r) = ckeep r (regVal u r) := by
  rcases calleeSaved_cases hr with ⟨n, rfl, -⟩ | ⟨n, rfl, -⟩
  · simp only [slotVal] at h
    simp only [regVal, ckeep, h]
  · simp only [slotVal] at h
    simp only [regVal, ckeep, h]

/-- **The allocated activation's return on the machine** (module doc). The relation at the
`rets` is `QA` (`RelQ`): in a return tail the store differs from the machine's at the restored
registers. `hr₀`: the registers the prologue pushes (`R.af.saves`) come back with their values at
the ABI entry, so the checker's entry values must be those (Cranelift's frame: the restores emit
no code, the save slots are not `Q`'s locations). -/
theorem rets_alloc {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {c : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt R.vc R.rf c ins a0) {r₀ : Reg → CV}
    (hr₀ : ∀ r ∈ R.af.saves, ckeep r (r₀ r) = ckeep r (regVal R.s0 r))
    {s : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hqa : QA R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vs : VState CV ArmState}
    (hm : MatchRun c ins ckeep r₀ ⟨b, .op k allocs :: its, m, w⟩ vs) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n ops, (MInst.rets us).operands = .ok ops ∧ (∀ i < n, R.GoodX (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ (iterN R.step n s).mem = s.mem ∧
      ((iterN R.step n s).program = s.program ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0) ∧
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
      obtain ⟨n, ht, hpc, herr, hsp, hx29, hregs, hsaved, hmem, -, hprogF, hvalsM⟩ :=
        ret_machine hR hent hqa hvbV hi
      refine ⟨n, _, operands_retsC ns, ht, hpc, herr, hsp, hmem, ⟨hprogF, hx29⟩, fun r hr => ?_,
        fun j v p x hj hx => ?_⟩
      · by_cases hsv : r ∈ R.af.saves
        · rw [ckeep_regVal_of_slotVal (hsaved r hsv) hr, hr₀ r hsv]
        · rw [hregs r (CallResumeL.calleeSaved_allocatable r hr) hsv]
          exact hks r hr
      · rw [← huses] at hx
        exact hvalsM _ (operands_retsC ns) j v p x hj hx
/-! ## The VCode return at the `rets` (layers 2/3) -/

section
open PrepThread Backend.Proof.Driver

/-- An event-free VCode thread run is a VCode run. -/
theorem star_of_vtrun_nil {vc : VCode} {sem : ISem CV ArmState}
    {ev : MInst → List CV → ArmState → List Ev} {c c' : VConf CV ArmState}
    {tr : List (List Ev)} (h : VTRun vc sem ev c tr c') (hnil : ∀ e ∈ tr, e = []) :
    Star (VStep vc sem) c c' := by
  induction h with
  | nil => exact .refl _
  | @cons c1 c2 c3 evs tr hs _ ih =>
    have he : evs = [] := hnil evs List.mem_cons_self
    subst he
    cases hs with
    | mk _ _ _ _ _ hst =>
      exact .step hst (ih fun e he => hnil e (List.mem_cons_of_mem _ he))

/-- **At a `rets` of the prepared code, `prepare`'s relation is the block correspondence to a
`rets` of the original.** -/
theorem pmatch_rets {vc vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)}
    (H : PrepFacts vc vcp L ss ss') {sem : ISem CV ArmState} (hds : DriverSemG sem)
    {ev : MInst → List CV → ArmState → List Ev}
    {src : VConf CV ArmState} {b' k : Nat} {ρ : Nat → CV} {w : ArmState} {vb' : VBlock}
    {us : List (Reg × Reg)} (hm : PMatch vc vcp sem ev L ss' src (.run ⟨b', k, ρ, w⟩))
    (hvb' : vcp.blocks[b']? = some vb') (hi : vb'.insts[k]? = some (.rets us)) :
    ∃ b vb, src = .run ⟨b, k, ρ, w⟩ ∧ vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us) := by
  cases hm with
  | @blk b _ _ _ _ hLb hσ =>
    obtain ⟨vb, vb1, hvb, hvb1, -, -, hsz, hins, -⟩ := (H.kept b b' hLb hσ).blocks
    rw [hvb'] at hvb1; cases hvb1
    have hklt : k < vb.insts.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hi).1
    obtain ⟨i, hi0⟩ : ∃ i, vb.insts[k]? = some i := ⟨_, Array.getElem?_eq_getElem hklt⟩
    obtain ⟨i'', hi'', hsame⟩ := hins k i hi0
    rw [hi] at hi''; cases hi''
    obtain ⟨-, -, hr⟩ := sameInst_facts' hds hsame
    exact ⟨b, vb, rfl, hvb, by rw [hi0, hr us rfl]⟩
  | pend _ _ _ _ _ _ _ _ _ _ _ _ heb hebi =>
    rw [heb] at hvb'; cases hvb'
    rw [hebi] at hi; cases hi

/-- **The VCode's returned values are the prepared `rets`' uses** (module doc): an event-free
VCode run from `vR` to a configuration related by `prepare` to a `rets` of the prepared code,
and a VCode return from `vR`, return that `rets`' uses (at its `ρ`) and world. -/
theorem ret_link {vc vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)}
    (H : PrepFacts vc vcp L ss ss') {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {vR : VState CV ArmState} {trR : List (List Ev)} {vV : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run vR) trR vV) (hnil : ∀ e ∈ trR, e = [])
    {b' k : Nat} {ρ : Nat → CV} {w : ArmState} {vb' : VBlock} {us : List (Reg × Reg)}
    (hm : PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' vV (.run ⟨b', k, ρ, w⟩))
    (hvb' : vcp.blocks[b']? = some vb') (hi : vb'.insts[k]? = some (.rets us))
    {us0 : List (Reg × Reg)} {outs : List CV} {w' : ArmState}
    (hret : Driver.VRetFrom vc (csem F fc X) vR us0 outs w') :
    ∃ ops, (MInst.rets us).operands = .ok ops ∧ us0 = us ∧ outs = vuses ops ρ ∧ w' = w := by
  have hds := (driverSem_csem F fc X).toDriverSemG
  obtain ⟨b, vb, rfl, hvb, hi0⟩ := pmatch_rets H hds hm hvb' hi
  obtain ⟨b1, k1, ρ1, w1, vb1, ops1, outs1, hstar, hvb1, hi1, hops1, hvals, hsem1⟩ := hret
  have hstar2 := star_of_vtrun_nil hr hnil
  -- a running state at a `rets` steps to a return, so a run from it reaches no running state
  have hstop : ∀ {b2 k2 : Nat} {ρ2 : Nat → CV} {w2 : ArmState} {vb2 : VBlock}
      {us2 : List (Reg × Reg)} {T : VState CV ArmState}, vc.blocks[b2]? = some vb2 →
      vb2.insts[k2]? = some (.rets us2) →
      Star (VStep vc (csem F fc X)) (.run ⟨b2, k2, ρ2, w2⟩) (.run T) → T = ⟨b2, k2, ρ2, w2⟩ := by
    intro b2 k2 ρ2 w2 vb2 us2 T hvb2 hi2 h
    cases h with
    | refl => rfl
    | step h1 h2 =>
      cases h1 with
      | step hvb3 hi3 _ hsem3 _ hn3 =>
        rw [hvb2] at hvb3; cases hvb3
        rw [hi2] at hi3; cases hi3
        simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, rfl, rfl⟩ := hsem3
        cases hn3 with
        | ret =>
          cases h2 with
          | step h _ => cases h
  have heq : (⟨b1, k1, ρ1, w1⟩ : VState CV ArmState) = ⟨b, k, ρ, w⟩ := by
    rcases star_det (r := VStep vc (csem F fc X)) (fun _ _ _ h1 h2 => IselStep.vstep_det h1 h2) hstar hstar2 with h | h
    · exact (hstop hvb1 hi1 h).symm
    · exact hstop hvb hi0 h
  simp only [VState.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  rw [hvb] at hvb1; cases hvb1
  rw [hi0] at hi1; cases hi1
  simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem1
  obtain ⟨-, rfl, -⟩ := hsem1
  exact ⟨ops1, hops1, rfl, hvals, rfl⟩

end


end Concurrency.CallRetsAlloc

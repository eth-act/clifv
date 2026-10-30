import FV.E2E.WorldTrapStop
import FV.E2E.TrapCallTryPrep
import FV.E2E.RegLevelTrapCallTry

/-!
# The per-function world theorem with callee traps, `try_call`s included (S9e, #408)

`backend_correct_world_cleanup_trapstop` (`FV/E2E/WorldTrapStop.lean`, what the linked-program
induction applies per function) without its premise `∀ B ∈ f.blocks, B.term.isTry = false`, by
the device of S9b (`FV/E2E/DeadCleanupTrapCallTry.lean`): the proof stops at the trapping call
instead of following the device's exception into a handler.

* `regLevel_trapStop_coreT`: `regLevel_trapStop_core` with a third end, a raising `tryCall`, a
  semantics halting there (`hhaltT`), and the GOT pins of the calls the run reaches (`hgotS`) in
  place of `GotSem` (the halting `tryCall` of `haltTry` has no pin);
* `regLevel_trapStop_worldT`: `regLevel_trapStop_world` without `vcp.hasTryCall = false` (the
  `try_call` callee contract from `ActEntry.tries`);
* `vTryRaise_gotV_gen`: a run to a raising `tryCall` with the GOT pins (`GotPair`);
* **`backend_correct_world_cleanup_trapstopT`**: under `TrapsExplicitCT`, every activation stops
  at a trap site of `f` or at a callee-trap state at a call site of either kind (`CallTrapAtT`).
-/

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup

/-- **The register level of the explicit and the callee traps with the stopping state, `try_call`s
included** (`regLevel_trapStop_core` for a semantics that also halts at a raising `tryCall`): an
explicit trap of the VCode run is a trap site of the machine run after which every state errs; a
raising `call` or `tryCall` is a callee-trap state at a call site of either kind; in each case
every earlier state is `GoodX` and the stopping state has the body's `sp` and the function's
program. -/
theorem regLevel_trapStop_coreT {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    {XT : Option String → List CV → Arm.ArmState → Prop}
    (hRz : Realizes R.vc R.rf semU ckeep R.step (QA R) R.GoodX)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem R.F R.ctx R.X i uses w = some (outs, w', .halt))
    (hhaltT : ∀ info ti uses w obj w', (xrT XT).raise (callDest info) uses w = some (obj, w') →
      semU (.tryCall info ti) uses w =
        some ((defCons (.tryCall info ti)).map (fun _ => ofX 0), w', .halt))
    (hgotS : ∀ (ρ : Nat → CV) (w : Arm.ArmState) (b k : Nat) (ρ' : Nat → CV) (w' : Arm.ArmState)
      (vb : VBlock) (i : MInst) (ops : Array Operand) (info : CallInfo),
      Star (VStep R.vc semU) (.run ⟨0, 0, ρ, w⟩) (.run ⟨b, k, ρ', w'⟩) →
      R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → gotGuard R.gv R.X info (vuses ops ρ'))
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ c, VTraps R.vc semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt R.fb R.base c (E2E.runX R.step n R.s0) ∧
        (∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) ∧
        (∀ m, Arm.r .ERR (E2E.runX R.step (n + m + 1) R.s0) ≠ .None) ∧
        spOf (E2E.runX R.step n R.s0) = R.spB ∧
        (E2E.runX R.step n R.s0).program = R.fb.program R.base) ∧
    (∀ obj w', VUnwinds R.vc semU (xrT XT) (ρsel m₀) w₀ obj w' →
      ∃ n, R.CallTrapPreT XT (E2E.runX R.step n R.s0) ∧
        (∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) ∧
        spOf (E2E.runX R.step n R.s0) = R.spB ∧
        (E2E.runX R.step n R.s0).program = R.fb.program R.base) ∧
    (VTryRaiseFrom R.vc semU (xrT XT) ⟨0, 0, ρsel m₀, w₀⟩ →
      ∃ n, R.CallTrapPreT XT (E2E.runX R.step n R.s0) ∧
        (∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) ∧
        spOf (E2E.runX R.step n R.s0) = R.spB ∧
        (E2E.runX R.step n R.s0).program = R.fb.program R.base) := by
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_init hR hent hbe
  obtain ⟨hSim, hinit, -⟩ := checkedAt_sound_match (sem := semU) (keep := ckeep) hcheck
    (locVal R.fr (iterN R.step n0 R.s0)) (ρsel (locVal R.fr (iterN R.step n0 R.s0))) w₀ (hsel _)
  have hfin : ∀ n1 n2 n3, E2E.runX R.step (n0 + n1 + n2 + n3) R.s0 =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 R.s0))) := by
    intro n1 n2 n3
    rw [runX_eq]
    simp only [iterN_add]
  -- an exceptional end at a raising `call`/`tryCall` `i` of the site `info`
  have hend : ∀ (b k : Nat) (ρ : Nat → CV) (w1 : Arm.ArmState) (vb : VBlock) (i : MInst)
      (info : CallInfo) (ops : Array Operand) (outs : List CV) (w' : Arm.ArmState),
      Star (VStep R.vc semU) (.run ⟨0, 0, ρsel (locVal R.fr (iterN R.step n0 R.s0)), w₀⟩)
        (.run ⟨b, k, ρ, w1⟩) →
      R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
      (xrT XT).raise (callDest info) (vuses ops ρ) w1 = some (0, w1) →
      semU i (vuses ops ρ) w1 = some (outs, w', .halt) →
      outs.length = (ops.toList.filter Operand.isDef).length →
      ∃ n, R.CallTrapPreT XT (E2E.runX R.step n R.s0) ∧
        (∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) ∧
        spOf (E2E.runX R.step n R.s0) = R.spB ∧
        (E2E.runX R.step n R.s0).program = R.fb.program R.base := by
    intro b k ρ w1 vb i info ops outs w' hstar hvb hi hops hik hraise hsem hlen
    have hgg0 := hgotS _ _ _ _ _ _ _ _ _ info hstar hvb hi hops hik
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w1⟩) (.halt w') :=
      VStep.step hvb hi hops hsem hlen VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    obtain ⟨u, hu⟩ : ∃ u, iterN R.step n2 (iterN R.step n1 (iterN R.step n0 R.s0)) = u :=
      ⟨_, rfl⟩
    rw [hu] at hq2
    cases hms with
    | move => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | @op b' k' allocs its m w2 vb' i2 ops2 outs2 outs2' w2' ctl m2 c3 hvb' hi' hops' hsz hsem2
        hlen2 hho hcl hn =>
      obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
      simp only at hb' hk' hw'
      subst hb' hk' hw'
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      have hq2 := (qa_op hq2 hvb hi (fun us h => by
        rcases hik with rfl | ⟨ti, rfl⟩ <;> cases h)).1
      obtain ⟨j0, items, pre, regs, i', cA, cB, ls1, ls2, ps1, psm, ps2, T', cc', wh, ops'', hal, hit,
        hsplit, hasg, hc1', hops'', hstat, hchk', hcode2, h1', h2', htr', hdrop, hpc, hst⟩ :=
        q_op hq2 hvb hi
      rw [hops] at hops''; cases hops''
      subst hal
      have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal u r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      have hraise' : (xrT XT).raise (callDest info) (useVals ops regs u) w1 = some (0, w1) := by
        rw [← useVals_of_store hstat hm', hU0]
        exact hraise
      have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
        rw [← useVals_of_store hstat hm', hU0]
        exact hgg0
      have hrun : E2E.runX R.step (n0 + n1 + n2) R.s0 = u := by
        rw [← hu, runX_eq]
        simp only [iterN_add]
      have htrace : ∀ i < n0 + n1 + n2, R.GoodX (E2E.runX R.step i R.s0) := fun i hi => by
        rw [runX_eq]
        exact trace_add ht0 (trace_add ht1 ht2) i (by omega)
      rcases hik with rfl | ⟨ti, rfl⟩
      · have hcpc := callAt_of_q hq2 hvb hi call_hcall regs i' rfl hasg
        refine ⟨n0 + n1 + n2, ?_, htrace, by rw [hrun]; exact hst.sp, by rw [hrun]; exact hst.prog⟩
        rw [hrun]
        exact ⟨info, ⟨b, vb, k, hvb, .inl hi⟩, by rw [hst.sp]; exact RL.K_le hR,
          fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs,
          i', w1, hops, hstat, hasg, hcpc, hst.world, hst.align, hst.err, hgg,
          (xrT_some hraise').1⟩
      · have hcpc := callAt_of_q hq2 hvb hi tryCall_hcall regs i' rfl hasg
        have hcl0 : ti.clobberAll = false := trySite_clobberAll hR.alloc ⟨b, vb, k, hvb, hi⟩
        obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
        refine ⟨n0 + n1 + n2, ?_, htrace, by rw [hrun]; exact hst.sp, by rw [hrun]; exact hst.prog⟩
        rw [hrun]
        exact ⟨info, ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩, by rw [hst.sp]; exact RL.K_le hR,
          fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs,
          .call ic, w1, by rw [← operands_tryCall_call info ti]; exact hops,
          by rw [← clobbers_tryCall hcl0]; exact hstat, hasg', callAt_tryCall_call hcpc,
          hst.world, hst.align, hst.err, hgg, (xrT_some hraise').1⟩
  refine ⟨locVal R.fr (iterN R.step n0 R.s0), fun c htr => ?_, fun obj w' hu => ?_, fun hu => ?_⟩
  · -- an explicit trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨hnil, hform⟩ :=
      csem_halt (hhalt _ _ _ _ _ (by rw [htc]; exact Option.some_ne_none _) hsem)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hnr : ∀ us, i ≠ .rets us := by
          intro us h
          rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
        have hq2 := (qa_op hq2 hvb hi hnr).1
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, hstuck, hsp, hprog⟩ := trap_udf_stop hR hq2 hvb hi
          refine ⟨n0 + n1 + n2 + 0, by rw [hfin]; exact htrap, fun i hi => ?_, fun m => ?_,
            by rw [hfin]; exact hsp, by rw [hfin]; exact hprog⟩
          · rw [runX_eq]
            exact trace_add ht0 (trace_add ht1 ht2) i (by omega)
          · rw [show n0 + n1 + n2 + 0 + m + 1 = n0 + n1 + n2 + (m + 1) by omega, hfin]
            exact hstuck m
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (hhalt _ _ _ _ _ (by simp [trapCode?]) hsem2)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, hgx3, hstuck, hsp, hprog⟩ :=
              trap_trapIf_stop hR hq2 hvb hi hops' hholds
            refine ⟨n0 + n1 + n2 + n3, by rw [hfin]; exact htrap, fun i hi => ?_, fun m => ?_,
              by rw [hfin]; exact hsp, by rw [hfin]; exact hprog⟩
            · rw [runX_eq]
              exact trace_add ht0 (trace_add ht1 (trace_add ht2 hgx3)) i (by omega)
            · rw [show n0 + n1 + n2 + n3 + m + 1 = n0 + n1 + n2 + (n3 + m + 1) by omega, hfin]
              exact hstuck m
  · -- a raising `call`
    obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
    obtain ⟨-, hobj, hw⟩ := xrT_some hraise
    rw [hobj, hw] at hraise
    exact hend b k ρ w1 vb _ info ops outs w' hstar hvb hi hops (.inl rfl) hraise hsem hlen
  · -- a raising `tryCall`
    obtain ⟨b, k, ρ, w1, vb, info, ti, ops, obj, w', hstar, hvb, hi, hops, hraise⟩ := hu
    obtain ⟨-, hobj, hw⟩ := xrT_some hraise
    rw [hobj, hw] at hraise
    exact hend b k ρ w1 vb _ info ops _ w1 hstar hvb hi hops (.inr ⟨ti, rfl⟩) hraise
      (hhaltT info ti _ w1 0 w1 hraise) (by simp [defCons, hops])

end Backend.Proof

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `haltTry` of the value semantics with the GOT pins keeps the GOT invariant. -/
theorem gotPair_haltTry (vc : VCode) (X : ExtSem) (gv : Nat → String → Prop) (F : BitVec 64 → Prop)
    (ctx : FnCtx) (XR : XRaise) :
    GotPair vc X (haltTry XR (valueSemVU gv F ctx X XR)) (haltTry XR (valueSemVU gv F ctx X XR)) where
  agree _ _ _ _ _ _ _ _ _ _ _ := rfl
  got _ _ _ _ _ _ _ h := by
    simp only [haltTry, valueSemVU, specForm, pureForm, cmpForm, Bool.false_or, Bool.false_eq_true, ite_false, csemVU, csemU, csem,
      Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-- **A run to a raising `tryCall` with the GOT pins** (`vTraps_gotV_gen`'s counterpart). -/
theorem vTryRaise_gotV_gen {vc : VCode} {X : ExtSem} {sem₁ sem₂ : Sem} (hG : GotPair vc X sem₁ sem₂)
    {XR : XRaise} {ρ₀ : Nat → CV} {w₀ : Arm.ArmState}
    (h : VTryRaiseFrom vc sem₁ XR ⟨0, 0, ρ₀, w₀⟩) : VTryRaiseFrom vc sem₂ XR ⟨0, 0, ρ₀, w₀⟩ := by
  obtain ⟨b, k, ρ, w, vb, info, ti, ops, obj, w', hs, hvb, hi, hops, hraise⟩ := h
  exact ⟨b, k, ρ, w, vb, info, ti, ops, obj, w', (gotInv_star_gen hG (gotInv_entry vc X ρ₀ w₀) hs).1,
    hvb, hi, hops, hraise⟩

/-- **The register level of the explicit and the callee traps for an activation inside a
linked program, with the stopping state, `try_call`s included** (`regLevel_trapStop_world`
without `vcp.hasTryCall = false`): an explicit trap of the VCode run is a trap site after which
every state errs or (the run passing a raising `tryCall` first) a callee-trap state; a raising
`call` or `tryCall` is a callee-trap state at a call site of either kind (`CallTrapAtT`); every
earlier state is `GoodX`, `sp` is the body's and the program the function's. -/
theorem regLevel_trapStop_worldT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks} {K : Nat}
    {F G : BitVec 64 → Prop} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (XT : Option String → List CV → Arm.ArmState → Prop)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : ActEntry vcp rf af fa fb K F G X H base ra s w₀) (ρ₀ : Nat → CV) :
    (∀ c, VTraps vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) ρ₀ w₀ c →
      ∃ n, (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base ∧
        ((TrapAt fb base c (runX (ArmStepX X H fa) n s) ∧
            ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) ∨
          CallTrapAtT vcp F K G s fa base X (GotV vcp) XT (runX (ArmStepX X H fa) n s))) ∧
    (∀ obj w', VUnwinds vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) (xrT XT)
        ρ₀ w₀ obj w' →
      ∃ n, (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base ∧
        CallTrapAtT vcp F K G s fa base X (GotV vcp) XT (runX (ArmStepX X H fa) n s)) ∧
    (VTryRaiseFrom vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) (xrT XT)
        ⟨0, 0, ρ₀, w₀⟩ →
      ∃ n, (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base ∧
        CallTrapAtT vcp F K G s fa base X (GotV vcp) XT (runX (ArmStepX X H fa) n s)) := by
  obtain ⟨cc, ins, hcA⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hcA.at
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, GotV vcp⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hb⟩,
    he.abi.program, he.gfree⟩
  have hF : R.F = F := he.hF
  have hreal := realizes_value_all hR (by rw [hF]; exact he.calls)
    (fun h => by rw [hF]; exact he.tries h) (by rw [hF]; exact he.tls) hcov
  have hRz := realizes_haltTry (XR := xrT XT) (semU := valueSemVU R.gv R.F R.ctx R.X (xrT XT))
    hreal (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr])
  have hbe' : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀ := by
    rw [hF]; exact he.body
  have hnt : ∀ i, trapCode? i ≠ none → ∀ info ti, i ≠ .tryCall info ti := by
    intro i ht info ti e; subst e; simp [trapCode?] at ht
  have hGP := gotPair_haltTry R.vc R.X R.gv R.F R.ctx (xrT XT)
  obtain ⟨_, h1, h2, h3⟩ := regLevel_trapStop_coreT (XT := XT) hR he.abi hat hRz
    (fun i _ _ _ _ ht h => valueSemVU_halt_trap ht (by rwa [haltTry_not_try (hnt i ht)] at h))
    (fun _ _ _ _ _ _ h => haltTry_raise h)
    (fun ρ w _ _ _ _ _ _ _ info hs hvb hi hops hik =>
      gotGuard_of_inv (gotInv_star_gen hGP (gotInv_entry _ _ ρ w) hs).2 hvb hi hops info hik)
    hbe' (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  have e1 : valueSemVU R.gv R.F R.ctx R.X (xrT XT) =
      valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT) := by
    rw [hF]; rfl
  have hstop : ∀ n, R.CallTrapPreT XT (runX R.step n R.s0) →
      (∀ i < n, R.GoodX (runX R.step i R.s0)) →
      spOf (runX R.step n R.s0) = R.spB → (runX R.step n R.s0).program = R.fb.program R.base →
      (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base ∧
        CallTrapAtT vcp F K G s fa base X (GotV vcp) XT (runX (ArmStepX X H fa) n s) := by
    intro n hct ht hsp hprog
    refine ⟨fun i hi => (ht i hi).act, hsp, hprog, ?_⟩
    have hct' : CallTrapAtT R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT
        (runX R.step n R.s0) := hct
    rw [hF] at hct'
    exact hct'
  -- an earlier raising `tryCall` on the way
  have hearly : ∀ v, (VConf.run ⟨0, 0, ρ₀, w₀⟩ : VConf CV Arm.ArmState) = .run v →
      VTryRaiseFrom R.vc (haltTry (xrT XT) (valueSemVU R.gv R.F R.ctx R.X (xrT XT))) (xrT XT) v →
      ∃ n, R.CallTrapPreT XT (runX R.step n R.s0) ∧ (∀ i < n, R.GoodX (runX R.step i R.s0)) ∧
        spOf (runX R.step n R.s0) = R.spB ∧ (runX R.step n R.s0).program = R.fb.program R.base := by
    intro v hv htr
    cases hv
    exact h3 htr
  refine ⟨fun c htr => ?_, fun obj w' hu => ?_, fun hu => ?_⟩
  · rw [← e1] at htr
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    rcases star_haltTry (XR := xrT XT) hstar with hs | ⟨v, hv, hT⟩
    · have hsem' := (haltTry_not_try (XR := xrT XT)
        (sem := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) (hnt i (by rw [htc]; simp)) _ _).trans hsem
      obtain ⟨n, htrap, ht, hstuck, hsp, hprog⟩ :=
        h1 c ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem', htc⟩
      exact ⟨n, fun i hi => (ht i hi).act, hsp, hprog, .inl ⟨htrap, hstuck⟩⟩
    · obtain ⟨n, hct, ht, hsp, hprog⟩ := hearly v hv hT
      obtain ⟨h1', h2', h3', h4'⟩ := hstop n hct ht hsp hprog
      exact ⟨n, h1', h2', h3', .inr h4'⟩
  · rw [← e1] at hu
    obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
    rcases star_haltTry (XR := xrT XT) hstar with hs | ⟨v, hv, hT⟩
    · have hsem' := (haltTry_not_try (XR := xrT XT)
        (sem := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) (i := .call info)
        (fun _ _ h => by cases h) _ _).trans hsem
      obtain ⟨n, hct, ht, hsp, hprog⟩ :=
        h2 obj w' ⟨b, k, ρ, w1, vb, info, ops, outs, hs, hvb, hi, hops, hraise, hsem', hlen⟩
      exact ⟨n, hstop n hct ht hsp hprog⟩
    · obtain ⟨n, hct, ht, hsp, hprog⟩ := hearly v hv hT
      exact ⟨n, hstop n hct ht hsp hprog⟩
  · rw [← e1] at hu
    obtain ⟨b, k, ρ, w1, vb, info, ti, ops, obj, w', hstar, hvb, hi, hops, hraise⟩ := hu
    rcases star_haltTry (XR := xrT XT) hstar with hs | ⟨v, hv, hT⟩
    · obtain ⟨n, hct, ht, hsp, hprog⟩ :=
        h3 ⟨b, k, ρ, w1, vb, info, ti, ops, obj, w', hs, hvb, hi, hops, hraise⟩
      exact ⟨n, hstop n hct ht hsp hprog⟩
    · obtain ⟨n, hct, ht, hsp, hprog⟩ := hearly v hv hT
      exact ⟨n, hstop n hct ht hsp hprog⟩

/-- **The per-function world theorem with callee traps and the stopping state, `try_call`s
included** (`backend_correct_world_cleanup_trapstop` without `∀ B ∈ f.blocks,
B.term.isTry = false`, under `TrapsExplicitCT`): every activation (`ActEntry`) of a function whose
run traps with `tc` stops at a state with the body's `sp` and the function's program, every
earlier state `GoodX`, which is a trap site of `f` with `tc` after which every state errs, or a
callee-trap state at a call site of either kind (`CallTrapAtT` with the GOT pins `GotV vcp` and the
trapping callees `TrapCallSem … tc`). -/
theorem backend_correct_world_cleanup_trapstopT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true) (hp : p.funcs = [])
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXT : XTrapsOk env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitCT env p cs) {fuel : Nat} {tc : Clif.TrapCode}
    (hrun : Clif.runLoop env p fuel cs = .trapped tc) :
    ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
      ∃ n, (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base ∧
        ((TrapAt fb base tc (runX (ArmStepX X H fa) n s) ∧
            ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) ∨
          CallTrapAtT vcp F K G s fa base X (GotV vcp)
            (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
              (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X tc)
            (runX (ArmStepX X H fa) n s)) := by
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  let XT := TrapCallSem env (f.externs.map (·.2)) (indSigs f) (RelW Γ f c) X tc
  let fctx : FnCtx := ⟨fa.k, af.slotBase⟩
  have hexcl : ∀ d uses w, X.call d uses w ≠ none → (xrT XT).raise d uses w = none :=
    fun _ _ _ hne => xrT_none fun h => hne h.1
  have houtB := outgoing_le_intBaseCleanupA hc.toA
  let sem := valueSemU F fctx X (xrT XT)
  have hRef : Refines F sem := refines_valueSemU _ _ X (xrT XT)
  have hmem : MemRefines F slotOff syms sem := memRefines_valueSemU _ _ X (xrT XT) hslot hsym
  have hcalls := callsRefine_valueSemU (F := F) (ctx := fctx) (xCallsOk_trapEnv (c := tc) hX) hexcl
  have hicalls := indCallsRefine_valueSemU (F := F) (ctx := fctx)
    (xCallsIndOk_trapEnv (c := tc) hXI) hsym (fun _ _ _ h => h.1.1.symbols) hexcl
  -- CLIF → VCode up to the trapping step, on the proof device `trapEnv env tc`
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs⟩ := loweringU_of_check hlU
  have HD : DriverHyp f vc ctx st0 R gn bl A sem (RelW Γ f c) (trapEnv env tc).toEnv p :=
    { shape := hshape
      cert := hcert
      dsem := (driverSem_valueSemU F fctx X (xrT XT)).toDriverSemG
      insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
        indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
        (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
        (memRelOk_relW Γ f c)
      terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
        branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
      ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
      indSig := indSig_of_subset hsub
      subE := hsub.subsetE
      entryLocs := entryOk_of_check hc.lowerOk
      brIdx := hbr
      noTail := noTail_of_subset hsub
      tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
        (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
      tryExt := hsub.tryExterns
      tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef
        (mrStable_relW Γ f c) hicalls
      tryIndSig := tryIndSig_of_subset hsub
      cfg := by
        obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
        exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩ }
  have HR : RaiseHyp f sem (RelW Γ f c) (trapEnv env tc) F X (xrT XT) slotOff syms
      (RAFrame.compute vcp rf).intBase :=
    ⟨raiseSem_valueSemU _ _ X (xrT XT), hRef, hmem, mrStable_relW Γ f c, outArgsOk_relW Γ f c,
      memRelOk_relW Γ f c, callsStack_mono (callsStack_of_check hc.lowerOk) houtB,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB, xRaiseOk_trapEnv hXT,
      xRaiseIndOk_trapEnv hXT, hsym, fun sl cm w h => (memRelOk_relW Γ f c).symbols sl cm w h⟩
  obtain ⟨B0, hentB, hbody, hterm, hty, hregs⟩ := hcs.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hentB
  have hD := driver_trapStop (slots := cs.frame.slots) (ρ₀ := fun _ => 0) hp HD hUs HR
    (driverSem_valueSemU F fctx X (xrT XT)) hB0 hcs.callers hcs.func rfl hbody hterm hregs
    hty.symm hcs.sig hrel hargs htr hrun
  -- `prune` + `prepare`
  have hP := prepareCorrectU_cleanup (driverSem_valueSemU F fctx X (xrT XT))
    (fun _ _ _ _ _ _ hp he => valueSemU_pure hp he) (valueSemU_cmpOverwrite _ _ _ _) hc.prepOk
    (xrT XT)
  intro H G base ra s he
  obtain ⟨hR1, hR2, hR3⟩ := regLevel_trapStop_worldT hc.check hc.alloc hc.emit hc.layout hcov XT
    he (fun _ => 0)
  rcases hD with h | ⟨obj, w', h⟩ | h
  · obtain ⟨n, ht, hsp, hprog, hcase⟩ :=
      hR1 tc (vTraps_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).2 tc h))
    exact ⟨n, ht, hsp, hprog, hcase⟩
  · obtain ⟨n, ht, hsp, hprog, hct⟩ :=
      hR2 obj w' (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ h))
    exact ⟨n, ht, hsp, hprog, .inr hct⟩
  · obtain ⟨n, ht, hsp, hprog, hct⟩ := hR3 (vTryRaise_gotV_gen (gotPair_valueU _ _ _)
      (tryRaise_cleanup (driverSem_valueSemU F fctx X (xrT XT))
        (fun _ _ _ _ _ _ hp' h' => valueSemU_pure hp' h') (valueSemU_cmpOverwrite _ _ _ _)
        hc.prepOk (xrT XT) h))
    exact ⟨n, ht, hsp, hprog, .inr hct⟩

end E2E

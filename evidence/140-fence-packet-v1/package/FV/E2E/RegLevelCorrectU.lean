import FV.E2E.RegLevelCorrect
import FV.E2E.RegLevelUTry
import FV.E2E.RegLevelFrameSaved
import FV.E2E.RegLevelCallSite
import FV.E2E.UnwindStatement

/-!
# The register-level theorem with unwinding (S10e, #232)

`RegLevelCorrectU` (`FV/E2E/UnwindStatement.lean`) for the machine with unwinding
`Unw.ArmStepU X H U T fa`: the counterpart of `regLevelCorrect_world_atX` →
`regLevelCorrect_backend_ex` (`FV/E2E/RegLevelCorrect.lean`).

* `checkedAt_sound_match`, `matchRun_uses`: `checkedAt_sound` with its relation (`Match`)
  exposed, and the relation's fact that the allocated code reads the values the VCode reads (a
  raising call's exception object is the one of the VCode run's callee).
* `regLevelCorrect_coreU`: **the generic core**, for any activation semantics `semU` realised by
  the machine with unwinding (`Realizes … R.stepU … R.GoodXU`, e.g. `realizes_allU` from a
  realisation of `csemV` or of the dead-cleanup value semantics), agreeing with `csem` at the
  returns and the traps. Returns and traps as in `regLevelCorrect_world_atX` (the old trace
  facts transported by `RLU.iterN_stepU`); an exceptional end (`VUnwinds`: a `call` whose callee
  raises) reaches the raising call state (`forward_last`), where the raising callees' contract
  (`CalleeUnwOkG`) gives the unwinder's state `t`, the personality continues (`personality_plain`
  with the call-site table `LsdaAt`, or no LSDA; the call-site bridge `SiteAt`) and the frame row
  restores the ABI return (`unwind_call_restores`, the frame invariant `frameSaved_of_stRel` at
  `t`, threaded by `SavedInv` through the run under `savedCheck`).
* `regLevelCorrect_world_atXU` → `regLevelCorrect_world_exU`/`regLevelCorrect_worldU` →
  `regLevelCorrect_backend_exU_of`/`regLevelCorrect_backendU_of`: the activation of a compiled
  function, still generic in the semantics (the dead-cleanup value semantics instantiates them);
  `regLevelCorrect_backend_exU`/`regLevelCorrect_backendU`: `RegLevelCorrectUEx`/
  `RegLevelCorrectU` for `csemU` (`realizes_csemU`, `realizesTryRaise_of_tables`). The tables
  the unwinder reads (`T`) are hypotheses (S10f discharges them from the linked bytes).
* Non-vacuity: `RegLevelCorrectUWitness.premises` (the unwinding premises hold on a compiled
  function with a call), `RegLevelCorrectUWitness.backendU_applies`.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.UnwindTables

/-! ## The register-allocation simulation with its relation -/

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {sem : ISem V W} {keep : Reg → V → V}
  {c : CheckCtx} {ins : Array (Option AState)}

/-- `checkedAt_sound` for the relation `Match` of its proof. -/
theorem checkedAt_sound_match {a0 : AState} (hc : CheckedAt vc rf c ins a0) (m₀ : Loc → V)
    (ρ₀ : Nat → V) (w₀ : W) (hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r))) :
    IsSimulation vc rf sem keep (Match c ins keep (fun r => m₀ (.reg r))) ∧
      Match c ins keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) ∧
      ∀ {vals m} {w : W} {v}, Match c ins keep (fun r => m₀ (.reg r)) (.ret vals m w) v →
        ∀ r ∈ calleeSaved, keep r (m (.reg r)) = keep r (m₀ (.reg r)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro cf v c' hR hs
    cases cf with
    | run ms =>
      cases v with
      | run vs =>
        rcases sim_step_at sem keep hc hR hs with ⟨ms', rfl, hmr, hlt⟩ | hr
        · exact .inl ⟨hmr, hlt⟩
        · exact .inr hr
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases hs
    | halt => cases hs
  · intro cf v v' hR hv
    cases cf with
    | run ms =>
      cases v with
      | run vs => exact sim_progress_at sem keep hc hR hv
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases v <;> first | exact hR.elim | cases hv
    | halt => cases v <;> first | exact hR.elim | cases hv
  · intro vals m w v hR
    cases v with
    | ret vals' w' => obtain ⟨rfl, rfl, -⟩ := hR; rfl
    | _ => exact hR.elim
  · intro w v hR
    cases v with
    | halt w' => cases hR; rfl
    | _ => exact hR.elim
  · intro s v hR
    cases v with
    | run s' => exact ⟨s', rfl⟩
    | _ => exact hR.elim
  · intro b src dst its m w v hR
    cases v with
    | run vs =>
      obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hR
      obtain ⟨-, hrun'⟩ := runItems_move hrun
      exact ⟨hb, hw, vb, _, out, hvb, hrun', Inv_move _ _ hinv, hedges⟩
    | _ => exact hR.elim
  · intro b k a its m w vs hR
    obtain ⟨hb, hw, vb, a, out, hvb, hrun, -⟩ := hR
    obtain ⟨-, hk, -⟩ := runItems_op hrun
    exact ⟨hb.symm, hk.symm, hw.symm⟩
  · obtain ⟨a, out, ha, hrb, hedges⟩ :=
      verifyBlock_ok (hc.blocks 0 (Nat.pos_of_ne_zero hc.nonempty))
    rw [hc.entry] at ha
    cases ha
    obtain ⟨vb, items, hvb, hitems, hrun⟩ := runBlock_ok hrb
    rw [hc.rf_eq] at hitems
    have : rf.blocks[0]! = items := by simp [getElem!_def, hitems]
    simp only [MConf.init, VConf.init, this]
    exact ⟨rfl, rfl, vb, a0, out, hvb, hrun, hinv0, hedges⟩
  · intro vals m w v hR
    cases v with
    | ret => exact hR.2.2
    | _ => exact hR.elim

/-- **Related configurations read the same values**: at an instruction item related by `Match`
to a VCode state, the allocated code's uses are the VCode's (`op_sound`). -/
theorem matchRun_uses {a0 : AState} (hc : CheckedAt vc rf c ins a0) {r₀ : Reg → V} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → V} {w : W} {vs : VState V W}
    {c' : MConf V W} (hm : MatchRun c ins keep r₀ ⟨b, .op k allocs :: its, m, w⟩ vs)
    (hs : MStep vc sem keep rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') {vb : VBlock}
    {i : MInst} {ops : Array Operand} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops) :
    ((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2) = vuses ops vs.ρ := by
  obtain ⟨b', k', ρ, w''⟩ := vs
  obtain ⟨hb, hw, vb', a, out, hvb', hrun, hinv, -⟩ := hm
  simp only at hb hw
  subst hb hw
  rw [hc.vc_eq, hvb] at hvb'
  cases hvb'
  obtain ⟨_, hk, i', ops', a', hi', hops', hstep, -⟩ := runItems_op hrun
  subst hk
  rw [hi] at hi'
  cases hi'
  rw [hops] at hops'
  cases hops'
  cases hs with
  | op hvb2 hi2 hops2 hsz hsem hlen hho hclob hnext =>
    rw [hvb] at hvb2
    cases hvb2
    rw [hi] at hi2
    cases hi2
    rw [hops] at hops2
    cases hops2
    exact (op_sound hstep hinv hlen hho hclob).2.1

/-- A realisation keeps an invariant of the allocated code's steps. -/
theorem realizes_and {S : Type} {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    {P : MConf V W → Prop} (h : Realizes vc rf sem keep step Q T)
    (hP : ∀ c c', MStep vc sem keep rf c c' → P c → P c') :
    Realizes vc rf sem keep step (fun s c => Q s c ∧ P c) T := by
  intro s c c' ⟨hq, hp⟩ hm
  obtain ⟨n, c'', hm', hq', ht⟩ := h s c c' hq hm
  exact ⟨n, c'', hm', ⟨hq', hP _ _ hm' hp⟩, ht⟩

end

/-! ## The generic core -/

/-- **The register-level simulation with unwinding, generic in the activation semantics**: for
a semantics `semU` that the machine with unwinding realises (`hRz`) and that agrees with `csem`
at the returns and at the trapping instructions, every return, trap and exceptional end
(`RegLevelUnw`) of the prepared VCode under `semU` is one of the machine run from the ABI entry
state. The exceptional ends need the call-site table in the tables `T` (`LsdaAt`), the call-site
bridge (`SiteAt`), the frame rows (`T.cie`, `T.fde` from `unwindRows`) and the frame-invariant
check `savedCheck`. -/
theorem regLevelCorrect_coreU {R : RLU} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hgot : GotSem R.gv R.X semU)
    (hRz : Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL)
      R.GoodXU)
    (hrets : ∀ us uses w, semU (.rets us) uses w = csem R.F R.ctx R.X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem R.F R.ctx R.X i uses w = some (outs, w', .halt))
    (hlsda : R.T.lsda = none ∨ LsdaAt R) (hsite : SiteAt R.toRL) {rows : List (Nat × Cfi)}
    (hrows : unwindRows R.af R.fa = .ok rows) (hcie : R.T.cie = cieInsns)
    (hfde : R.T.fde = insnsFrom 0 rows) (hsaved : savedCheck R.vc R.rf = true)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w, VReturns R.vc semU (ρsel m₀) w₀ us vals w →
      ∃ n, ArmRet ra R.s0 (E2E.runX R.stepU n R.s0) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX R.stepU n R.s0) p = x) ∧
        (∀ a, ¬ R.F a → (E2E.runX R.stepU n R.s0).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX R.stepU n R.s0) = Arm.r f w) ∧
        (∀ a, R.G a → (E2E.runX R.stepU n R.s0).mem a = R.s0.mem a) ∧
        (E2E.runX R.stepU n R.s0).program = R.s0.program) ∧
    (∀ c, VTraps R.vc semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt R.fb R.base c (E2E.runX R.stepU n R.s0)) ∧
    RegLevelUnw semU R.XR R.F R.stepU R.vc ra R.s0 (ρsel m₀) w₀ := by
  have hf : R.af.frame = true := lowerRFunc_frame hR.alloc
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hrf : savedCheckRF R.vc R.rf = true := by
    have h := hsaved
    simp only [savedCheck, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_init hR hent hbe
  have h0 : iterN R.stepU n0 R.s0 = iterN R.step n0 R.s0 := RLU.iterN_stepU hR hU n0 R.s0 ht0
  have he : ∀ r ∈ calleeSaved, locVal R.fr (iterN R.step n0 R.s0) (.reg r) = regVal R.s0 r :=
    entry_calleeSaved hf0
  obtain ⟨hSim, hinit, hkeep⟩ := checkedAt_sound_match (sem := semU) (keep := ckeep) hcheck
    (locVal R.fr (iterN R.step n0 R.s0)) (ρsel (locVal R.fr (iterN R.step n0 R.s0))) w₀ (hsel _)
  have hRz' := realizes_and hRz
    (P := SavedInv R.rf ckeep (fun r => locVal R.fr (iterN R.step n0 R.s0) (.reg r)))
    fun _ _ hm hp => savedInv_step hrf hm hp
  have hq0' : QA R.toRL (iterN R.stepU n0 R.s0)
      (MConf.init R.rf (locVal R.fr (iterN R.step n0 R.s0)) w₀) ∧
      SavedInv R.rf ckeep (fun r => locVal R.fr (iterN R.step n0 R.s0) (.reg r))
        (MConf.init R.rf (locVal R.fr (iterN R.step n0 R.s0)) w₀ : MConf CV Arm.ArmState) :=
    ⟨.inl ⟨by rw [h0]; exact hq0, hA0⟩, savedInv_init _ _ _ _⟩
  have hfin : ∀ n1 n2 n3, E2E.runX R.stepU (n0 + n1 + n2 + n3) R.s0 =
      iterN R.stepU n3 (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0))) := by
    intro n1 n2 n3
    rw [runX_eq]
    simp only [iterN_add]
  refine ⟨locVal R.fr (iterN R.step n0 R.s0), fun us vals w hret => ?_, fun c htr => ?_,
    fun obj w' hu => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨n1, c1, hq1, hr1, -⟩ := forward hSim hRz' hstar hinit hq0'
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops
    cases hops
    have hsem' := hsem
    rw [hrets] at hsem'
    simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, rfl, -⟩ := hsem'
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w₁⟩) (.ret vals w₁) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_
        (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz' h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      have hks := hkeep hr3
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [operands_retsC] at hops'; cases hops'
        have hsem3 := hsem2
        rw [hrets] at hsem3
        simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, rfl, rfl⟩ := hsem3
        cases hn with
        | ret _ =>
        rw [rets_store hlen2 rfl hho hcl] at hks
        obtain ⟨mt, hq2'⟩ := qa_q hq2
        have hst := q_stRel hq2'
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hsvd, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machine hR hent hq2 hvb hi
        have e3 := RLU.iterN_stepU hR hU n3 _ ht3
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 R.s0) (.reg r) =
            regVal (iterN R.step n0 R.s0) r := fun _ => rfl
        refine ⟨n0 + n1 + n2 + n3, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
        all_goals rw [hfin, e3]
        · exact hpc
        · exact herr
        · exact hsp
        · intro n hn
          simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
          obtain ⟨a, ha, rfl⟩ := hn
          by_cases h29 : a = 10
          · subst h29; exact hx29
          obtain ⟨hcs, hal⟩ := calleeSaved_x (n := 19 + a) (by omega) (by omega)
          by_cases hsv : Reg.x (19 + a) ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have hne : ∀ q, q < 32 → q ≠ 19 + a →
              Arm.StateField.GPR (rnum (19 + a)) ≠ .GPR (BitVec.ofNat 5 q) :=
            fun q h1 h2 e => rnum_ne (a := 19 + a) (b := q) (by omega) h1 (Ne.symm h2)
              (Arm.StateField.GPR.inj e)
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
            (hne 16 (by omega) (by omega))] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          by_cases hsv : Reg.v n ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (by simp) (by simp) (by simp)] at k1
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) R.s0).setWidth 64
          rw [k2]
          exact setWidth128_inj k1
        · intro j v p x hj hx
          have e1 := hSim.ret hr3
          simp only [VConf.ret.injEq] at e1
          rw [e1.1] at hx
          exact hvalsM _ (operands_retsC ns) j v p x hj hx
        · intro a ha
          rw [hmem]
          exact hst.world.2.1 a ha
        · intro f hf' h29 h31
          rw [hfld f hf' h29 h31]
          exact hst.world.1 f hf'
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, -⟩ := forward hSim hRz' hstar hinit hq0'
    obtain ⟨hnil, hform⟩ :=
      csem_halt (hhalt _ _ _ _ _ (by rw [htc]; exact Option.some_ne_none _) hsem)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz' h1 _ c1 _ (Nat.le_refl _) hr1 hq1
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
          exact ⟨n0 + n1 + n2 + 0, by rw [hfin]; exact (trap_udf hR hq2 hvb hi).1⟩
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (hhalt _ _ _ _ _ (by simp [trapCode?]) hsem2)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, ht3, -⟩ := trap_trapIf hR hq2 hvb hi hops' hholds
            exact ⟨n0 + n1 + n2 + n3, by rw [hfin, RLU.iterN_stepU hR hU n3 _ ht3]; exact htrap⟩
  · -- an exceptional end: a `call` whose callee raises
    obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
    obtain ⟨n1, c1, hq1, hr1, -⟩ := forward hSim hRz' hstar hinit hq0'
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w1⟩) (.halt w') :=
      VStep.step hvb hi hops hsem hlen VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, hS2⟩, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz' h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    obtain ⟨u, hu⟩ : ∃ u, iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0)) = u :=
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
      have hq2 := (qa_op hq2 hvb hi (fun _ h => by cases h)).1
      rw [hops] at hops'; cases hops'
      -- the allocated code reads the VCode's uses: the same raising callee
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      obtain ⟨j0, items, pre, regs, i', cA, cB, ls1, ls2, ps1, psm, ps2, T', cc', wh, ops'', hal, hit,
        hsplit, hasg, hc1', hops'', hstat, hchk', hcode2, h1', h2', htr', hdrop, hpc, hst⟩ :=
        q_op hq2 hvb hi
      rw [hops] at hops''; cases hops''
      subst hal
      have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal u r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      have hraise' : R.XR.raise (callDest info) (useVals ops regs u) w1 = some (obj, w') := by
        rw [← useVals_of_store hstat hm', hU0]
        exact hraise
      have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
        rw [← useVals_of_store hstat hm', hU0]
        exact (hgot _ _ _ _).1 hsem
      -- the raising callees' contract: the unwinder's state `t` at our call
      have hsite0 : R.vc.CallSite info := ⟨b, vb, k, hvb, .inl hi⟩
      have hcpc := callAt_of_q hq2 hvb hi call_hcall regs i' rfl hasg
      have hraiseU := hU.os info (.call info) hsite0 (.inl rfl) u
        (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
        hst.gkeep cc' wh ops regs i' w1 hops hstat hasg hcpc hst.world hst.align hst.err hgg
      obtain ⟨t, hUr, hW, hFK, herrt, hprogt, hoth, hkc⟩ := hraiseU obj w' hraise'
      obtain ⟨hstepU, -⟩ := RLU.stepU_q_raise hR hq2 hvb hi (.inl rfl) hUr
      -- the personality continues at a plain call
      obtain ⟨j, x, hj, hpcj, -, hmem⟩ :=
        hsite u b k _ its m w1 vb _ info none hq2 hvb hi (.inl ⟨rfl, rfl⟩)
      have hpers : Unw.personality R.T.lsda (lineOffset R.L j + 4 - 1) = .continue := by
        rcases hlsda with hn | ⟨sites, hcs, hlsda'⟩
        · rw [hn]; rfl
        · rw [hlsda']; exact Unw.personality_plain hcs hmem
      have hne : R.fb.words.toList ≠ [] := by
        obtain ⟨_, wd, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
        intro h
        have : R.fb.words.size = 0 := by simpa using congrArg List.length h
        simp [this] at hk
      have hpb : progBase u = R.base := progBase_eq (by rw [hst.prog]; rfl) hne
      have hfit : lineOffset R.L j + 4 ≤ 2 ^ 64 := by
        have h1' := lineOffset_succ R.L j _ hj
        have h2' := lineOffset_le_size R.L (j + 1)
        have h3' := layout_sum hR.layout
        have h4' := hR.fit
        simp only [Line.size, RL.L] at h1' h2' h3' ⊢
        omega
      have hoff : (Arm.r .PC u + 4 - 1 - progBase u).toNat = lineOffset R.L j + 4 - 1 := by
        rw [hpcj, hpb]
        simp only [RL.pcOf]
        have : R.base + BitVec.ofNat 64 (lineOffset R.L j) + 4 - 1 - R.base =
            BitVec.ofNat 64 (lineOffset R.L j + 3) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
            show (4 : BitVec 64).toNat = 4 from rfl, show (1 : BitVec 64).toNat = 1 from rfl]
          have := R.base.isLt
          omega
        rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
      -- the frame invariant at `t`: the store of `t` and `SavedInv`
      have hFK' : FrameKeep R.FK u t :=
        ⟨hFK.1, fun a ha => hFK.2.1 a ⟨RL.FK_F ha, by rw [hst.sp]; exact RL.FK_not_below hR ha⟩, hFK.2.2⟩
      have hst' : StRel R.toRL t (fun l => match l with | .reg r => regVal t r | l => m l) w' :=
        stRel_after hR hst (fun r _ => rfl)
          (fun l hl => by cases l with | reg r => exact absurd rfl (hl r) | _ => rfl)
          hW herrt hprogt hFK'
      obtain ⟨hpre, hA, -, hB⟩ := hS2
      have hok : (regs.map Loc.reg).all (bodyWritable R.rf.saveRegs) = true :=
        savedCheckRF_body hrf hit _ (mem_bodyOf hsplit rfl _ List.mem_cons_self)
      rw [Array.all_eq_true'] at hok
      have hkeepT : ∀ r ∈ calleeSaved, r ∉ R.rf.saveRegs →
          ckeep r (regVal t r) = ckeep r (regVal u r) := by
        intro r hr hns
        by_cases hc : r ∈ (MInst.call info).clobbers
        · exact hkc r hc hr
        · rw [hoth r (calleeSaved_allocatable hr) (fun p hp _ e => ?_) hc]
          have hp2 : p.2 ∈ regs.toList := by
            rw [Array.toList_zip] at hp
            exact (List.of_mem_zip hp).2
          have hmemr : Loc.reg p.2 ∈ regs.map Loc.reg :=
            Array.mem_map.2 ⟨p.2, Array.mem_toList_iff.1 hp2, rfl⟩
          exact bodyWritable_ne_reg (hok _ hmemr) hr hns (by rw [e])
      have hls0 : RItem.leadSaves (RItem.op k (regs.map Loc.reg) :: its) = [] := rfl
      have hA' : ∀ r ∈ calleeSaved, r ∉ R.rf.saveRegs →
          ckeep r (regVal t r) = ckeep r (locVal R.fr (iterN R.step n0 R.s0) (.reg r)) := by
        intro r hr hns
        rw [hkeepT r hr hns, ← hm' r (calleeSaved_allocatable hr)]
        exact hA r hr hns
      have hinvT : SavedInv R.rf ckeep (fun r => locVal R.fr (iterN R.step n0 R.s0) (.reg r))
          (.run ⟨b, .op k (regs.map Loc.reg) :: its,
            (fun l => match l with | .reg r => regVal t r | l => m l), w'⟩ :
            MConf CV Arm.ArmState) :=
        ⟨hpre, hA', fun r hr => (by rw [hls0] at hr; cases hr), hB⟩
      have hfs : Unw.FrameSaved R.af R.s0 t := frameSaved_of_stRel hR hent hf hsaved he hst' hinvT
      obtain ⟨-, t', hrest, hretA, -, hmem'⟩ :=
        Unw.unwind_call_restores hrows hf (List.of_mem_zip hmem).2 hfs herrt
      have hstep : R.stepU u = Arm.w (.GPR 0#5) obj t' := by
        rw [hstepU]
        simp only [Unw.unwindAt, hoff, hpers, hcie, hfde, hrest]
      refine ⟨n0 + n1 + n2 + 1, ?_, ?_, ?_⟩
      all_goals rw [hfin, hu]
      all_goals simp only [iterN]
      all_goals rw [hstep]
      · rw [← hent.lr]
        exact Unw.armRet_x0 hretA obj
      · exact Arm.r_of_w_same
      · intro a ha
        rw [Arm.mem_w_of_mem_eq hmem']
        exact hW.2.1 a ha

/-! ## The activation of a compiled function -/

/-- **`regLevelCorrect_world_atX` with unwinding, generic in the semantics**: the core for the
activation of the allocated, lowered, emitted and laid-out function entered in `s`, with the
addresses `frameWG K … G s` outside the world and the calls through the GOT `gv`. `hRz`: the
machine with unwinding realises `semU` for that activation (`realizes_allU`). -/
theorem regLevelCorrect_world_atXU {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks} {XR : XRaise}
    {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat} {G : BitVec 64 → Prop}
    {gv : Nat → String → Prop} {base ra : BitVec 64} {s : Arm.ArmState}
    (hent : AbiCall fb base ra s) (hres : StackAvail K af s)
    (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a) {semU : Sem}
    (hgot : GotSem gv X semU)
    (hRz : ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) R.GoodXU)
    (hrets : ∀ us uses w, semU (.rets us) uses w =
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X i uses w = some (outs, w', .halt))
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    (hlsda : T.lsda = none ∨ ∃ sites, CallSitesOk af fa sites ∧ T.lsda = some (sites.map (·.entry)))
    (hlast : lastCallsOk af fa = true) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w, VReturns vcp semU (ρsel m₀) w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (Unw.ArmStepU X H U T fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (Unw.ArmStepU X H U T fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (Unw.ArmStepU X H U T fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (Unw.ArmStepU X H U T fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (Unw.ArmStepU X H U T fa) n s).mem a = s.mem a) ∧
        (E2E.runX (Unw.ArmStepU X H U T fa) n s).program = s.program) ∧
    (∀ c, VTraps vcp semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (Unw.ArmStepU X H U T fa) n s)) ∧
    RegLevelUnw semU XR
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      (Unw.ArmStepU X H U T fa) vcp ra s (ρsel m₀) w₀ := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  have hR : (⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ : RLU).Wf :=
    ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩,
      hent.program, hG⟩
  exact regLevelCorrect_coreU hR hent hcheck hU hgot (hRz lm psF _ rfl hR) hrets hhalt hlsda
    (siteAt_of_check hR hlast) hrows hcie hfde hsaved hbe ρsel hsel

/-- `regLevelCorrect_world_atXU` for an `AllocChecked` allocation, for one initial vreg file of
the theorem's choice (`entryRho`; `regLevelCorrect_world_ex`'s counterpart). -/
theorem regLevelCorrect_world_exU {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat} {G : BitVec 64 → Prop}
    {gv : Nat → String → Prop} {base ra : BitVec 64} {s : Arm.ArmState}
    (hent : AbiCall fb base ra s) (hres : StackAvail K af s)
    (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a) {semU : Sem}
    (hgot : GotSem gv X semU)
    (hRz : ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) R.GoodXU)
    (hrets : ∀ us uses w, semU (.rets us) uses w =
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X i uses w = some (outs, w', .halt))
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    (hlsda : T.lsda = none ∨ ∃ sites, CallSitesOk af fa sites ∧ T.lsda = some (sites.map (·.entry)))
    (hlast : lastCallsOk af fa = true) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) vcp.EntryArg af s w₀) :
    ∃ ρ₀ : Nat → CV,
    (∀ us vals w, VReturns vcp semU ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (Unw.ArmStepU X H U T fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (Unw.ArmStepU X H U T fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (Unw.ArmStepU X H U T fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (Unw.ArmStepU X H U T fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (Unw.ArmStepU X H U T fa) n s).mem a = s.mem a) ∧
        (E2E.runX (Unw.ArmStepU X H U T fa) n s).program = s.program) ∧
    (∀ c, VTraps vcp semU ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (Unw.ArmStepU X H U T fa) n s)) ∧
    RegLevelUnw semU XR
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      (Unw.ArmStepU X H U T fa) vcp ra s ρ₀ w₀ := by
  obtain ⟨cc, ins, a0, hat, hok⟩ := hcheck
  obtain ⟨_, h⟩ := regLevelCorrect_world_atXU hat hok halloc hemit hlayout hent hres hG hgot hRz
    hrets hhalt hU hlsda hlast hrows hcie hfde hsaved hbe (entryRho a0) (Inv_entryRho ckeep hok)
  exact ⟨_, h⟩

/-- `regLevelCorrect_world_atXU` for a `checkAlloc`-accepted allocation, for every initial vreg
file (`regLevelCorrect_world`'s counterpart). -/
theorem regLevelCorrect_worldU {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat} {G : BitVec 64 → Prop}
    {gv : Nat → String → Prop} {base ra : BitVec 64} {s : Arm.ArmState}
    (hent : AbiCall fb base ra s) (hres : StackAvail K af s)
    (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a) {semU : Sem}
    (hgot : GotSem gv X semU)
    (hRz : ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) R.GoodXU)
    (hrets : ∀ us uses w, semU (.rets us) uses w =
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X i uses w = some (outs, w', .halt))
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    (hlsda : T.lsda = none ∨ ∃ sites, CallSitesOk af fa sites ∧ T.lsda = some (sites.map (·.entry)))
    (hlast : lastCallsOk af fa = true) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w, VReturns vcp semU ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (Unw.ArmStepU X H U T fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (Unw.ArmStepU X H U T fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (Unw.ArmStepU X H U T fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (Unw.ArmStepU X H U T fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (Unw.ArmStepU X H U T fa) n s).mem a = s.mem a) ∧
        (E2E.runX (Unw.ArmStepU X H U T fa) n s).program = s.program) ∧
    (∀ c, VTraps vcp semU ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (Unw.ArmStepU X H U T fa) n s)) ∧
    RegLevelUnw semU XR
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      (Unw.ArmStepU X H U T fa) vcp ra s ρ₀ w₀ := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atXU hat (entryOk_of_le hle) halloc hemit hlayout hent
    hres hG hgot hRz hrets hhalt hU hlsda hlast hrows hcie hfde hsaved hbe (fun _ => ρ₀)
    (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-! ## The per-function layer (no kept addresses, no GOT pinning) -/

/-- **`RegLevelCorrectUEx` from a realisation of any semantics** `semOf` (`csemU`, or the
dead-cleanup value semantics with unwinding) agreeing with `csem` at the returns and traps. -/
theorem regLevelCorrect_backend_exU_of {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    {semOf : Arm.ArmState → Sem}
    (hRz : ∀ base s lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩,
        XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf (semOf s) ckeep R.stepU (QA R.toRL)
        R.GoodXU)
    (hrets : ∀ s us uses w, semOf s (.rets us) uses w =
      csem (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X (.rets us) uses w)
    (hhalt : ∀ s i uses w outs w', trapCode? i ≠ none →
      semOf s i uses w = some (outs, w', .halt) →
      csem (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X i uses w = some (outs, w', .halt))
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hlsda : T.lsda = none ∨ ∃ sites, CallSitesOk af fa sites ∧ T.lsda = some (sites.map (·.entry)))
    (hlast : lastCallsOk af fa = true) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) :
    RegLevelCorrectUEx semOf XR
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (Unw.ArmStepU X H U T fa) vcp af fb := by
  intro base ra s hent hres w₀ hbe
  have e := frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  obtain ⟨ρ₀, h1, h2, h3⟩ := regLevelCorrect_world_exU (G := fun _ => False)
    (gv := fun _ _ => False) hcheck halloc hemit hlayout hent.toCall hres (fun _ h => h.elim)
    (gotSem_bot X _)
    (hRz base s) (by rw [e]; exact hrets s) (by rw [e]; exact hhalt s) (by rw [e]; exact hU base s)
    hlsda hlast hrows hcie hfde hsaved
    (by rw [e]; exact hbe.w _ fun r ⟨_, _, hvb, hi, _, hv⟩ =>
      ((ctlCheck_args (lowerRFunc_ok halloc).2.2 hvb hi).2.2 _ hv).2)
  rw [e] at h1 h3
  exact ⟨ρ₀, fun us vals w hret => by
    obtain ⟨n, a1, a2, a3, -⟩ := h1 us vals w hret
    exact ⟨n, a1, a2, a3⟩, h2, h3⟩

/-- **`RegLevelCorrectU` from a realisation of any semantics** (`checkAlloc`, every initial vreg
file). -/
theorem regLevelCorrect_backendU_of {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    {semOf : Arm.ArmState → Sem}
    (hRz : ∀ base s lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩,
        XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf (semOf s) ckeep R.stepU (QA R.toRL)
        R.GoodXU)
    (hrets : ∀ s us uses w, semOf s (.rets us) uses w =
      csem (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X (.rets us) uses w)
    (hhalt : ∀ s i uses w outs w', trapCode? i ≠ none →
      semOf s i uses w = some (outs, w', .halt) →
      csem (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X i uses w = some (outs, w', .halt))
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hlsda : T.lsda = none ∨ ∃ sites, CallSitesOk af fa sites ∧ T.lsda = some (sites.map (·.entry)))
    (hlast : lastCallsOk af fa = true) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) :
    RegLevelCorrectU semOf XR
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (Unw.ArmStepU X H U T fa) vcp af fb := by
  intro base ra s hent hres w₀ hbe ρ₀
  have e := frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  obtain ⟨h1, h2, h3⟩ := regLevelCorrect_worldU (G := fun _ => False)
    (gv := fun _ _ => False) hcheck halloc hemit hlayout hent.toCall hres (fun _ h => h.elim)
    (gotSem_bot X _)
    (hRz base s) (by rw [e]; exact hrets s) (by rw [e]; exact hhalt s) (by rw [e]; exact hU base s)
    hlsda hlast hrows hcie hfde hsaved
    (by rw [e]; exact hbe.w _ fun r ⟨_, _, hvb, hi, _, hv⟩ =>
      ((ctlCheck_args (lowerRFunc_ok halloc).2.2 hvb hi).2.2 _ hv).2) ρ₀
  rw [e] at h1 h3
  exact ⟨fun us vals w hret => by
    obtain ⟨n, a1, a2, a3, -⟩ := h1 us vals w hret
    exact ⟨n, a1, a2, a3⟩, h2, h3⟩

/-! ## `csemU` -/

theorem noRaise_of_ne {XR : XRaise} {i : MInst} (hc : ∀ info, i ≠ .call info)
    (ht : ∀ info ti, i ≠ .tryCall info ti) (uses : List CV) (w : Arm.ArmState) :
    NoRaise XR i uses w := by
  intro info h
  rcases h with rfl | ⟨ti, rfl⟩
  · exact absurd rfl (hc info)
  · exact absurd rfl (ht info ti)

/-- At a trapping instruction `csemU` is `csem`. -/
theorem csemU_trap {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise} {i : MInst}
    (ht : trapCode? i ≠ none) (uses : List CV) (w : Arm.ArmState) :
    csemU F ctx X XR i uses w = csem F ctx X i uses w :=
  csemU_noRaise (noRaise_of_ne (fun info h => by subst h; simp [trapCode?] at ht)
    (fun info ti h => by subst h; simp [trapCode?] at ht) uses w)

/-- A function whose call-site table is empty (`callSites … = .ok none`) has no `try_call`
among its calls. -/
theorem callSites_none {af : AFunc} {fa : FnAsm} (h : callSites af fa = .ok none) :
    af.calls.any (·.isSome) = false := by
  cases hc : af.calls.any (·.isSome) with
  | false => rfl
  | true =>
    exfalso
    unfold callSites at h
    simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp [pure, Except.pure] at h

/-- The tables' LSDA is the emitted call-site table: none, or one `CallSitesOk` describes. -/
theorem lsda_cases {af : AFunc} {fa : FnAsm} {T : Unw.FnTables}
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) :
    T.lsda = none ∨ ∃ sites, CallSitesOk af fa sites ∧ T.lsda = some (sites.map (·.entry)) := by
  cases lsda with
  | none => exact .inl hlsda
  | some sites => exact .inr ⟨sites, callSites_ok hsites, hlsda⟩

/-- **The raising `tryCall` case of `realizes_allU` from the tables**: `realizes_tryCall_raiseU`
when the function has an LSDA (the emitted call-site table, `callSites`); vacuous when it has
none (no call of the function is a `try_call`, so the call-site bridge `SiteAt` excludes a
`tryCall` item). -/
theorem realizesTryRaise_of_tables {R : RLU} (hR : R.Wf) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hsemT : TryRaiseSem R.XR semU) (hgot : GotSem R.gv R.X semU) {lsda : Option (List CallSite)}
    (hsites : callSites R.af R.fa = .ok lsda) (hlsda : R.T.lsda = lsda.map (List.map (·.entry)))
    (hpad : PadsNonzero R.af R.fa) (hlast : lastCallsOk R.af R.fa = true) :
    RealizesTryRaise R semU := by
  cases lsda with
  | some sites =>
    exact realizes_tryCall_raiseU hR hU hsemT hgot ⟨sites, callSites_ok hsites, hlsda⟩ hpad
      (siteAt_of_check hR hlast)
  | none =>
    intro s b k allocs its m w vb info ti ops c' obj w' hq _ hvb hi
    obtain ⟨j, x, -, -, -, hmem⟩ := siteAt_of_check hR hlast s b k allocs its m w vb _ info
      (some ti) hq hvb hi (.inr ⟨ti, rfl, rfl⟩)
    have hn := callSites_none hsites
    have : (some ti : Option TryInfo) ∈ R.af.calls := (List.of_mem_zip hmem).1
    rw [List.any_eq_false] at hn
    exact ((hn _ this) rfl).elim

/-- **`realizesTryRaise_of_tables` with the raising-call states' step facts** (trace
`R.GoodXUF`, `realizes_tryCall_raiseUF`). -/
theorem realizesTryRaise_of_tablesF {R : RLU} (hR : R.Wf) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hsemT : TryRaiseSem R.XR semU) (hgot : GotSem R.gv R.X semU) {lsda : Option (List CallSite)}
    (hsites : callSites R.af R.fa = .ok lsda) (hlsda : R.T.lsda = lsda.map (List.map (·.entry)))
    (hpad : PadsNonzero R.af R.fa) (hlast : lastCallsOk R.af R.fa = true) :
    RealizesTryRaiseP R semU R.GoodXUF := by
  cases lsda with
  | some sites =>
    exact realizes_tryCall_raiseUF hR hU hsemT hgot ⟨sites, callSites_ok hsites, hlsda⟩ hpad
      (siteAt_of_check hR hlast)
  | none =>
    intro s b k allocs its m w vb info ti ops c' obj w' hq _ hvb hi
    obtain ⟨j, x, -, -, -, hmem⟩ := siteAt_of_check hR hlast s b k allocs its m w vb _ info
      (some ti) hq hvb hi (.inr ⟨ti, rfl, rfl⟩)
    have hn := callSites_none hsites
    have : (some ti : Option TryInfo) ∈ R.af.calls := (List.of_mem_zip hmem).1
    rw [List.any_eq_false] at hn
    exact ((hn _ this) rfl).elim

/-- The realisation of `csemU` for a compiled function's activation (no kept addresses, no GOT
pinning): `realizes_allU` from `realizes_all` and `realizes_tryCall_raiseU`. -/
theorem realizes_csemU {R : RLU} (hR : R.Wf)
    (hgv : R.gv = fun _ _ => False)
    (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hCT : R.vc.hasTryCall = true →
      CalleeTryOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H) (hcov : FormsCovered R.ctx R.vc)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    {lsda : Option (List CallSite)} (hsites : callSites R.af R.fa = .ok lsda)
    (hlsda : R.T.lsda = lsda.map (List.map (·.entry))) (hpad : PadsNonzero R.af R.fa)
    (hlast : lastCallsOk R.af R.fa = true) :
    Realizes R.vc R.rf (csemU R.F R.ctx R.X R.XR) ckeep R.stepU
      (QA R.toRL) R.GoodXU := by
  have hreal := realizes_all hR hC hCT hTls hcov
  refine realizes_allU hR hU hreal (fun i uses w h => ?_) (fun info uses w r obj w' h hr => ?_)
    (realizesTryRaise_of_tables hR hU (tryRaiseSem_csemU _ _ _ _)
      (by rw [hgv]; exact gotSem_bot _ _)
      hsites hlsda hpad hlast)
  · rw [csemU_noRaise h, RL.sem, hgv, csemV_bot]
  · rw [csemU_call_raise hr] at h
    cases h
    rfl

/-- `realizes_csemU` for every activation of the compiled function (no kept addresses, no GOT
pinning), from `regLevelCorrect_backend_ex`'s callee contracts and the raising callees'. -/
theorem realizes_csemU_backend {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true) :
    ∀ base s lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩,
        XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf
        (csemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
          ⟨fa.k, af.slotBase⟩ X XR) ckeep R.stepU
        (QA R.toRL) R.GoodXU := by
  intro base s lm psF R hReq hR
  subst hReq
  have hF : (⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩,
      XR, U, T⟩ : RLU).F =
      frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s :=
    frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  have h := realizes_csemU hR rfl (by rw [hF]; exact (hC s).g _ s _ _)
    (by rw [hF]; exact fun h => (hCT h s).g _ _ s _ _) (by rw [hF]; exact fun h => hTls h s)
    hcov (by rw [hF]; exact hU base s) hsites hlsda (padsNonzero_of_check hpad) hlast
  rw [hF] at h
  exact h

/-- `csemU` is `csem` at the returns. -/
theorem csemU_rets {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    (us : List (Reg × Reg)) (uses : List CV) (w : Arm.ArmState) :
    csemU F ctx X XR (.rets us) uses w = csem F ctx X (.rets us) uses w :=
  csemU_noRaise (noRaise_of_ne (fun _ h => by cases h) (fun _ _ h => by cases h) uses w)

/-- **`RegLevelCorrect` with unwinding for the backend's code** (`RegLevelCorrectUEx`, an
`AllocChecked` allocation): for the allocated, lowered, emitted and laid-out function, the
machine with unwinding `Unw.ArmStepU X H U T fa` realises every return, trap and exceptional end
of the prepared VCode under `csemU`, given `regLevelCorrect_backend_ex`'s premises, the raising
callees' contract `CalleeUnwOkG` of every activation, the emitted call-site table, the landing
pads at non-zero offsets and the call-site bridge (`padsNonzeroB`, `lastCallsOk`), the frame rows
the unwinder reads (`T.cie`, `T.fde` from `unwindRows`) and the frame-invariant check
`savedCheck`. -/
theorem regLevelCorrect_backend_exU {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) :
    RegLevelCorrectUEx
      (fun s => csemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X XR)
      XR (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (Unw.ArmStepU X H U T fa) vcp af fb :=
  regLevelCorrect_backend_exU_of hcheck halloc hemit hlayout
    (realizes_csemU_backend hcov hC hCT hTls hU hsites hlsda hpad hlast) (fun _ => csemU_rets)
    (fun _ _ _ _ _ _ ht h => by rwa [← csemU_trap ht]) hU (lsda_cases hsites hlsda) hlast
    hrows hcie hfde hsaved

/-- **`RegLevelCorrectU` for the backend's code** (a `checkAlloc`-accepted allocation, every
initial vreg file; `regLevelCorrect_backend`'s counterpart). -/
theorem regLevelCorrect_backendU {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) :
    RegLevelCorrectU
      (fun s => csemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X XR)
      XR (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (Unw.ArmStepU X H U T fa) vcp af fb :=
  regLevelCorrect_backendU_of hcheck halloc hemit hlayout
    (realizes_csemU_backend hcov hC hCT hTls hU hsites hlsda hpad hlast) (fun _ => csemU_rets)
    (fun _ _ _ _ _ _ ht h => by rwa [← csemU_trap ht]) hU (lsda_cases hsites hlsda) hlast
    hrows hcie hfde hsaved

/-! ## Non-vacuity -/

namespace RegLevelCorrectUWitness

/-- A function with a plain call: `args`, `call f`, `rets`. -/
def vc : VCode where
  name := "w"
  blocks := #[{ label := 0, insts := #[.args [], .call ⟨.sym "f", [], []⟩, .rets []] }]
  classes := #[]
  slotBytes := 0
  outgoing := 0
  rulesFired := #[]

/-- Its allocation (no operands, no callee-saves). -/
def rf : RFunc where
  blocks := #[#[.op 0 #[], .op 1 #[], .op 2 #[]]]
  spillSlots := 0
  saved := []

/-- Its lowering, final code and frame rows. -/
def af : AFunc := (lowerRFunc vc rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def rows : List (Nat × Cfi) := (unwindRows af fa).toOption.getD []

/-- The tables the unwinder reads for it: the emitted CIE and FDE rows, no LSDA (no
`try_call`). -/
def T : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rows, none⟩

theorem ok_getD {ε α : Type} [Inhabited α] {e : Except ε α} (h : e.toBool = true) :
    e = .ok (e.toOption.getD default) := by
  cases e <;> simp_all [Except.toBool, Except.toOption]

/-- **Non-vacuity of `regLevelCorrect_backend_exU`'s (and `regLevelCorrect_backendU`'s)
premises beyond `regLevelCorrect_backend_ex`'s**, on a compiled function with a call, for callees
that do not raise (`XRaise.none`, `Unw.UnwHooks.none`: the normal-return theorem's shape): the
allocation is accepted and lowered with a frame, the raising callees' contract holds, the
function has no LSDA and no `try_call`, the pad and call-site checks pass, the FDE rows are the
emitted ones, and the frame-invariant check passes. -/
theorem premises (K : Nat) (X : ExtSem) :
    checkAlloc vc rf = .ok () ∧ lowerRFunc vc rf = .ok af ∧ emitFunc 0 af = .ok fa ∧
      af.frame = true ∧ vc.CallSite ⟨.sym "f", [], []⟩ ∧ af.calls.length = 1 ∧
      (∀ base s, CalleeUnwOkG
        (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K
        (fun _ => False) s (CallAt fa base) X XRaise.none Unw.UnwHooks.none vc.CallSite
        (fun _ _ => False)) ∧
      callSites af fa = .ok none ∧ T.lsda = (none : Option (List CallSite)).map (List.map (·.entry)) ∧
      padsNonzeroB af fa = true ∧ lastCallsOk af fa = true ∧ unwindRows af fa = .ok rows ∧
      T.cie = cieInsns ∧ T.fde = insnsFrom 0 rows ∧ savedCheck vc rf = true := by
  have halloc : lowerRFunc vc rf = .ok af := ok_getD (by decide +kernel)
  have hc : savedCheck vc rf = true ∧ lastCallsOk af fa = true ∧ padsNonzeroB af fa = true ∧
      af.calls.any (·.isSome) = false ∧ af.calls.length = 1 := by decide +kernel
  have hcs : callSites af fa = .ok none := by
    unfold callSites
    simp [hc.2.2.2.1, pure, Except.pure]
  exact ⟨ok_getD (by decide +kernel), halloc, ok_getD (by decide +kernel),
    lowerRFunc_frame halloc, ⟨0, _, 1, rfl, .inl rfl⟩, hc.2.2.2.2,
    fun base s => calleeUnwOkG_none _ _ _ _ _ _ _ _, hcs, rfl, hc.2.2.1, hc.2.1,
    ok_getD (by decide +kernel), rfl, rfl, hc.1⟩

/-- `regLevelCorrect_backendU` applies to the witness function with `regLevelCorrect_backend`'s
premises only (its unwinding premises are `premises`). -/
theorem backendU_applies {X : ExtSem} {H : ArmHooks} {K : Nat} {fb : FnBin}
    (hlayout : fa.layout = .ok fb) (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vc)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K X H vc.CallSite)
    (hTls : vc.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K X H) :
    RegLevelCorrectU
      (fun s => csemU (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s)
        ⟨fa.k, af.slotBase⟩ X XRaise.none)
      XRaise.none (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af) K
      (Unw.ArmStepU X H Unw.UnwHooks.none T fa) vc af fb := by
  obtain ⟨hca, halloc, hemit, -, -, -, hU, hsites, hlsda, hpad, hlast, hrows, hcie, hfde,
    hsaved⟩ := premises K X
  have hnt : vc.hasTryCall = false := by decide +kernel
  exact regLevelCorrect_backendU hca halloc hemit hlayout hcov hC
    (fun h => absurd h (by rw [hnt]; decide)) hTls hU hsites hlsda hpad hlast hrows hcie hfde
    hsaved

end RegLevelCorrectUWitness

end Backend.Proof

import FV.E2E.RegLevelCorrectR

/-!
# M6 at the register-guarded value semantics: `valueSemVR` (#753, stage R3)

`DeadCleanupRealizes`'s `realizes_value_all`, `DeadCleanupRegLevel`'s
`regLevelCorrect_world_atX_value` and the world theorems of `DeadCleanupRegLevel{,X}` at the
register-guarded value semantics `regG P R.valueSem` (`valueSemVR P gv`, `LinkWorldR`) under the
callee contracts with the register guard; and **`regLevelR : RegLevelR`**, M6 for the
register-guarded semantics (the premise of stage R2's world theorems).

* `realizes_value_allR`: the machine realises the allocated code under `regG P R.valueSem`
  (`realizes_value_all`'s proof on `realizes_stepR`);
* `regLevelCorrect_world_atX_valueR`, `regLevelCorrect_world_valueR : RegLevelWorldValueR`,
  `regLevelCorrect_worldX_valueR : RegLevelWorldXValueR`;
* `regLevelR`: the four statements of `RegLevelR`.
-/

namespace Backend.Proof
open Backend E2E Backend.DeadCleanup

private theorem valueSemV_haltR {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {X : ExtSem} {i : MInst} {us outs : List CV}
    {w w' : Arm.ArmState} (h : valueSemV gv F ctx X i us w = some (outs, w', .halt)) :
    csemV gv F ctx X i us w = some (outs, w', .halt) := by
  by_cases hp : specForm i = true
  · have hs : mspec ctx.slotBase i us w = some (outs, w', .halt) := by
      simpa [valueSemV, hp] using h
    have := mspec_spec_next hp hs
    cases this
  · simpa [valueSemV, hp] using h

private theorem q_world_changeR {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem}
    {m : Loc → CV} {w w' : Arm.ArmState} (hq : Q R s (.run ⟨b, its, m, w⟩))
    (hw : SameWorld R.F w w') : Q R s (.run ⟨b, its, m, w'⟩) := by
  have hqs : ∀ {b its}, Qs R s b its m w → Qs R s b its m w' := by
    intro b its h
    obtain ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, hb, hi, hsplit, hc, hcode, hl1, hl2,
      htr, hdrop, hpc, hst, hx, hsc⟩ := h
    exact ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, hb, hi, hsplit, hc, hcode, hl1, hl2,
      htr, hdrop, hpc, { hst with world := hst.world.trans hw }, hx, hsc⟩
  have hqe : ∀ {b}, QE R s m w b → QE R s m w' b := by
    intro b h
    induction h with
    | std hit hq => exact .std hit (hqs hq)
    | fwd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ ih => exact .fwd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih
  rcases hq with h | ⟨items, hit, hits, h⟩
  · exact .inl (hqs h)
  · exact .inr ⟨items, hit, hits, hqe h⟩

private theorem aInv_step_semR {R : RL} {sem : Sem} (hR : R.Wf)
    {s : Arm.ArmState} {c c' : MConf CV Arm.ArmState}
    (hq : Q R s c) (hA : AInv R c) (h : MStep R.vc sem ckeep R.rf c c') : AInv R c' := by
  have hck := (hR.alloc.ok).2.2
  cases h with
  | @move b src dst its m w =>
    intro hb hop
    subst hb
    obtain ⟨items, pre, hit, hsplit⟩ := Q.split hq
    obtain ⟨hmv, hrd⟩ := ctlCheck_before hck hit hsplit hop
    have hA' := hA rfl (by obtain ⟨a, ha⟩ := hop; exact ⟨a, List.mem_cons_of_mem _ ha⟩)
    intro r hr
    have hne : Loc.reg r ≠ dst := by
      intro e; subst e; simp [RItem.regDst] at hrd
    rw [upd_other hne]
    exact hA' r hr
  | op _ _ _ _ _ _ _ _ hn =>
    cases hn with
    | next =>
      intro hb hop
      subst hb
      obtain ⟨items, pre, hit, hsplit⟩ := Q.split hq
      have := (ctlCheck_before hck hit hsplit hop).1
      simp [RItem.isMove] at this
    | goto _ hs _ =>
      intro hb
      exact absurd hb (ctlCheck_succ hck hs)
    | ret => trivial
    | halt => trivial

/-- A `Rets` step of the guarded value semantics ends the run. -/
private theorem rets_mstepVR {R : RL} {P : BitVec 64 → Clif.Signature → Prop} {b k : Nat}
    {a : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {c' : MConf CV Arm.ArmState} {vb : VBlock} {us : List (Reg × Reg)}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us))
    (h : MStep R.vc (regG P R.valueSem) ckeep R.rf (.run ⟨b, .op k a :: its, m, w⟩) c') :
    ∃ vals m' w', c' = .ret vals m' w' := by
  cases h with
  | op hvb' hi' hop hsz hs hl hho hcl hn =>
    rw [hvb] at hvb'; cases hvb'
    rw [hi] at hi'; cases hi'
    exact rets_mstep hvb hi (MStep.op hvb hi hop hsz
      (by simpa [RL.valueSem, valueSemV, RL.sem, specForm, pureForm, cmpForm] using regG_sub hs)
      hl hho hcl hn)

/-- **The machine realises the allocated code under the register-guarded value semantics**
(`realizes_value_all` at `regG P R.valueSem`, on `realizes_stepR`). -/
theorem realizes_value_allR {R : RL} (hR : R.Wf) {P : BitVec 64 → Clif.Signature → Prop}
    (hC : CalleeOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    Realizes R.vc R.rf (regG P R.valueSem) ckeep R.step (QA R) R.GoodX := by
  refine realizesQA hR (fun s c c' hq hA hm hns => ?_)
    (fun _ _ _ _ _ _ _ hq hs => realizes_move hR hq hs)
    (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepVR hvb hi h)
  have hreal := realizes_stepR hR hC hT hTls hcov
  have hno : ∀ {b k allocs its m w}, ∀ b' src dst its' m' w',
      (MConf.run ⟨b, .op k allocs :: its, m, w⟩ : MConf CV Arm.ArmState) =
        .run ⟨b', .move src dst :: its', m', w'⟩ → src.isSave = false :=
    fun _ _ _ _ _ _ e => by cases e
  cases hm with
  | move =>
    obtain ⟨n, c'', hstep, hq', ht⟩ := hreal s _ _ hq hA MStep.move hns
    cases hstep with
    | move => exact ⟨n, _, MStep.move, hq', ht⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hb hi hop hsz hsG hl hho hcl hn =>
    obtain ⟨hg, hs⟩ := regG_inv hsG
    by_cases hp : specForm i = true
    · have hspec : mspec R.ctx.slotBase i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', ctl) := by
        simpa [RL.valueSem, valueSemV, RL.sem, hp] using hs
      have hc := mspec_spec_next hp hspec
      subst ctl
      obtain ⟨wc, hconcrete, hworld⟩ := spec_mspec_csem (F := R.F) (X := R.X) hp hspec
      have hsem : R.sem i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, wc, .next) := by
        rw [R.sem_eq]
        · exact hconcrete
        · intro info he; subst i; simp [specForm, pureForm, cmpForm] at hp
        · intro info ti he; subst i; simp [specForm, pureForm, cmpForm] at hp
      have hsemG : regG P R.sem i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, wc, .next) := by
        rw [regG_of hg]; exact hsem
      cases hn with
      | next hk =>
        have hold : MStep R.vc (regG P R.sem) ckeep R.rf
            (.run ⟨b, .op k allocs :: its, m, w⟩)
            (.run ⟨b, its, writeM m2
              ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isLate)), wc⟩) :=
          MStep.op hb hi hop hsz hsemG hl hho hcl (MNext.next hk)
        obtain ⟨n, c'', hactual, ⟨hq', _⟩, ht⟩ := hreal s _ _ hq hA hold hno
        cases hactual with
        | @op _ _ _ _ _ _ vb' i' ops' os os' ww ct m3 cc hb' hi' hop' hsz' hsem' hl' hho' hcl' hn' =>
          rw [hb] at hb'; cases hb'
          rw [hi] at hi'; cases hi'
          rw [hop] at hop'; cases hop'
          rw [hsemG] at hsem'; cases hsem'
          cases hn' with
          | next hk' =>
            have hnew : MStep R.vc (regG P R.valueSem) ckeep R.rf
                (.run ⟨b, .op k allocs :: its, m, w⟩)
                (.run ⟨b, its, writeM m3
                  ((((ops.zip allocs).toList.filter (·.1.isDef)).zip os').filter (·.1.1.isLate)), w'⟩) :=
              MStep.op hb hi hop hsz hsG hl hho' hcl' (MNext.next hk')
            exact ⟨n, _, hnew, ⟨q_world_changeR hq' hworld, aInv_step_semR hR hq hA hnew⟩, ht⟩
    · have hsR : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
          some (outs, w', ctl) := by
        simpa [RL.valueSem, valueSemV, RL.sem, hp] using hs
      have hold : MStep R.vc (regG P R.sem) ckeep R.rf
          (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
        MStep.op hb hi hop hsz (by rw [regG_of hg]; exact hsR) hl hho hcl hn
      obtain ⟨n, c'', hactual, ⟨hq', _⟩, ht⟩ := hreal s _ _ hq hA hold hno
      cases hactual with
      | @op _ _ _ _ _ _ vb' i' ops' os os' ww ct m3 cc hb' hi' hop' hsz' hsem' hl' hho' hcl' hn' =>
        rw [hb] at hb'; cases hb'
        rw [hi] at hi'; cases hi'
        obtain ⟨hg', hs'⟩ := regG_inv hsem'
        have hsV : R.valueSem i (((ops'.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
            some (os, ww, ct) := by
          simpa [RL.valueSem, valueSemV, RL.sem, hp] using hs'
        have hnew : MStep R.vc (regG P R.valueSem) ckeep R.rf
            (.run ⟨b, .op k allocs :: its, m, w⟩) _ :=
          MStep.op hb hi hop' hsz' (by rw [regG_of hg']; exact hsV) hl' hho' hcl' hn'
        exact ⟨n, _, hnew, ⟨hq', aInv_step_semR hR hq hA hnew⟩, ht⟩

/-- **`regLevelCorrect_world_atX_value` at the register-guarded semantics** `valueSemVR P gv`
under the callee contracts with the register guard (`CalleeOkGR`, `CalleeTryOkGR`): the same
proof on `realizes_value_allR`. -/
theorem regLevelCorrect_world_atX_valueR {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0) (halloc : AllocAF vcp rf af)
    (hleaf : af.frame = false → fa.leafChk = true)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {P : BitVec 64 → Clif.Signature → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w, VReturns vcp (valueSemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ us vals w →
      ∃ n, (ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        (∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af))) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c, VTraps vcp (valueSemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨p, hp, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, p.ps, K, G, gv⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm, by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres,
    ⟨p, hp, rfl⟩, hent.program, hG, fun h => leafKeep_of_leafChk (hleaf h) hlm⟩
  have hck := (hR.alloc.ok).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_init hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf (regG P R.valueSem) ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
  have hRz := realizes_value_allR hR hC hCT hTls hcov
  -- the states of the run: `GoodX`, from the entry's run (`q_init`) and the realised items
  have hmk : ∀ (n1 n23 : Nat), (∀ i < n1 + n23, R.GoodX (iterN R.step i (iterN R.step n0 s))) →
      ∀ i < n0 + (n1 + n23), actGoodX vcp rf af fa fb base s X H K G gv
        (E2E.runX (ArmStepX X H fa) i s) := by
    intro n1 n23 hb i hi
    rw [runX_eq]
    exact (trace_add ht0 hb i hi).act
  refine ⟨locVal R.fr (iterN R.step n0 s), fun us vals w hret => ?_, fun c htr => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops
    cases hops
    have hsem' := regG_sub hsem
    simp only [valueSemV, specForm, pureForm, cmpForm, Bool.false_or, Bool.false_eq_true, ↓reduceIte, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, rfl, -⟩ := hsem'
    have h1 : VStep R.vc (regG P R.valueSem) (.run ⟨b, k, ρ, w₁⟩) (.ret vals w₁) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_ (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    have hfin : ∀ n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
        iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
      intro n3; rw [runX_eq]; simp only [iterN_add]; rfl
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
        have hsem3 := regG_sub hsem2
        simp only [RL.valueSem, valueSemV, specForm, pureForm, cmpForm, Bool.false_or, Bool.false_eq_true, ↓reduceIte, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, rfl, rfl⟩ := hsem3
        cases hn with
        | ret _ =>
        rw [rets_store hlen2 rfl hho hcl] at hks
        obtain ⟨mt, hq2'⟩ := qa_q hq2
        have hst := q_stRel hq2'
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hsaved, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machine hR hent hq2 hvb hi (RL.leafRegs3 hR ht0 ht1 ht2)
        -- every state of the run before the return is `GoodX`
        have htr : ∀ i < n0 + n1 + n2 + n3, R.GoodX (E2E.runX (ArmStepX X H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add ht0 (trace_add ht1 (trace_add ht2 ht3)) i (by omega)
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 s) (.reg r) = regVal (iterN R.step n0 s) r :=
          fun _ => rfl
        refine ⟨n0 + n1 + n2 + n3, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun i hi0 hi hpcall => ?_⟩,
          fun i hi => (htr i hi).act⟩
        rotate_right
        · exact (htr i hi).good.resolve_left (fun h => h hpcall)
        all_goals rw [hfin]
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
          · exact hsaved _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have hne : ∀ q, q < 32 → q ≠ 19 + a →
              Arm.StateField.GPR (rnum (19 + a)) ≠ .GPR (BitVec.ofNat 5 q) :=
            fun q h1 h2 e => rnum_ne (a := 19 + a) (b := q) (by omega) h1 (Ne.symm h2)
              (Arm.StateField.GPR.inj e)
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
            (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp)] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          by_cases hsv : Reg.v n ∈ R.af.saves
          · exact hsaved _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)] at k1
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) s).setWidth 64
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
        · intro f hf h29 h31
          rw [hfld f hf h29 h31]
          exact hst.world.1 f hf
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub (valueSemV_haltR (regG_sub hsem)))
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc (regG P R.valueSem) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    have hfin : ∀ n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
        iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
      intro n3; rw [runX_eq]; simp only [iterN_add]; rfl
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
          obtain ⟨htrap, hstuck⟩ := trap_udf hR hq2 hvb hi
          refine ⟨n0 + n1 + n2 + 0, by rw [hfin]; exact htrap,
            fun i hi => hmk n1 (n2 + 0)
              (trace_add ht1 (trace_add ht2 fun _ h => absurd h (Nat.not_lt_zero _))) i (by omega),
            fun m => ?_⟩
          rw [show n0 + n1 + n2 + 0 + m + 1 = n0 + n1 + n2 + (m + 1) by omega, hfin]
          exact hstuck m
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub (valueSemV_haltR (regG_sub hsem2)))
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, ht3, hstuck⟩ := trap_trapIf hR hq2 hvb hi hops' hholds
            refine ⟨n0 + n1 + n2 + n3, by rw [hfin]; exact htrap,
              fun i hi => hmk n1 (n2 + n3) (trace_add ht1 (trace_add ht2 ht3)) i (by omega),
              fun m => ?_⟩
            rw [show n0 + n1 + n2 + n3 + m + 1 = n0 + n1 + n2 + (n3 + m + 1) by omega, hfin]
            exact hstuck m

/-- **`regLevelCorrect_world_value` at the register-guarded semantics** (`RegLevelWorldValueR`,
one of the four statements of `RegLevelR`). -/
theorem regLevelCorrect_world_valueR : RegLevelWorldValueR := by
  intro vcp rf af fa fb k hcheck halloc hleaf hemit hlayout X H K G gv P hcov base ra s hent hres hG
    hC hCT hTls w₀ hbe ρ₀
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h1, h2⟩ := regLevelCorrect_world_atX_valueR hat (entryOk_of_le hle) halloc hleaf hemit
    hlayout hcov hent hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact ⟨fun us vals w hret => let ⟨n, h, _⟩ := h1 us vals w hret; ⟨n, h⟩,
    fun c htr => let ⟨n, h, _⟩ := h2 c htr; ⟨n, h⟩⟩

/-- **`regLevelCorrect_worldX_value` at the register-guarded semantics** (`RegLevelWorldXValueR`,
one of the four statements of `RegLevelR`). -/
theorem regLevelCorrect_worldX_valueR : RegLevelWorldXValueR := by
  intro vcp rf af fa fb k hcheck halloc hemit hlayout X H K G gv P hcov base ra s hent hres hG hC
    hCT hTls w₀ hbe ρ₀
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atX_valueR hat (entryOk_of_le hle)
    (AllocAF.of_lowerRFunc halloc) (noLeaf_of_lowerRFunc halloc) hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- **M6 for the register-guarded semantics** (#753, stage R3): the four statements of
`RegLevelR`, the premise `hM6` of stage R2's world theorems. -/
theorem regLevelR : RegLevelR :=
  ⟨regLevelCorrect_worldR, regLevelCorrect_worldXR, regLevelCorrect_world_valueR,
    regLevelCorrect_worldX_valueR⟩

end Backend.Proof

import FV.E2E.RegLevelCallR
import FV.E2E.RegLevelCorrectCY

/-!
# M6 at the register-guarded semantics: `csemVR` (#753, stage R3)

`RegLevelCorrect`'s `realizes_all`, `regLevelCorrect_world_atX` and `RegLevelCorrectX`'s
`regLevelCorrect_worldX` at the register-guarded semantics `regG P R.sem` (`csemVR P gv`) under the
callee contracts with the register guard (`CalleeOkGR P`, `CalleeTryOkGR P`):

* `regG_le`, `MStep.regG_sub`: the guarded semantics agrees with the base one where it is
  defined; its allocated-code steps are steps of the base semantics;
* `rets_mstepR`, `realizes_stepR`, `realizes_allR`: the machine realises the allocated code under
  `regG P R.sem` (the calls by `realizes_callR`/`realizes_tryCallR`, every other step by the
  lemma `realizes_step` uses on the base step, lifted back by `MStep.guardLift`);
* `regLevelCorrect_world_atXR`: `regLevelCorrect_world_atX` at `csemVR P gv` (the allocation
  simulation `checkedAt_sound` holds for every semantics);
* `regLevelCorrect_worldXR : RegLevelWorldXR`, `regLevelCorrect_worldR : RegLevelWorldR`: two of
  the four statements of `RegLevelR` (`LinkWorldR`).
-/

namespace Backend.Proof

open Backend E2E

section
variable {W : Type} {P : BitVec 64 → Clif.Signature → Prop} {sem : ISem CV W}

/-- The guarded semantics agrees with the base one wherever it is defined (`MStep.guardLift`'s
premise). -/
theorem regG_le : ∀ i us w r r', regG P sem i us w = some r → sem i us w = some r' →
    regG P sem i us w = some r' := by
  intro i us w r r' h h'
  rw [regG_of (regG_inv h).1]
  exact h'

/-- An allocated-code step of the guarded semantics is one of the base semantics. -/
theorem MStep.regG_sub {vc : VCode} {rf : RFunc} {keep : Reg → CV → CV} {c c' : MConf CV W}
    (h : MStep vc (regG P sem) keep rf c c') : MStep vc sem keep rf c c' := by
  cases h with
  | move => exact .move
  | op hvb hi hops hsz hsem hlen hho hcl hn =>
    exact .op hvb hi hops hsz (Backend.Proof.regG_sub hsem) hlen hho hcl hn

end

/-- A `Rets` step of the guarded semantics ends the run. -/
theorem rets_mstepR {R : RL} {P : BitVec 64 → Clif.Signature → Prop} {b k : Nat} {a : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState} {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us))
    (h : MStep R.vc (regG P R.sem) ckeep R.rf (.run ⟨b, .op k a :: its, m, w⟩) c') :
    ∃ vals m' w', c' = .ret vals m' w' :=
  rets_mstep hvb hi (MStep.regG_sub h)

/-- **`realizes_step` at the register-guarded semantics** `regG P R.sem` under the callee
contracts with the register guard: the calls by `realizes_callR`/`realizes_tryCallR`; every other
step is one of `R.sem`, realised by the lemma `realizes_step` uses, and lifted back
(`MStep.guardLift`). -/
theorem realizes_stepR {R : RL} (hR : R.Wf) {P : BitVec 64 → Clif.Signature → Prop}
    (hC : CalleeOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    ∀ s c c', Q R s c → AInv R c → MStep R.vc (regG P R.sem) ckeep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodX (iterN R.step i s) := by
  intro s c c' hq hA h hns
  have lift : ∀ c'', MStep R.vc R.sem ckeep R.rf c c'' → MStep R.vc (regG P R.sem) ckeep R.rf c c'' :=
    fun c'' h'' => MStep.guardLift h'' h regG_le
  have fin : ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodX (iterN R.step i s)) →
      ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodX (iterN R.step i s) :=
    fun n c'' hm hq' ht => ⟨n, c'', lift c'' hm, ⟨hq', aInv_step hR hq hA hm⟩, ht⟩
  have finG : ∀ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodX (iterN R.step i s)) →
      ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodX (iterN R.step i s) :=
    fun n c'' hm hq' ht => ⟨n, c'', hm, ⟨hq', aInv_step hR hq hA (MStep.regG_sub hm)⟩, ht⟩
  have nil : ∀ i < 0, R.GoodX (iterN R.step i s) := fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (hR.alloc.ok).2.2
  cases h with
  | move =>
    obtain ⟨n, hn, ht⟩ := realizes_move hR hq (hns _ _ _ _ _ _ rfl)
    exact fin n _ MStep.move hn ht
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsemG hlen hho hcl hn =>
    have hsem := regG_sub hsemG
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    cases hct : i.isCtl
    · rcases (hcov b vb k i hvb hi).resolve_left (by simp [hct]) with hfo | hpl
      rotate_left
      · -- the literal-pool load (#565)
        obtain ⟨sz, d, v, fl, rfl, -⟩ := isPoolLoad_form hpl
        obtain ⟨-, rfl⟩ := pool_world hsem
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_poolLoad hR hq hvb hi hpl hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht
      -- a covered straight-line form
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_op_next hR hq hvb hi hops hsz hsem hlen hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        exact fin n c'' hm hq' ht
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_callR hR hC hq hvb hi hops hsz hsemG hlen hk
          exact finG n c'' hm hq' ht
      case args ds => exact fin 0 c' hstep (realizes_args hR hq hA hvb hi hstep) nil
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact fin 0 _ hstep trivial nil
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddr hR hq hvb hi (.inl ⟨d, nm, rfl⟩) hops hsz
            hsem hlen hk
          exact fin n c'' hm hq' ht
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddr hR hq hvb hi (.inr ⟨d, nm, off, rfl⟩) hops
            hsz hsem hlen hk
          exact fin n c'' hm hq' ht
      case jump l =>
        obtain ⟨n, hq', ht⟩ := realizes_goto hR hq hvb hi (.inl ⟨l, rfl⟩) hstep
        exact fin n c' hstep hq' ht
      case condBr t e kk =>
        obtain ⟨n, hq', ht⟩ := realizes_goto hR hq hvb hi (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact fin n c' hstep hq' ht
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht⟩ := realizes_goto hR hq hvb hi (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact fin n c' hstep hq' ht
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact fin 0 _ hstep trivial nil
        · obtain ⟨n, hq', ht⟩ := realizes_trapIf_next hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact fin n c' hstep hq' ht
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact fin 0 _ hstep trivial nil
      case emitIsland nb => exact fin 0 c' hstep (realizes_island hR hq hvb hi hstep) nil
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_jt hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_rmwLoop hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_casLoop hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tryCallR hR hC (hT (hasTryCall_of_mem hvb hi)) hq hvb
            hi hops hsz hsemG hlen hk1 hsucc hitems rfl
          exact finG n c'' hm hq' ht
      case elfTlsGetAddr nm rd tmp =>
        have hv := ctlCheck_inst hck hvb hi
        simp only [ctlInstOk, Bool.and_eq_true] at hv
        obtain ⟨d, rfl⟩ := isVregInt_iff hv.1
        obtain ⟨t, rfl⟩ := isVregInt_iff hv.2
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tls hR (hTls (hasTls_of_mem hvb hi)) hq hvb hi
            hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht

/-- **The machine realises the allocated code under the register-guarded semantics**
(`realizes_all` at `regG P R.sem` under `CalleeOkGR`, `CalleeTryOkGR`). -/
theorem realizes_allR {R : RL} (hR : R.Wf) {P : BitVec 64 → Clif.Signature → Prop}
    (hC : CalleeOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    Realizes R.vc R.rf (regG P R.sem) ckeep R.step (QA R) R.GoodX :=
  realizesQA hR (realizes_stepR hR hC hT hTls hcov)
    (fun _ _ _ _ _ _ _ hq hs => realizes_move hR hq hs)
    (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepR hvb hi h)

/-- **`regLevelCorrect_world_atX` at the register-guarded semantics** `csemVR P gv` under the
callee contracts with the register guard (`CalleeOkGR`, `CalleeTryOkGR`): the same proof on
`realizes_allR` (the allocation simulation `checkedAt_sound` holds for every semantics). -/
theorem regLevelCorrect_world_atXR {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0) (halloc : lowerRFunc vcp rf = .ok af)
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
    (∀ us vals w, VReturns vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ us vals w →
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
    (∀ c, VTraps vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨p, hp, hL, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, p.ps, K, G, gv⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hcheck, hok⟩, AllocAF.of_lowerRFunc halloc, hemit, hlayout, hlm, by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres,
    ⟨p, hp, rfl⟩, hent.program, hG, noLeaf_of_lowerRFunc halloc⟩
  have hck := (hR.alloc.ok).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_init hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf (regG P R.sem) ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
  have hRz := realizes_allR hR hC hCT hTls hcov
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
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, rfl, -⟩ := hsem'
    have h1 : VStep R.vc (regG P R.sem) (.run ⟨b, k, ρ, w₁⟩) (.ret vals w₁) := by
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
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
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
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub (regG_sub hsem))
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc (regG P R.sem) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
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
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub (regG_sub hsem2))
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

/-- **`regLevelCorrect_worldX` at the register-guarded semantics** (`RegLevelWorldXR`, one of the
four statements of `RegLevelR`). -/
theorem regLevelCorrect_worldXR : RegLevelWorldXR := by
  intro vcp rf af fa fb k hcheck halloc hemit hlayout X H K G gv P hcov base ra s hent hres hG hC
    hCT hTls w₀ hbe ρ₀
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atXR hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- **`regLevelCorrect_world` at the register-guarded semantics** (`RegLevelWorldR`, one of the
four statements of `RegLevelR`): `regLevelCorrect_worldXR` without the per-state facts. -/
theorem regLevelCorrect_worldR : RegLevelWorldR := by
  intro vcp rf af fa fb k hcheck halloc hemit hlayout X H K G gv P hcov base ra s hent hres hG hC
    hCT hTls w₀ hbe ρ₀
  obtain ⟨h1, h2⟩ := regLevelCorrect_worldXR hcheck halloc hemit hlayout hcov hent hres hG hC hCT
    hTls hbe ρ₀
  exact ⟨fun us vals w hret => let ⟨n, h, _⟩ := h1 us vals w hret; ⟨n, h⟩,
    fun c htr => let ⟨n, h, _⟩ := h2 c htr; ⟨n, h⟩⟩

end Backend.Proof

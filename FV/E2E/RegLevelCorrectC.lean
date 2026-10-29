import FV.E2E.RegLevelCountP
import FV.E2E.RegLevelMoveN
import FV.E2E.RegLevelOpN
import FV.E2E.RegLevelNextN
import FV.E2E.RegLevelCallN
import FV.E2E.RegLevelTryN
import FV.E2E.RegLevelJTN
import FV.E2E.RegLevelAtomicN
import FV.E2E.RegLevelTlsN
import FV.E2E.RegLevelFrameN
import FV.E2E.RegLevelPoolN

/-!
# The counted register-level theorem with the call contract of index `n` at call `n` only
(SEM1 #537, step 2k, docs/plans/uninit.md §5.5)

* `realizes_allC`: `realizes_all` counting the call states (`RL.CallSt`) of each realised
  segment (`RealizesCP`: `opCalls` of them), the callee contracts needed only at the states `P`
  (`CalleeOkGP`, `CalleeTryOkGP`);
* `regLevelCorrect_world_atC`, `regLevelCorrect_worldC`: `regLevelCorrect_world_atI`/`_worldI`
  with the contract of index `n` required only at the states of the activation's own run with
  `n` call states before them (`OnCall`, `callsBefore`): the counted VCode run's counter is the
  machine's call count (`RealizesCP.countedRun` on `stepC`).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- **`realizesQA` counting the call states**: `RealizesCP` under `QA` from the realisation
under `Q ∧ AInv` of every step but a callee restore, the realisation of the moves (no restore)
under `Q` with no call state, and the `Rets` steps' ending the run. The restores take no machine
step (`q_restore`); the moves of a return tail are realised on the machine's store. -/
theorem realizesQA_CP {R : RL} (hR : R.Wf) {sem : ISem CV Arm.ArmState} {keep : Reg → CV → CV}
    {T C P : Arm.ArmState → Prop}
    (hstep : ∀ s c c', Q R s c → AInv R c → P s → MStep R.vc sem keep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc sem keep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, T (iterN R.step i s)) ∧ countIn C R.step s n = opCalls R.vc c)
    (hmove : ∀ s b src dst its m w, Q R s (.run ⟨b, .move src dst :: its, m, w⟩) →
      src.isSave = false → ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, upd m dst (m src), w⟩) ∧
        (∀ i < n, T (iterN R.step i s)) ∧ countIn C R.step s n = 0)
    (hrets : ∀ b k a its m w c' vb us, R.vc.blocks[b]? = some vb → vb.insts[k]? = some (.rets us) →
      MStep R.vc sem keep R.rf (.run ⟨b, .op k a :: its, m, w⟩) c' → ∃ vals m' w', c' = .ret vals m' w') :
    RealizesCP R.vc R.rf sem keep R.step (QA R) T C P := by
  intro s c c' hqa hP hm
  have nil : ∀ i < 0, T (iterN R.step i s) := fun _ h => absurd h (Nat.not_lt_zero _)
  rcases hqa with ⟨hq, hA⟩ | hrt
  · by_cases hres : ∃ b r dst its m w, c = .run ⟨b, .move (.save r) dst :: its, m, w⟩
    · obtain ⟨b, r, dst, its, m, w, rfl⟩ := hres
      obtain ⟨rfl, D, htl⟩ := restore_tail hR hq
      cases hm
      refine ⟨0, _, .move, .inr ?_, nil, rfl⟩
      simp only [RetTail]
      refine ⟨m, D ++ [r], q_restore rfl hq, fun l hl => ?_, htl⟩
      simp only [upd, hl r (by simp), ite_false]
    · obtain ⟨n, c'', hm', hq', ht, hc⟩ := hstep s c c' hq hA hP hm fun b src dst its m w e => by
        cases src with
        | save r => exact absurd ⟨b, r, dst, its, m, w, e⟩ hres
        | _ => rfl
      exact ⟨n, c'', hm', .inl hq', ht, hc⟩
  · rcases c with ⟨b, its, m, w⟩ | ⟨vals, m, w⟩ | w
    · simp only [RetTail] at hrt
      obtain ⟨mt, D, hq, hmD, vb, pend, k, a, rest, us, hvb, rfl, hk, htl⟩ := hrt
      rcases pend with _ | ⟨it, pend⟩
      · obtain ⟨vals, m', w', rfl⟩ := hrets b k a rest m w c' vb us hvb hk hm
        exact ⟨0, _, hm, .inl ⟨trivial, trivial⟩, nil,
          by simp [opCalls, hvb, hk, MInst.isCallI, countIn]⟩
      · simp only [List.cons_append] at hm hq
        unfold retTailOk at htl
        split at htl
        · rename_i r hr1 hr2
          simp only [Bool.and_eq_true] at htl
          obtain rfl := RItem.eq_restore hr1 hr2
          cases hm
          refine ⟨0, _, .move, .inr ?_, nil, rfl⟩
          simp only [RetTail]
          refine ⟨mt, D ++ [r], q_restore rfl hq, fun l hl => ?_, vb, pend, k, a, rest, us, hvb, rfl,
            hk, htl.2⟩
          simp only [upd, hl r (by simp), ite_false]
          exact hmD l (fun r' hr' => hl r' (List.mem_append_left _ hr'))
        · simp only [Bool.and_eq_true] at htl
          obtain ⟨hav, htl⟩ := htl
          cases it with
          | op _ _ => simp [RItem.avoids] at hav
          | move x y =>
            simp only [RItem.avoids, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
              Bool.or_eq_true, beq_iff_eq, not_or] at hav
            obtain ⟨⟨hx, -⟩, hD⟩ := hav
            cases hm
            obtain ⟨n, hq', ht, hc⟩ := hmove s b x y _ mt w hq hx
            refine ⟨n, _, .move, .inr ?_, ht, by rw [hc]; rfl⟩
            simp only [RetTail]
            refine ⟨upd mt y (mt x), D, hq', fun l hl => ?_, vb, pend, k, a, rest, us, hvb, rfl, hk, htl⟩
            by_cases hly : l = y
            · simp only [upd, hly, ite_true]
              exact hmD x (fun r hr e => (hD r hr).1 e)
            · simp only [upd, hly, ite_false]
              exact hmD l hl
    · simp only [RetTail] at hrt
    · simp only [RetTail] at hrt

/-- **One step of the allocated code from `Q ∧ AInv`** that is not a restore move, from the
states `P`, counting its call states (`realizes_allC`'s non-restore case). -/
theorem realizes_stepC {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    ∀ s c c', Q R s c → AInv R c → P s → MStep R.vc R.sem ckeep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s)) ∧ countIn R.CallSt R.step s n = opCalls R.vc c := by
  intro s c c' hq hA hP h hns
  have fin1 : ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodX (iterN R.step i s)) → countIn R.CallSt R.step s n = opCalls R.vc c →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s)) ∧ countIn R.CallSt R.step s n = opCalls R.vc c :=
    fun n c'' hm hq' ht hc => ⟨n, c'', hm, ⟨hq', aInv_step hR hq hA hm⟩, ht, hc⟩
  have fin : ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodXN (iterN R.step i s)) → opCalls R.vc c = 0 →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s)) ∧ countIn R.CallSt R.step s n = opCalls R.vc c :=
    fun n c'' hm hq' ht h0 => fin1 n c'' hm hq' (fun i hi => (ht i hi).1)
      (by rw [h0]; exact countIn_zero_of fun i hi => (ht i hi).2)
  have nil : ∀ i < 0, R.GoodXN (iterN R.step i s) := fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases h with
  | move =>
    obtain ⟨n, hn, ht⟩ := realizes_moveN hR hq (hns _ _ _ _ _ _ rfl)
    exact fin n _ MStep.move hn ht rfl
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hoc : opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = if i.isCallI then 1 else 0 := by
      simp only [opCalls, hvb, hi]
    have hoc0 : i.isCallI = false → opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = 0 :=
      fun h => by rw [hoc, h]; rfl
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
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_poolLoadN hR hq hvb hi hpl hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht (hoc0 rfl)
      -- a covered straight-line form
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_op_nextN hR hq hvb hi hops hsz hsem hlen hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        exact fin n c'' hm hq' ht (hoc0 (by cases i <;> first | rfl | simp [MInst.isCtl] at hct))
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, i0, hi0, hc0, hnc⟩ := realizes_callN hR hC hP hq hvb hi hops hsz
            hsem hlen hk
          exact fin1 n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
      case args ds => exact fin 0 c' hstep (realizes_args hR hq hA hvb hi hstep) nil (hoc0 rfl)
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact fin 0 _ hstep trivial nil (hoc0 rfl)
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrN hR hq hvb hi (.inl ⟨d, nm, rfl⟩) hops hsz
            hsem hlen hk
          exact fin n c'' hm hq' ht (hoc0 rfl)
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrN hR hq hvb hi (.inr ⟨d, nm, off, rfl⟩) hops
            hsz hsem hlen hk
          exact fin n c'' hm hq' ht (hoc0 rfl)
      case jump l =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoN hR hq hvb hi (.inl ⟨l, rfl⟩) hstep
        exact fin n c' hstep hq' ht (hoc0 rfl)
      case condBr t e kk =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoN hR hq hvb hi (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact fin n c' hstep hq' ht (hoc0 rfl)
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoN hR hq hvb hi (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact fin n c' hstep hq' ht (hoc0 rfl)
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact fin 0 _ hstep trivial nil (hoc0 rfl)
        · obtain ⟨n, hq', ht⟩ := realizes_trapIf_nextN hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact fin n c' hstep hq' ht (hoc0 rfl)
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact fin 0 _ hstep trivial nil (hoc0 rfl)
      case emitIsland nb => exact fin 0 c' hstep (realizes_island hq hvb hi hstep) nil (hoc0 rfl)
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_jtN hR hq hvb hi hstep
        exact fin n c'' hm hq' ht (hoc0 rfl)
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_rmwLoopN hR hq hvb hi hstep
        exact fin n c'' hm hq' ht (hoc0 rfl)
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_casLoopN hR hq hvb hi hstep
        exact fin n c'' hm hq' ht (hoc0 rfl)
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht, i0, hi0, hc0, hnc⟩ := realizes_tryCallN hR hC
            (hT (hasTryCall_of_mem hvb hi)) hP hq hvb hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin1 n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
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
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tlsN hR (hTls (hasTls_of_mem hvb hi)) hq hvb hi
            hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht (hoc0 rfl)

/-- **The machine realises the allocated code** under `QA` from the states `P`, each segment
passing `opCalls` call states, the callee contracts needed at the states `P` only. -/
theorem realizes_allC {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    RealizesCP R.vc R.rf R.sem ckeep R.step (QA R) R.GoodX R.CallSt P :=
  realizesQA_CP hR (realizes_stepC hR hC hT hTls hcov)
    (fun _ _ _ _ _ _ _ hq hs => let ⟨n, h1, h2⟩ := realizes_moveN hR hq hs
      ⟨n, h1, fun i hi => (h2 i hi).1, countIn_zero_of fun i hi => (h2 i hi).2⟩)
    (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstep hvb hi h)

/-- **`regLevelCorrect_world_atI` with the contract of call `n` at call `n` only**: the callee
contracts of index `n` (`CalleeOkGP`, `CalleeTryOkGP`) are needed only at the states of the
activation's own run from `s` with `n` call states before them (`OnCall`). -/
theorem regLevelCorrect_world_atC {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkGP (OnCall (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (OnCall (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w nc, VRetFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρsel m₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XI.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_initN hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf (csemVI R.gv R.F R.ctx XI) ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) (w₀, 0) (hsel _)
  have hP0 : countIn R.CallSt R.step s n0 = 0 := countIn_zero_of fun i hi => (ht0 i hi).2
  have hRz := Realizes.ofStepC (vc := R.vc) (rf := R.rf) (keep := ckeep) (C := R.CallSt) (T := R.Good)
    (Q := fun p c => QA R p.1 (c.mapW Prod.fst) ∧ p.2 = c.world.2 ∧
      ∃ i, p = iterN (stepC R.CallSt R.step) i (iterN R.step n0 s, 0)) (by
    refine RealizesCP.countedRun (vc := R.vc) (rf := R.rf) (keep := ckeep)
      (sem := fun n => csemV R.gv R.F R.ctx (XI.at n))
      (Q := fun u c => QA R u c) (T := R.Good) (C := R.CallSt)
      (P := fun n u => OnCall R.step fa base s n u) (s0 := iterN R.step n0 s) (fun n => ?_)
      (onCall_of_run hP0)
    have hq : ∀ u c, QA (Rn n) u c ↔ QA R u c := fun u c =>
      (RL.QA_withX (Rn n) (XI.at 0) (RL.sP_withX (hRn n) hent (XI.at 0)) u c).symm
    exact ((realizes_allC (hRn n) (hC n) (fun h => hCT h n) (fun h => hTls h n) hcov).mono_T
      (T' := R.Good) fun _ h => h.good).congr_Q hq)
  have hfin0 : ∀ n1 n2 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun us vals w nc hret => ?_, fun c htr => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨n1, c1, hz1, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨0, .inl ⟨hq0, hA0⟩, rfl, 0, rfl⟩
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops
    cases hops
    obtain ⟨hsemV, -⟩ := ISem.counted_some hsem
    have hsem' := hsemV
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, hw, -⟩ := hsem'
    have h1 : VStep R.vc (csemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w₁⟩) (.ret vals (w, nc)) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_ (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    obtain ⟨n2, c', c'', ⟨_, hq2, -⟩, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hz1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      have hks := hkeep hr3
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        dsimp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [operands_retsC] at hops'; cases hops'
        cases hn with
        | ret _ =>
        obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
        simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, -, -⟩ := hsem3
        rw [rets_store hlen2 rfl hho hcl] at hks
        have hq2' : QA R (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s)))
            (.run ⟨b, .op k _ :: _, _, w₁.1⟩) := hq2
        obtain ⟨mt, hq2''⟩ := qa_q hq2'
        have hst := q_stRel hq2''
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hsvd, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machine hR hent hq2' hvb hi
        have htr : ∀ i < n0 + n1 + n2 + n3, R.Good (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add (fun j hj => (ht0 j hj).1.good)
            (trace_add ht1 (trace_add ht2 fun j hj => (ht3 j hj).good)) i (by omega)
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 s) (.reg r) = regVal (iterN R.step n0 s) r :=
          fun _ => rfl
        refine ⟨n0 + n1 + n2 + n3, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun i hi0 hi hpcall => ?_⟩
        rotate_right
        · exact (htr i hi).resolve_left (fun h => h hpcall)
        all_goals rw [hfin0]
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
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) s).setWidth 64
          rw [k2]
          exact setWidth128_inj k1
        · intro j v p x hj hx
          have e1 := hSim.ret hr3
          simp only [VConf.ret.injEq] at e1
          rw [e1.1] at hx
          exact hvalsM _ (operands_retsC ns) j v p x hj hx
        · intro a ha
          rw [hmem, ← hw]
          exact hst.world.2.1 a ha
        · intro f hf h29 h31
          rw [hfld f hf h29 h31, ← hw]
          exact hst.world.1 f hf
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hz1, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨0, .inl ⟨hq0, hA0⟩, rfl, 0, rfl⟩
    obtain ⟨hsemV, -⟩ := ISem.counted_some hsem
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub hsemV)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc (csemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', ⟨_, hq2, -⟩, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hz1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        dsimp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hq2'' : QA R (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s)))
            (.run ⟨b, .op k _ :: _, _, w.1⟩) := hq2
        have hnr : ∀ us, i ≠ .rets us := by
          intro us h
          rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
        have hq2' := (qa_op hq2'' hvb hi hnr).1
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, hholds⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, -⟩ := trap_udf hR hq2' hvb hi
          exact ⟨n0 + n1 + n2 + 0, by rw [hfin0]; exact htrap⟩
        · cases hn with
          | halt =>
          obtain ⟨hsem3, -⟩ := ISem.counted_some hsem2
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub hsem3)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds'⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, -, -⟩ := trap_trapIf hR hq2' hvb hi hops' hholds'
            exact ⟨n0 + n1 + n2 + n3, by rw [hfin0]; exact htrap⟩

/-- **`regLevelCorrect_worldI` with the contract of call `n` at call `n` only** (`OnCall`). -/
theorem regLevelCorrect_worldC {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkGP (OnCall (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (OnCall (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w nc, VRetFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atC hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof

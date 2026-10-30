import FV.E2E.RegLevelCorrect
import FV.E2E.RegLevelOpWrites
import FV.E2E.RegLevelOpW
import FV.E2E.RegLevelAtomicW
import FV.E2E.RegLevelCallW
import FV.E2E.RegLevelGotoW
import FV.E2E.RegLevelNextW
import FV.E2E.RegLevelJTW
import FV.E2E.RegLevelTryW
import FV.E2E.RegLevelTlsW

/-!
# The machine realises the allocated code, with the writes (A3, #412, slice F8b)

`realizes_allW`: `realizes_all` with `RL.GoodXW` (every state of the run with `GoodX` and the
writes `RL.WritesAt`), from the W versions of the item cases.
-/

namespace Backend.Proof

open Backend E2E

/-- **One step of the allocated code from `Q ∧ AInv`** that is not a restore move, with the
writes (`realizes_step` with `RL.GoodXW`). -/
theorem realizes_stepW {R : RL} (hR : R.Wf) (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → CalleeTryOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    ∀ s c c', Q R s c → AInv R c → MStep R.vc R.sem ckeep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodXW (iterN R.step i s) := by
  intro s c c' hq hA h hns
  have fin : ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodXW (iterN R.step i s)) →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodXW (iterN R.step i s) :=
    fun n c'' hm hq' ht => ⟨n, c'', hm, ⟨hq', aInv_step hR hq hA hm⟩, ht⟩
  have nil : ∀ i < 0, R.GoodXW (iterN R.step i s) := fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases h with
  | move =>
    obtain ⟨n, hn, ht⟩ := realizes_moveW hR hq (hns _ _ _ _ _ _ rfl)
    exact fin n _ MStep.move hn ht
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    cases hct : i.isCtl
    · -- a covered straight-line form
      have hfo := (hcov b vb k i hvb hi).resolve_left (by simp [hct])
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_op_nextW hR hq hvb hi hops hsz hsem hlen hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (fun ha hasg hl hw he hal hs env => formOk_writes hfo hops ha hasg hl hw he hal hs env)
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
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_callW hR hC hq hvb hi hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht
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
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrW hR hq hvb hi (.inl ⟨d, nm, rfl⟩) hops hsz
            hsem hlen hk
          exact fin n c'' hm hq' ht
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrW hR hq hvb hi (.inr ⟨d, nm, off, rfl⟩) hops
            hsz hsem hlen hk
          exact fin n c'' hm hq' ht
      case jump l =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoW hR hq hvb hi (.inl ⟨l, rfl⟩) hstep
        exact fin n c' hstep hq' ht
      case condBr t e kk =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoW hR hq hvb hi (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact fin n c' hstep hq' ht
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoW hR hq hvb hi (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact fin n c' hstep hq' ht
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact fin 0 _ hstep trivial nil
        · obtain ⟨n, hq', ht⟩ := realizes_trapIf_nextW hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact fin n c' hstep hq' ht
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact fin 0 _ hstep trivial nil
      case emitIsland nb => exact fin 0 c' hstep (realizes_island hq hvb hi hstep) nil
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_jtW hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_rmwLoopW hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_casLoopW hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tryCallW hR hC (hT (hasTryCall_of_mem hvb hi)) hq hvb
            hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin n c'' hm hq' ht
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
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tlsW hR (hTls (hasTls_of_mem hvb hi)) hq hvb hi
            hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht

/-- **The machine realises the allocated code with the writes** (`realizes_all` with
`RL.GoodXW`), under `QA`. -/
theorem realizes_allW {R : RL} (hR : R.Wf) (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → CalleeTryOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    Realizes R.vc R.rf R.sem ckeep R.step (QA R) R.GoodXW :=
  realizesQA hR (realizes_stepW hR hC hT hTls hcov)
    (fun _ _ _ _ _ _ _ hq hs => realizes_moveW hR hq hs)
    (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstep hvb hi h)

end Backend.Proof

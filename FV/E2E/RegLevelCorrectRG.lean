import FV.E2E.RegLevelCallRG

/-!
# M6 at `csemVR` with the guarded per-state facts (#753, stage R3')

`RegLevelCorrectR` with the per-state facts `RL.GoodXR P` / `actGoodXR P` (`RegLevelGoodXRG`): at a
call line the callee contract's premise holds with the guarded step.

* `q_initG`, `ret_machineG`, `trap_trapIfG`: the prologue's, the epilogue's and a trap's states at
  `R.noCall` (at no call line);
* `realizes_stepRG`, `realizes_allRG`: the calls by `realizes_callRG`/`realizes_tryCallRG`, every
  other step realised at `R.noCall` and lifted back (`MStep.guardLift`, `RL.noCall_le`);
* `regLevelCorrect_world_atXRG`, `RegLevelWorldXRG`, `regLevelCorrect_worldXRG`.
-/

namespace Backend.Proof

open Backend E2E

set_option autoImplicit false

/-- `q_init` with the prologue's states at `R.noCall` (at no call line). -/
theorem q_initG {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, (∀ i < n, R.noCall.GoodX (iterN R.step i R.s0)) ∧
      Q R (iterN R.step n R.s0) (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      AInv R (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 →
        (∀ fl, f ≠ .FLAG fl) → Arm.r f (iterN R.step n R.s0) = Arm.r f R.s0 := by
  obtain ⟨n, h1, h2, h3, h4⟩ := q_init hR.noCall hent hbe
  exact ⟨n, h1, h2.ofNoCall, h3, h4⟩

/-- `ret_machine` with the epilogue's states at `R.noCall` (at no call line). -/
theorem ret_machineG {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hqa : QA R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us))
    (hlr : R.af.frame = false → xreg 29 s = xreg 29 R.s0 ∧ xreg 30 s = xreg 30 R.s0) :
    ∃ n, (∀ i < n, R.noCall.GoodX (iterN R.step i s)) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0 ∧
      (∀ r, r.allocatable = true → r ∉ R.af.saves → regVal (iterN R.step n s) r = m (.reg r)) ∧
      (∀ r ∈ R.af.saves, slotVal (iterN R.step n s) r = slotVal R.s0 r) ∧
      (iterN R.step n s).mem = s.mem ∧
      (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f (iterN R.step n s) = Arm.r f s) ∧
      (iterN R.step n s).program = s.program ∧
      ∀ ops, (MInst.rets us).operands = .ok ops → ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) →
        ((((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)))[j]? = some x →
        regVal (iterN R.step n s) p = x := by
  obtain ⟨n, h1, h2⟩ := ret_machine hR.noCall hent hqa.noCall hvb hi hlr
  exact ⟨n, h1, h2⟩

/-- `trap_trapIf` with the states at `R.noCall` (at no call line). -/
theorem trap_trapIfG {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ (∀ i < n, R.noCall.GoodX (iterN R.step i s)) ∧
      ∀ m, Arm.r .ERR (iterN R.step (n + m + 1) s) ≠ .None := by
  obtain ⟨n, h1, h2, h3⟩ := trap_trapIf hR.noCall hq.noCall hvb hi hops hholds
  exact ⟨n, h1, h2, h3⟩

/-- **`realizes_stepR` with the per-state facts `GoodXR P`**: the calls by
`realizes_callRG`/`realizes_tryCallRG`; every other step is one of `R.noCall.sem` (the same step
off the calls, `RL.noCall_sem`), realised by the lemma `realizes_step` uses at `R.noCall` (whose
states are at no call line) and lifted back (`MStep.guardLift`, `RL.noCall_le`). -/
theorem realizes_stepRG {R : RL} (hR : R.Wf) {P : BitVec 64 → Clif.Signature → Prop}
    (hC : CalleeOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    ∀ s c c', Q R s c → AInv R c → MStep R.vc (regG P R.sem) ckeep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodXR P (iterN R.step i s) := by
  intro s c c' hq hA h hns
  have hRN := hR.noCall
  have hqN := hq.noCall
  -- a realisation at `R.noCall` (a step that is no call), lifted to the guarded semantics
  have fin : ∀ n c'', MStep R.vc R.noCall.sem ckeep R.rf c c'' →
      Q R.noCall (iterN R.noCall.step n s) c'' →
      (∀ i < n, R.noCall.GoodX (iterN R.noCall.step i s)) →
      ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodXR P (iterN R.step i s) :=
    fun n c'' hm hq' ht => ⟨n, c'', MStep.guardLift hm h RL.noCall_le,
      ⟨hq'.ofNoCall, (aInv_step hRN hqN hA.noCall hm).ofNoCall⟩, fun i hi => .inl (ht i hi)⟩
  have finG : ∀ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodXR P (iterN R.step i s)) →
      ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.GoodXR P (iterN R.step i s) :=
    fun n c'' hm hq' ht => ⟨n, c'', hm, ⟨hq', aInv_step hR hq hA (MStep.regG_sub hm)⟩, ht⟩
  have nil : ∀ i < 0, R.noCall.GoodX (iterN R.noCall.step i s) :=
    fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (hR.alloc.ok).2.2
  cases h with
  | move =>
    obtain ⟨n, hn, ht⟩ := realizes_move hRN hqN (hns _ _ _ _ _ _ rfl)
    exact fin n _ MStep.move hn ht
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsemG hlen hho hcl hn =>
    have hsem := regG_sub hsemG
    have hN : (∀ info, i ≠ .call info) → (∀ info ti, i ≠ .tryCall info ti) →
        R.noCall.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
          some (outs, w', ctl) ∧
        MStep R.vc R.noCall.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' := fun h1 h2 => by
      have e : R.noCall.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
          some (outs, w', ctl) := by rw [RL.noCall_sem h1 h2]; exact hsem
      exact ⟨e, MStep.op hvb hi hops hsz e hlen hho hcl hn⟩
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    cases hct : i.isCtl
    · have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
      have hnt : ∀ info ti, i ≠ .tryCall info ti := by rintro info ti rfl; simp [MInst.isCtl] at hct
      rcases (hcov b vb k i hvb hi).resolve_left (by simp [hct]) with hfo | hpl
      rotate_left
      · -- the literal-pool load (#565)
        obtain ⟨sz, d, v, fl, rfl, -⟩ := isPoolLoad_form hpl
        obtain ⟨-, rfl⟩ := pool_world hsem
        obtain ⟨hsemN, -⟩ := hN hnc hnt
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_poolLoad hRN hqN hvb hi hpl hops hsz hsemN hlen hk
          exact fin n c'' hm hq' ht
      -- a covered straight-line form
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X.noCall) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      obtain ⟨hsemN, -⟩ := hN hnc hnt
      cases hn with
      | next hk =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_op_next hRN hqN hvb hi hops hsz hsemN hlen hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.noCall.sem_csem hsemN) hnc herrw)
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
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_callRG hR hC hq hvb hi hops hsz hsemG hlen hk
          exact finG n c'' hm hq' ht
      case args ds =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        exact fin 0 c' hstepN (realizes_args hRN hqN hA.noCall hvb hi hstepN) nil
      case rets us =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact fin 0 _ hstepN trivial nil
      case loadExtNameGot rd nm =>
        obtain ⟨hsemN, -⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddr hRN hqN hvb hi (.inl ⟨d, nm, rfl⟩) hops hsz
            hsemN hlen hk
          exact fin n c'' hm hq' ht
      case loadExtNameNear rd nm off =>
        obtain ⟨hsemN, -⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddr hRN hqN hvb hi (.inr ⟨d, nm, off, rfl⟩) hops
            hsz hsemN hlen hk
          exact fin n c'' hm hq' ht
      case jump l =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨n, hq', ht⟩ := realizes_goto hRN hqN hvb hi (.inl ⟨l, rfl⟩) hstepN
        exact fin n c' hstepN hq' ht
      case condBr t e kk =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨n, hq', ht⟩ := realizes_goto hRN hqN hvb hi (.inr (.inl ⟨t, e, kk, rfl⟩)) hstepN
        exact fin n c' hstepN hq' ht
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨n, hq', ht⟩ := realizes_goto hRN hqN hvb hi (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩))
          hstepN
        exact fin n c' hstepN hq' ht
      case trapIf kk code =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact fin 0 _ hstepN trivial nil
        · obtain ⟨n, hq', ht⟩ := realizes_trapIf_next hRN hqN hvb hi hstepN
            (fun w'' e => hh ⟨w'', e⟩)
          exact fin n c' hstepN hq' ht
      case udf code =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact fin 0 _ hstepN trivial nil
      case emitIsland nb =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        exact fin 0 c' hstepN (realizes_island hRN hqN hvb hi hstepN) nil
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_jt hRN hqN hvb hi hstepN
        exact fin n c'' hm hq' ht
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_rmwLoop hRN hqN hvb hi hstepN
        exact fin n c'' hm hq' ht
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨-, hstepN⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_casLoop hRN hqN hvb hi hstepN
        exact fin n c'' hm hq' ht
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tryCallRG hR hC (hT (hasTryCall_of_mem hvb hi)) hq
            hvb hi hops hsz hsemG hlen hk1 hsucc hitems rfl
          exact finG n c'' hm hq' ht
      case elfTlsGetAddr nm rd tmp =>
        obtain ⟨hsemN, -⟩ := hN (fun _ h => by cases h) (fun _ _ h => by cases h)
        have hv := ctlCheck_inst hck hvb hi
        simp only [ctlInstOk, Bool.and_eq_true] at hv
        obtain ⟨d, rfl⟩ := isVregInt_iff hv.1
        obtain ⟨t, rfl⟩ := isVregInt_iff hv.2
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tls hRN (hTls (hasTls_of_mem hvb hi)).noCall hqN hvb
            hi hops hsz hsemN hlen hk
          exact fin n c'' hm hq' ht

/-- **`realizes_allR` with the per-state facts `GoodXR P`.** -/
theorem realizes_allRG {R : RL} (hR : R.Wf) {P : BitVec 64 → Clif.Signature → Prop}
    (hC : CalleeOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    Realizes R.vc R.rf (regG P R.sem) ckeep R.step (QA R) (R.GoodXR P) :=
  realizesQA hR (realizes_stepRG hR hC hT hTls hcov)
    (fun _ _ _ _ _ _ _ hq hs =>
      let ⟨n, h1, h2⟩ := realizes_move hR.noCall hq.noCall hs
      ⟨n, h1.ofNoCall, fun i hi => .inl (h2 i hi)⟩)
    (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepR hvb hi h)

/-- **`regLevelCorrect_world_atXR` with the per-state facts `actGoodXR P`**: the same proof on
`realizes_allRG`, the prologue, epilogue and trap states at `R.noCall` (`q_initG`, `ret_machineG`,
`trap_trapIfG`). -/
theorem regLevelCorrect_world_atXRG {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
        ∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c, VTraps vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨p, hp, hL, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, p.ps, K, G, gv⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hcheck, hok⟩, AllocAF.of_lowerRFunc halloc, hemit, hlayout, hlm, by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres,
    ⟨p, hp, rfl⟩, hent.program, hG, noLeaf_of_lowerRFunc halloc⟩
  have hck := (hR.alloc.ok).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_initG hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf (regG P R.sem) ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
  have hRz := realizes_allRG hR hC hCT hTls hcov
  -- the states of the run: `GoodX`, from the entry's run (`q_init`) and the realised items
  have hmk : ∀ (n1 n23 : Nat), (∀ i < n1 + n23, R.GoodXR P (iterN R.step i (iterN R.step n0 s))) →
      ∀ i < n0 + (n1 + n23), actGoodXR P vcp rf af fa fb base s X H K G gv
        (E2E.runX (ArmStepX X H fa) i s) := by
    intro n1 n23 hb i hi
    rw [runX_eq]
    exact RL.GoodXR.act (trace_add (T := R.GoodXR P) (fun i hi => .inl (ht0 i hi)) hb i hi)
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
          ret_machineG hR hent hq2 hvb hi (RL.leafRegs3 hR (fun i hi => (ht0 i hi).ofNoCall)
            (fun i hi => (ht1 i hi).toGoodX) (fun i hi => (ht2 i hi).toGoodX))
        -- every state of the run before the return is `GoodX`
        have htr : ∀ i < n0 + n1 + n2 + n3, R.GoodXR P (E2E.runX (ArmStepX X H fa) i s) := by
          intro i hi
          rw [runX_eq]
          exact trace_add (T := R.GoodXR P) (fun i hi => .inl (ht0 i hi))
            (trace_add ht1 (trace_add ht2 (fun i hi => .inl (ht3 i hi)))) i (by omega)
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 s) (.reg r) = regVal (iterN R.step n0 s) r :=
          fun _ => rfl
        refine ⟨n0 + n1 + n2 + n3, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun i hi0 hi hpcall => ?_⟩,
          fun i hi => (htr i hi).act⟩
        rotate_right
        · exact (htr i hi).toGoodX.good.resolve_left (fun h => h hpcall)
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
            obtain ⟨n3, htrap, ht3, hstuck⟩ := trap_trapIfG hR hq2 hvb hi hops' hholds
            refine ⟨n0 + n1 + n2 + n3, by rw [hfin]; exact htrap,
              fun i hi => hmk n1 (n2 + n3) (trace_add ht1 (trace_add ht2 (fun i hi => .inl (ht3 i hi)))) i
                (by omega),
              fun m => ?_⟩
            rw [show n0 + n1 + n2 + n3 + m + 1 = n0 + n1 + n2 + (n3 + m + 1) by omega, hfin]
            exact hstuck m

/-- `RegLevelWorldXR` with the per-state facts `actGoodXR P` (the guarded call premise; #753 R3'). -/
def _root_.E2E.RegLevelWorldXRG : Prop :=
  ∀ {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
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
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV),
    (∀ us vals w, VReturns vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, (ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
        ∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c, VTraps vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None)

/-- **`regLevelCorrect_worldXR` with the per-state facts `actGoodXR P`** (`RegLevelWorldXRG`). -/
theorem regLevelCorrect_worldXRG : RegLevelWorldXRG := by
  intro vcp rf af fa fb k hcheck halloc hemit hlayout X H K G gv P hcov base ra s hent hres hG hC
    hCT hTls w₀ hbe ρ₀
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_atXRG hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof

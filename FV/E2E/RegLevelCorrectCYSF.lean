import FV.E2E.RegLevelCorrectCYS

/-!
# The dispatcher with the segment's lines (SEM1 #537, `docs/plans/uninit.md` §5.9, machine lock)

`realizes_allCWS` also exporting that the segment realising the step runs no frame-record line
and no `ret` (`RL.FRFree`), from the `realizes_*NAF` cases (each segment runs only lines of its
own item, and no allocated instruction's lines hold one, `frLine_lines`). Same proof otherwise.

* `realizes_op_nextNASF`, **`realizes_allCWSF`**.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- **`realizes_op_nextNAS` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_op_nextNASF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hYF : ∀ a, R.F a → Y a)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hsemY : (∃ rY, csem Y R.ctx R.X i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))
      w = some rY) ∨ ∀ (regs : Array Reg) i', i.assign regs = .ok i' → i'.memRd = false)
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    (hOS : ∀ env, OperandsSound R.F (execMInst R.ctx env) (csem R.F R.ctx R.X) i)
    (hL : ∀ regs i', i.assign regs = .ok i' →
      LinesOk R.ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us))
    (hRd : ∀ {F' : BitVec 64 → Prop} {regs : Array Reg} {i' : MInst} {ls : List Line}
      {ps ps' : PState} {u v : Arm.ArmState}
      {r : List CV × Arm.ArmState × Ctl}, AllocOk ops regs → i.assign regs = .ok i' →
      i'.lines R.ctx ps = .ok (ls, ps') → SameWorld F' u v → Arm.r .ERR v = .None →
      Arm.CheckSPAlignment v → csem F' R.ctx R.X i (useVals ops regs u) v = some r → ∀ env,
      LinesReads env ls u (fun a => ¬ F' a))
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  rcases hsemY with ⟨rY, hsemY⟩ | hnr
  · exact realizes_op_nextNAF hR hYF hq hvb hi hops hsz hsem hsemY hlen hk hOS hL hRd hW'
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 s (R.ReadInY Y false) :=
    fun regs i' _ _ hasg hl1 _ => linesReads_noLoads (lines_noLoads (hl1 {}) (hnr regs i' hasg))
  exact realizes_op_coreXNAF hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 u (R.ReadInY Y false))
    hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAs_of_linesOkNA hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'

set_option maxHeartbeats 4000000 in
/-- **`realizes_stepCWS` with the segment's lines** (`RL.FRFree`; same proof on the
`realizes_*NAF` cases). -/
theorem realizes_stepCWSF {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' : MConf CV Arm.ArmState} (hq : QW R s j ps1 T c) (hA : AInv R c) (hP : P s)
    (hG : MStep R.vc (R.semGS Ok) ckeep R.rf c c')
    (hns : ∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) :
    ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n ∧
      R.FRFree s n := by
  have lift : ∀ c'', MStep R.vc R.sem ckeep R.rf c c'' → MStep R.vc (R.semGS Ok) ckeep R.rf c c'' :=
    fun c'' h'' => MStep.guardLift h'' hG RL.semGS_le
  have fin1 : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' →
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' →
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) →
      countIn R.CallSt R.step s n = opCalls R.vc c → R.SegLenA j ps1 T c c'' s n →
      R.FRFree s n →
      ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
        QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
          (R.nextW j ps1 T c c'').2.2 c'' ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n ∧
        R.FRFree s n :=
    fun Y hYF hYO n c'' hm hq' ht hc hs hf => ⟨n, c'', lift c'' hm, MStep.shapeEq (lift c'' hm) hG,
      aInv_step hR hq.q hA hm, hq', fun i hi => ⟨(ht i hi).1, Y, hYF, hYO, (ht i hi).2⟩, hc, hs, hf⟩
  have fin : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' →
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' →
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) → opCalls R.vc c = 0 →
      R.SegLenA j ps1 T c c'' s n → R.FRFree s n →
      ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
        QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
          (R.nextW j ps1 T c c'').2.2 c'' ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n ∧
        R.FRFree s n :=
    fun Y hYF hYO n c'' hm hq' ht h0 hs hf => fin1 Y hYF hYO n c'' hm hq'
      (fun i hi => ⟨(ht i hi).1.1, (ht i hi).2⟩)
      (by rw [h0]; exact countIn_zero_of fun i hi => (ht i hi).1.2) hs hf
  have finT := fin (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have fin1T := fin1 (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have nil : ∀ i < 0, R.GoodXNY (fun _ => True) (iterN R.step i s) :=
    fun _ h => absurd h (Nat.not_lt_zero _)
  have z := RL.frFree_zero R s
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases hG with
  | move =>
    obtain ⟨n, hq', ht, hs, hf⟩ := realizes_moveNAF (Y := fun _ => True) hR hq (hns _ _ _ _ _ _ rfl)
    exact finT n _ MStep.move hq' ht rfl hs hf
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsemG hlen hho hcl hn =>
    obtain ⟨hguard, hsem⟩ := RL.semGS_inv hsemG
    have hoc : opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = if i.isCallI then 1 else 0 := by
      simp only [opCalls, hvb, hi]
    have hoc0 : i.isCallI = false → opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = 0 :=
      fun h => by rw [hoc, h]; rfl
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have toA : ∀ {c'' : MConf CV Arm.ArmState} {n : Nat},
        MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' →
        (∀ us, i ≠ .rets us) →
        ((∃ cd, i = .udf cd) ∨ (∃ kk cd, i = .trapIf kk cd) → ∀ w'', c'' ≠ .halt w'') →
        R.SegLen j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n →
        R.SegLenA j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n :=
      fun hm hnr hnh hs => RL.segLenA_of_run (RL.mstep_run hm hvb hi hnr hnh) hs
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq.q
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    obtain ⟨Y, hYF, hOk, hwr⟩ := hguard
    have hYO : (∀ a, Y a) ∨ ∃ w, Ok w Y := .inr ⟨w, hOk⟩
    cases hct : i.isCtl
    · rcases (hcov b vb k i hvb hi).resolve_left (by simp [hct]) with hfo | hpl
      rotate_left
      · -- the literal-pool load (#565)
        obtain ⟨sz, d, v, fl, rfl, -⟩ := isPoolLoad_form hpl
        obtain ⟨-, rfl⟩ := pool_world hsem
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_poolLoadNAF (Y := fun _ => True) hR hq
            hvb hi hpl hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
            hf
      -- a covered straight-line form
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      have hwi : i.wReads = true := by
        simp [MInst.wReads, hct]
      have hsemY := (hwr hwi).imp_right fun h (regs : Array Reg) (i' : MInst) hasg =>
        formOk_noLoad_memRd hfo h (regs := regs) (i' := i') hasg
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_op_nextNASF hR hYF hq hvb hi hops hsz
          hsem hsemY hlen hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        refine fin Y hYF hYO n c'' hm hq' ht
          (hoc0 (by cases i <;> first | rfl | simp [MInst.isCtl] at hct))
          (toA hm (fun us h => by subst h; simp [MInst.isCtl] at hct)
            (fun h => by rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [MInst.isCtl] at hct) hs) hf
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, ⟨i0, hi0, hc0, hnc⟩, hs, hf⟩ :=
            realizes_callNAF (Y := fun _ => True) hR hC hP hq hvb hi hops hsz hsem hlen hk
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
            hf
      case args ds =>
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          have hQ := realizes_args hR hq.q hA hvb hi hstep
          obtain ⟨hq', -, hs⟩ := realizes_zeroNA (Y := fun _ => True) hq hvb hi (.inl ⟨ds, rfl⟩)
            (q_stRel hQ)
          exact finT 0 _ hstep hq' nil (hoc0 rfl) hs z
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl z
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_symAddrNAF (Y := fun _ => True) hR hq
            hvb hi (.inl ⟨d, nm, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
            hf
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_symAddrNAF (Y := fun _ => True) hR hq
            hvb hi (.inr ⟨d, nm, off, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
            hf
      case jump l =>
        obtain ⟨n, ⟨hq', ht, hs⟩, hf⟩ := realizes_gotoNAF (Y := fun _ => True) hR hq hvb hi
          (.inl ⟨l, rfl⟩) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
          hf
      case condBr t e kk =>
        obtain ⟨n, ⟨hq', ht, hs⟩, hf⟩ := realizes_gotoNAF (Y := fun _ => True) hR hq hvb hi
          (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
          hf
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, ⟨hq', ht, hs⟩, hf⟩ := realizes_gotoNAF (Y := fun _ => True) hR hq hvb hi
          (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
          hf
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl z
        · obtain ⟨n, ⟨hq', ht, hs⟩, hf⟩ := realizes_trapIf_nextNAF (Y := fun _ => True) hR hq hvb
            hi hstep (fun w'' e => hh ⟨w'', e⟩)
          exact finT n c' hstep hq' ht (hoc0 rfl)
            (toA hstep (fun _ h => by cases h) (fun _ w'' e => hh ⟨w'', e⟩) hs) hf
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl z
      case emitIsland nb =>
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          have hQ := realizes_island hq.q hvb hi hstep
          obtain ⟨hq', -, hs⟩ := realizes_zeroNA (Y := fun _ => True) hq hvb hi (.inr ⟨nb, rfl⟩)
            (q_stRel hQ)
          exact finT 0 _ hstep hq' nil (hoc0 rfl) hs z
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_jtNAF (Y := fun _ => True) hR hq hvb hi
          hstep
        exact finT n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
          hf
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_rmwLoopNAF hR hq hvb hi hstep
          fun ops' hops' => by
            rw [hops] at hops'; cases hops'
            exact (hwr rfl).resolve_right fun h => by simp [MInst.loadForm] at h
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
          hf
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_casLoopNAF hR hq hvb hi hstep
          fun ops' hops' => by
            rw [hops] at hops'; cases hops'
            exact (hwr rfl).resolve_right fun h => by simp [MInst.loadForm] at h
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
          hf
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht, ⟨i0, hi0, hc0, hnc⟩, hs, hf⟩ :=
            realizes_tryCallNAF (Y := fun _ => True) hR hC (hT (hasTryCall_of_mem hvb hi)) hP hq hvb
              hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
            hf
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
          obtain ⟨n, c'', hm, ⟨hq', ht, hs⟩, hf⟩ := realizes_tlsNAF (Y := fun _ => True) hR
            (hTls (hasTls_of_mem hvb hi)) hq hvb hi hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
            hf

/-- **`realizes_allCWS` with the segment's lines** (`RL.FRFree`; `realizesQWA` on
`realizes_stepCWSF`). -/
theorem realizes_allCWSF {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' : MConf CV Arm.ArmState} (hq : QWA R s j ps1 T c) (hP : P s)
    (hG : MStep R.vc (R.semGS Ok) ckeep R.rf c c') :
    ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧
      QWA R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n ∧
      R.FRFree s n :=
  realizesQWA (Tr := fun u => R.GoodX u ∧ R.WReadsIn Ok u) (Ex := R.FRFree) hR
    (fun s => RL.frFree_zero R s) (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepGS hvb hi h)
    (fun s j ps1 T b src dst its m w hq hs =>
      let ⟨n, h1, h2, h3, h4⟩ := realizes_moveNAF (Y := fun _ => True) hR hq hs
      ⟨n, h1, fun i hi => ⟨(h2 i hi).1.1, fun _ => True, fun _ _ => trivial,
        .inl fun _ => trivial, (h2 i hi).2⟩, countIn_zero_of fun i hi => (h2 i hi).1.2, h3, h4⟩)
    (fun hq hA hns => realizes_stepCWSF hR Ok hC hT hTls hcov hq hA hP hG hns) hq hG

end Backend.Proof

import FV.E2E.RegLevelCorrectPRSY
import FV.E2E.RegLevelCorrectCW

/-!
# The activation's run cut into realised segments (SEM1 #537, item (3), route (a))

`regLevelCorrect_world_atCSY`'s return case on `realizes_allC_spW`: the run to the return is the
prologue (`q_initNA`: exactly its line count), a chain of realised segments from the initial
witness (`RL.SegChain`, every segment cut at its first arrival), and the epilogue and `ret`
(`ret_machineNA`: exactly `RL.retLen` steps).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- The activation's data as an `RL` (the counted external semantics at call number 0). -/
def actRL (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin)
    (lm : Std.HashMap Lbl Nat) (base : BitVec 64) (s : Arm.ArmState) (XI : ExtSemI) (H : ArmHooks)
    (psF : PState) (K : Nat) (G : BitVec 64 → Prop) (gv : Nat → String → Prop) : RL :=
  ⟨vcp, rf, af, fa, fb, lm, base, s, XI.at 0, H, psF, K, G, gv⟩

/-- `QW` does not read the external semantics (given the state after the prologue does not,
`RL.sP_withX`). -/
theorem QW.ofWithX {R : RL} {X : ExtSem} (hP : ({ R with X := X } : RL).sP = R.sP)
    {s : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} {c : MConf CV Arm.ArmState} (h : QW { R with X := X } s j ps1 T c) :
    QW R s j ps1 T c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    obtain ⟨vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10.ofWithX hP⟩
  | ret => trivial
  | halt => trivial

theorem QW.withX {R : RL} {X : ExtSem} (hP : ({ R with X := X } : RL).sP = R.sP)
    {s : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} {c : MConf CV Arm.ArmState} (h : QW R s j ps1 T c) :
    QW { R with X := X } s j ps1 T c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    obtain ⟨vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    exact ⟨vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10.withX hP⟩
  | ret => trivial
  | halt => trivial

/-- `QWA` does not read the external semantics (given the state after the prologue does not). -/
theorem QWA.ofWithX {R : RL} {X : ExtSem} (hP : ({ R with X := X } : RL).sP = R.sP)
    {s : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} {c : MConf CV Arm.ArmState} (h : QWA { R with X := X } s j ps1 T c) :
    QWA R s j ps1 T c := by
  rcases h with ⟨hq, hA⟩ | h
  · exact .inl ⟨hq.ofWithX hP, hA⟩
  · cases c with
    | run vs =>
      obtain ⟨b, its, m, w⟩ := vs
      obtain ⟨mt, D, hq, hm, ht⟩ := h
      exact .inr ⟨mt, D, hq.ofWithX hP, hm, ht⟩
    | ret => exact h.elim
    | halt => exact h.elim

theorem QWA.withX {R : RL} {X : ExtSem} (hP : ({ R with X := X } : RL).sP = R.sP)
    {s : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} {c : MConf CV Arm.ArmState} (h : QWA R s j ps1 T c) :
    QWA { R with X := X } s j ps1 T c := by
  rcases h with ⟨hq, hA⟩ | h
  · exact .inl ⟨hq.withX hP, hA⟩
  · cases c with
    | run vs =>
      obtain ⟨b, its, m, w⟩ := vs
      obtain ⟨mt, D, hq, hm, ht⟩ := h
      exact .inr ⟨mt, D, hq.withX hP, hm, ht⟩
    | ret => exact h.elim
    | halt => exact h.elim

/-- A segment chain of an activation with another external semantics of the same machine is
one of the activation (the trace predicate weakened). -/
theorem RL.SegChain.ofWithX {R : RL} {X : ExtSem} (hX : ({ R with X := X } : RL).step = R.step)
    {Tr Tr' : Arm.ArmState → Prop} (hT : ∀ u, Tr' u → Tr u) {s : Arm.ArmState}
    {W : Nat × PState × List Line} {c : MConf CV Arm.ArmState}
    {l : List (Nat × MConf CV Arm.ArmState)} {u : Arm.ArmState} {W' : Nat × PState × List Line}
    {c' : MConf CV Arm.ArmState} (h : RL.SegChain { R with X := X } Tr' s W c l u W' c') :
    R.SegChain Tr s W c l u W' c' := by
  induction h with
  | nil => exact .nil
  | @snoc l u W1 c1 c2 n _ hs ht ih =>
    rw [hX]
    refine .snoc ih ?_ fun i hi => hT _ (by rw [← hX]; exact ht i hi)
    cases c2 with
    | run _ =>
      simp only [RL.SegLenA, RL.SegLen, FirstArr] at hs ⊢
      rw [hX] at hs
      exact hs
    | ret => exact hs
    | halt => exact hs

theorem RL.SegChain.withX {R : RL} {X : ExtSem} (hX : ({ R with X := X } : RL).step = R.step)
    {Tr Tr' : Arm.ArmState → Prop} (hT : ∀ u, Tr u → Tr' u) {s : Arm.ArmState}
    {W : Nat × PState × List Line} {c : MConf CV Arm.ArmState}
    {l : List (Nat × MConf CV Arm.ArmState)} {u : Arm.ArmState} {W' : Nat × PState × List Line}
    {c' : MConf CV Arm.ArmState} (h : R.SegChain Tr s W c l u W' c') :
    RL.SegChain { R with X := X } Tr' s W c l u W' c' := by
  induction h with
  | nil => exact .nil
  | @snoc l u W1 c1 c2 n _ hs ht ih =>
    rw [← hX]
    refine .snoc ih ?_ fun i hi => hT _ (by rw [hX]; exact ht i hi)
    cases c2 with
    | run _ =>
      simp only [RL.SegLenA, RL.SegLen, FirstArr] at hs ⊢
      rw [hX]
      exact hs
    | ret => exact hs
    | halt => exact hs

set_option maxHeartbeats 4000000 in
/-- **The returning run, segmented**: `regLevelCorrect_world_atCSY`'s return with the run's
length split as prologue + a chain of realised segments from the initial witness + epilogue. -/
theorem regLevelCorrect_world_atCSW {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkGP (fun u => OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        OnCall (ArmStepX (XI.at 0) H fa) fa base s n u ∧ spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    ∀ us vals w nc, VRetFrom vcp (csemVIG gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI Ok) ⟨0, 0, ρsel m₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ (l : List (Nat × MConf CV Arm.ArmState)) (W : Nat × PState × List Line)
        (c' : MConf CV Arm.ArmState),
        (actRL vcp rf af fa fb lm base s XI H psF K G gv).SegChain
          (fun u => (actRL vcp rf af fa fb lm base s XI H psF K G gv).Good u ∧
            (actRL vcp rf af fa fb lm base s XI H psF K G gv).WReadsIn Ok u)
          (E2E.runX (ArmStepX (XI.at 0) H fa) (prologueLines af.saves af.frameSize af.isCaller).length s)
          (actRL vcp rf af fa fb lm base s XI H psF K G gv).initW
          (MConf.init rf (locVal (RAFrame.compute vcp rf)
            (E2E.runX (ArmStepX (XI.at 0) H fa) (prologueLines af.saves af.frameSize af.isCaller).length s)) w₀) l
          (E2E.runX (ArmStepX (XI.at 0) H fa)
            ((prologueLines af.saves af.frameSize af.isCaller).length + (l.map Prod.fst).sum) s) W c' ∧
        Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) ((prologueLines af.saves af.frameSize af.isCaller).length +
          (l.map Prod.fst).sum + (actRL vcp rf af fa fb lm base s XI H psF K G gv).retLen) s) = ra ∧
        ∀ i < (prologueLines af.saves af.frameSize af.isCaller).length + (l.map Prod.fst).sum +
            (actRL vcp rf af fa fb lm base s XI H psF K G gv).retLen,
          actWReadsIn vcp rf af fa fb base s (XI.at 0) H K G gv Ok
            (E2E.runX (ArmStepX (XI.at 0) H fa) i s) := by
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XI.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hpsF⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨n0, hn0, ht0, hq0, hA0, -⟩ := q_initNA (Y := fun _ => True) hR hent hbe
  have hn0' : n0 = (prologueLines af.saves af.frameSize af.isCaller).length := hn0
  subst hn0'
  let s₁ := iterN R.step (prologueLines af.saves af.frameSize af.isCaller).length s
  let c₁ := MConf.init R.rf (locVal R.fr s₁) w₀
  obtain ⟨Rl, hSim, hinit, -⟩ :=
    checkedAt_sound R.vc R.rf (csemVIG R.gv R.F R.ctx XI Ok) ckeep hcheck
      (locVal R.fr s₁) (ρsel (locVal R.fr s₁)) (w₀, 0) (hsel _)
  have hP0 : countIn R.CallSt R.step s (prologueLines af.saves af.frameSize af.isCaller).length = 0 :=
    countIn_zero_of fun i hi => (ht0 i hi).1.2
  let QC : Arm.ArmState → MConf CV Arm.ArmState → Prop := fun u c =>
    ∃ l W, R.SegChain (fun u => R.Good u ∧ R.WReadsIn Ok u) s₁ R.initW c₁ l u W c ∧
      QWA R u W.1 W.2.1 W.2.2 c
  have hRz := Realizes.ofStepC (vc := R.vc) (rf := R.rf) (keep := ckeep) (C := R.CallSt)
    (T := fun u => R.Good u ∧ R.WReadsIn Ok u)
    (Q := fun p c => QC p.1 (c.mapW Prod.fst) ∧ p.2 = c.world.2 ∧
      ∃ i, p = iterN (stepC R.CallSt R.step) i (s₁, 0)) (by
    refine RealizesCP.countedRun (vc := R.vc) (rf := R.rf) (keep := ckeep)
      (sem := fun n => csemVG R.gv R.F R.ctx (XI.at n) Ok)
      (Q := QC) (T := fun u => R.Good u ∧ R.WReadsIn Ok u) (C := R.CallSt)
      (P := fun n u => OnCall R.step fa base s n u) (s0 := s₁) (fun n => ?_)
      (onCall_of_run hP0)
    have hX : ({ R with X := XI.at n } : RL).step = R.step := rfl
    have hP : ({ R with X := XI.at n } : RL).sP = R.sP := RL.sP_withX hR hent (XI.at n)
    exact ((realizes_allC_spW (hRn n) Ok (hC n) (fun h => hCT h n) (fun h => hTls h n) hcov
      s₁ R.initW c₁).mono_T (T' := fun u => R.Good u ∧ R.WReadsIn Ok u)
        fun _ h => ⟨h.1.good, h.2⟩).congr_Q fun u c => by
      constructor
      · rintro ⟨l, W, hch, hq⟩
        exact ⟨l, W, RL.SegChain.ofWithX (R := R) (X := XI.at n) hX (fun _ h => h) hch,
          QWA.ofWithX (R := R) (X := XI.at n) hP hq⟩
      · rintro ⟨l, W, hch, hq⟩
        exact ⟨l, W, RL.SegChain.withX (R := R) (X := XI.at n) hX (fun _ h => h) hch,
          QWA.withX (R := R) (X := XI.at n) hP hq⟩)
  have hTop : ∀ u, R.ReadsInY (fun _ => True) u → R.WReadsIn Ok u :=
    fun u h => ⟨fun _ => True, fun _ _ => trivial, .inl fun _ => trivial, h⟩
  refine ⟨locVal R.fr s₁, fun us vals w nc hret => ?_⟩
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
  obtain ⟨n1, c1, hz1, hr1, ht1⟩ := forward hSim hRz hstar hinit
    ⟨0, ⟨[], R.initW, .nil, .inl ⟨hq0, hA0⟩⟩, rfl, 0, rfl⟩
  obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
  rw [operands_retsC] at hops
  cases hops
  have h1 : VStep R.vc (csemVIG R.gv R.F R.ctx XI Ok) (.run ⟨b, k, ρ, w₁⟩) (.ret vals (w, nc)) := by
    obtain ⟨hsemG, -⟩ := ISem.counted_some hsem
    have hsem' := (csemVG_inv hsemG).2
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, -, -⟩ := hsem'
    rw [hvals]
    refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_ (VNext.ret rfl)
    rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
  obtain ⟨n2, c', c'', ⟨_, ⟨l, W, hch, hqW⟩, -⟩, hr2, hms, hr3, -⟩ :=
    forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hz1
  -- the chain ends at the `rets` item
  have hret : ∃ n3, n3 = R.retLen ∧
      (∀ i < n3, R.GoodXNY (fun _ => True) (iterN R.step i (iterN R.step n2 (iterN R.step n1 s₁)))) ∧
      Arm.r .PC (iterN R.step n3 (iterN R.step n2 (iterN R.step n1 s₁))) = ra := by
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        dsimp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hq2' : QA R (iterN R.step n2 (iterN R.step n1 s₁))
            (.run ⟨b, .op k _ :: _, _, w₁.1⟩) := hqW.qa
        obtain ⟨n3, hn3, ht3, hpc, -⟩ := ret_machineNA (Y := fun _ => True) hR hent hq2' hvb hi
        exact ⟨n3, hn3, ht3, hpc⟩
  obtain ⟨n3, hn3, ht3, hpc⟩ := hret
  subst hn3
  have hU : iterN R.step ((prologueLines af.saves af.frameSize af.isCaller).length + (l.map Prod.fst).sum) s =
      iterN R.step n2 (iterN R.step n1 s₁) := by
    rw [iterN_add]; exact hch.iter.symm
  refine ⟨l, W, c'.mapW Prod.fst, ?_, ?_, fun i hi => ?_⟩
  · rw [runX_eq, runX_eq]
    show R.SegChain (fun u => R.Good u ∧ R.WReadsIn Ok u) s₁ R.initW c₁ l
      (iterN R.step ((prologueLines af.saves af.frameSize af.isCaller).length + (l.map Prod.fst).sum) s) W _
    rw [hU]; exact hch
  · rw [runX_eq]
    show Arm.r .PC (iterN R.step ((prologueLines af.saves af.frameSize af.isCaller).length + (l.map Prod.fst).sum +
      R.retLen) s) = ra
    rw [iterN_add, hU]; exact hpc
  · rw [runX_eq]
    refine trace_add (T := fun u => R.WReadsIn Ok u) (step := R.step)
      (a := (prologueLines af.saves af.frameSize af.isCaller).length) (b := (l.map Prod.fst).sum + R.retLen)
      (fun j hj => hTop _ (ht0 j hj).2)
      (trace_add (T := fun u => R.WReadsIn Ok u) (step := R.step) (a := (l.map Prod.fst).sum)
        (b := R.retLen) (fun j hj => (hch.trace j hj).2) (fun j hj => ?_)) i (by
          have : R.retLen = (actRL vcp rf af fa fb lm base s XI H psF K G gv).retLen := rfl
          omega)
    show R.WReadsIn Ok (iterN R.step j (iterN R.step (l.map Prod.fst).sum s₁))
    rw [← hch.iter]
    exact hTop _ (ht3 j hj).2

end Backend.Proof

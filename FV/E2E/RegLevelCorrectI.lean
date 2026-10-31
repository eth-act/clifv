import FV.E2E.RegLevelCorrect
import FV.Backend.Proof.VCodeSemI

/-!
# The register-level theorem for the counted VCode world (SEM1 step 2, `docs/plans/uninit.md` §5.4)

`regLevelCorrect_world` (`FV/E2E/RegLevelCorrect.lean`) for the VCode run of `csemVI`: the
guarded semantics `csemV` whose call number `n` (the world's counter) has the external semantics
`XI.at n` (an `ExtSemI`, `FV/Backend/Proof/VCodeSemI.lean`), a call bumping the counter.

* `ISem.counted sem`: a semantics on `W × Nat` whose step at counter `n` is `sem n`'s, the counter
  bumped by the calls (`csemI` is `ISem.counted (csem · (X.at ·))`, `csemI_eq_counted`);
  `ISem.counted_some`; `MStep.counted_proj`/`MStep.counted_lift`: an allocated-code step at
  counter `n` is one of `sem n` on the first components, and back;
* `Realizes.counted`: the machine realises the counted semantics under `Q` of the first
  components when it realises every `sem n` under `Q` (the same machine and trace invariant);
  `Realizes.mono_T`;
* `csemVI`, `csemVI_sub` (a run of `csemVI` is one of `csemI`);
* `regLevelCorrect_world_atI`, `regLevelCorrect_worldI`: returns and traps of the counted run are
  realised by the machine `ArmStepX (XI.at 0) H fa` (it reads only `XI.sym`, the same at every
  index), with the callee contracts (`CalleeOkG`, `CalleeTryOkG`, `TlsOk`) of every index. The
  counter is not yet related to the machine's calls (`callsBefore`): with it in the relation the
  contract of index `n` is needed only at the run's `n`-th call (next item).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-! ## Counted semantics -/

section
variable {V W : Type}

/-- **The counted semantics of `sem`**: at counter `n`, `sem n` on the first component, a call
bumping the counter. -/
def ISem.counted (sem : Nat → ISem V W) : ISem V (W × Nat) := fun i uses w =>
  (sem w.2 i uses w.1).map fun r => (r.1, (r.2.1, if i.isCallI then w.2 + 1 else w.2), r.2.2)

theorem csemI_eq_counted (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    csemI F ctx X = ISem.counted fun n => csem F ctx (X.at n) := rfl

variable {vc : VCode} {rf : RFunc} {keep : Reg → V → V} {sem : Nat → ISem V W}

theorem ISem.counted_some {i : MInst} {uses : List V} {w : W × Nat} {outs : List V}
    {w' : W × Nat} {ctl : Ctl} (h : ISem.counted sem i uses w = some (outs, w', ctl)) :
    sem w.2 i uses w.1 = some (outs, w'.1, ctl) ∧ w'.2 = (if i.isCallI then w.2 + 1 else w.2) := by
  simp only [ISem.counted, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨o, v, c⟩, hs, rfl, rfl, rfl⟩ := h
  exact ⟨hs, rfl⟩

/-- **An allocated-code step at counter `n` is one of `sem n`** on the first components. -/
theorem MStep.counted_proj {b : Nat} {its : List RItem} {m : Loc → V} {w : W} {n : Nat}
    {c' : MConf V (W × Nat)}
    (h : MStep vc (ISem.counted sem) keep rf (.run ⟨b, its, m, (w, n)⟩) c') :
    MStep vc (sem n) keep rf (.run ⟨b, its, m, w⟩) (c'.mapW Prod.fst) := by
  cases h with
  | move => exact .move
  | op hb hi ho ha hs hl hh hc hn =>
    exact .op hb hi ho ha (ISem.counted_some hs).1 hl hh hc (MNext_mapW hn)

/-- **A step of `sem n` lifts to the counted semantics at counter `n`.** -/
theorem MStep.counted_lift {b : Nat} {its : List RItem} {m : Loc → V} {w : W} {n : Nat}
    {d : MConf V W} (h : MStep vc (sem n) keep rf (.run ⟨b, its, m, w⟩) d) :
    ∃ c', c'.mapW Prod.fst = d ∧
      MStep vc (ISem.counted sem) keep rf (.run ⟨b, its, m, (w, n)⟩) c' := by
  cases h with
  | move => exact ⟨.run ⟨b, _, _, (w, n)⟩, rfl, .move⟩
  | @op _ _ _ _ _ _ _ i _ _ _ w' _ _ _ hb hi ho ha hs hl hh hc hn =>
    obtain ⟨c'', rfl, hn'⟩ := MNext_liftW (π := Prod.fst)
      (w := (w', if i.isCallI then n + 1 else n)) hn
    refine ⟨c'', rfl, .op hb hi ho ha ?_ hl hh hc hn'⟩
    simp only [ISem.counted, hs, Option.map_some]

/-- `Realizes` with a weaker trace invariant. -/
theorem Realizes.mono_T {S : Type} {sem' : ISem V W} {step : S → S} {Q : S → MConf V W → Prop}
    {T T' : S → Prop} (h : Realizes vc rf sem' keep step Q T) (hT : ∀ s, T s → T' s) :
    Realizes vc rf sem' keep step Q T' := fun s c c' hq hs =>
  let ⟨n, c'', hm, hq', ht⟩ := h s c c' hq hs
  ⟨n, c'', hm, hq', fun i hi => hT _ (ht i hi)⟩

/-- `Realizes` under an equivalent relation. -/
theorem Realizes.congr_Q {S : Type} {sem' : ISem V W} {step : S → S} {Q Q' : S → MConf V W → Prop}
    {T : S → Prop} (h : Realizes vc rf sem' keep step Q T) (hQ : ∀ s c, Q s c ↔ Q' s c) :
    Realizes vc rf sem' keep step Q' T := fun s c c' hq hs =>
  let ⟨n, c'', hm, hq', ht⟩ := h s c c' ((hQ s c).2 hq) hs
  ⟨n, c'', hm, (hQ _ _).1 hq', ht⟩

/-- **The machine realises the counted semantics** under `Q` of the first components when it
realises the semantics of every index under `Q`. -/
theorem Realizes.counted {S : Type} {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (h : ∀ n, Realizes vc rf (sem n) keep step Q T) :
    Realizes vc rf (ISem.counted sem) keep step (fun s c => Q s (c.mapW Prod.fst)) T := by
  intro s c c' hq hs
  cases c with
  | run vs =>
    obtain ⟨b, its, m, ⟨w, n⟩⟩ := vs
    obtain ⟨k, d, hd, hq', ht⟩ := h n s _ _ hq (MStep.counted_proj hs)
    obtain ⟨c'', rfl, hc''⟩ := MStep.counted_lift hd
    exact ⟨k, c'', hc'', hq', ht⟩
  | ret => cases hs
  | halt => cases hs

end

/-- **The counted guarded semantics**: `csemV` with call number `n`'s external semantics `X.at n`. -/
noncomputable def csemVI (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSemI) : ISem CV (Arm.ArmState × Nat) :=
  ISem.counted fun n => csemV gv F ctx (X.at n)

/-- A step of `csemVI` is one of `csemI`. -/
theorem csemVI_sub {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSemI}
    {i : MInst} {uses : List CV} {w : Arm.ArmState × Nat}
    {r : List CV × (Arm.ArmState × Nat) × Ctl} (h : csemVI gv F ctx X i uses w = some r) :
    csemI F ctx X i uses w = some r := by
  obtain ⟨o, w', c⟩ := r
  obtain ⟨h1, h2⟩ := ISem.counted_some h
  obtain ⟨w'1, w'2⟩ := w'
  simp only at h1 h2
  subst h2
  rw [csemI_eq_counted]
  simp only [ISem.counted, csemV_sub h1, Option.map_some]

/-! ## The register-level theorem -/

/-- **The state after the prologue does not read the external semantics**: the prologue's lines
are not hooked, and from the ABI entry both machines run them as `execLines` (`iterN_steps`). -/
theorem RL.sP_withX {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (X : ExtSem) : ({ R with X := X } : RL).sP = R.sP := by
  have hR' : ({ R with X := X } : RL).Wf :=
    ⟨hR.check, hR.alloc, hR.emit, hR.layout, hR.lm, hR.fit, hR.stack, hR.psF, hR.prog0, hR.gfree⟩
  obtain ⟨-, hfs, -, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, -⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  have hins : ∀ ln ∈ prologueLines R.af.saves R.af.frameSize R.af.isCaller,
      ∃ x, ln = .ins x none ∧ x.hooked = false :=
    fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ _ ln h; exact ⟨x, e, hh⟩
  have h1 := (iterN_steps hR hdrop hins hent.program hpc1 hent.err hsteps).1
  have h2 := (iterN_steps (R := { R with X := X }) hR' hdrop hins hent.program hpc1 hent.err
    hsteps).1
  exact h2.trans h1.symm

/-- `StRel` does not read the external semantics (given the state after the prologue does not,
`RL.sP_withX`; `StRel.fplr` compares with the prologue's image `R.topImg`). -/
theorem StRel.withX {R : RL} {X : ExtSem} (hP : ({ R with X := X } : RL).sP = R.sP)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (h : StRel R s m w) : StRel { R with X := X } s m w :=
  ⟨h.store, h.world, h.err, h.prog, h.sp, h.align, fun hf => by
    show Arm.read_mem_bytes R.topN R.topB s =
      Arm.read_mem_bytes R.topN R.topB ({ R with X := X } : RL).sP
    rw [hP]; exact h.fplr hf, h.code, h.gkeep, h.fp⟩

theorem StRel.ofWithX {R : RL} {X : ExtSem} (hP : ({ R with X := X } : RL).sP = R.sP)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (h : StRel { R with X := X } s m w) : StRel R s m w :=
  ⟨h.store, h.world, h.err, h.prog, h.sp, h.align, fun hf => by
    show Arm.read_mem_bytes R.topN R.topB s = Arm.read_mem_bytes R.topN R.topB R.sP
    rw [← hP]; exact h.fplr hf, h.code, h.gkeep, h.fp⟩

/-- **The simulation relation does not read the external semantics** (given the state after the
prologue does not, `RL.sP_withX`). -/
theorem RL.Q_withX (R : RL) (X : ExtSem) (hP : ({ R with X := X } : RL).sP = R.sP)
    (s : Arm.ArmState) (c : MConf CV Arm.ArmState) :
    Q { R with X := X } s c ↔ Q R s c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    constructor
    · rintro ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      exact ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10.ofWithX hP⟩
    · rintro ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      exact ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10.withX hP⟩
  | ret => exact Iff.rfl
  | halt => exact Iff.rfl

/-- **`QA` does not read the external semantics** (given the state after the prologue does not,
`RL.sP_withX`). -/
theorem RL.QA_withX (R : RL) (X : ExtSem) (hP : ({ R with X := X } : RL).sP = R.sP)
    (s : Arm.ArmState) (c : MConf CV Arm.ArmState) :
    QA { R with X := X } s c ↔ QA R s c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    constructor
    · rintro (⟨hq, hA⟩ | ⟨mt, D, hq, hm, ht⟩)
      · exact .inl ⟨(RL.Q_withX R X hP s _).1 hq, hA⟩
      · exact .inr ⟨mt, D, (RL.Q_withX R X hP s _).1 hq, hm, ht⟩
    · rintro (⟨hq, hA⟩ | ⟨mt, D, hq, hm, ht⟩)
      · exact .inl ⟨(RL.Q_withX R X hP s _).2 hq, hA⟩
      · exact .inr ⟨mt, D, (RL.Q_withX R X hP s _).2 hq, hm, ht⟩
  | ret => exact Iff.rfl
  | halt => exact Iff.rfl

/-- **`regLevelCorrect_world_at` for the counted run** (`csemVI`, counter `0` at the body entry):
its returns and traps are realised by the machine, given the callee contracts of every index. -/
theorem regLevelCorrect_world_atI {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkG
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
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_init hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf (csemVI R.gv R.F R.ctx XI) ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) (w₀, 0) (hsel _)
  have hRz : Realizes R.vc R.rf (csemVI R.gv R.F R.ctx XI) ckeep R.step
      (fun u c => QA R u (c.mapW Prod.fst)) R.Good := by
    refine Realizes.counted (sem := fun n => csemV R.gv R.F R.ctx (XI.at n))
      (Q := fun u c => QA R u c) fun n => ?_
    have hq : ∀ u c, QA (Rn n) u c ↔ QA R u c := fun u c =>
      (RL.QA_withX (Rn n) (XI.at 0) (RL.sP_withX (hRn n) hent (XI.at 0)) u c).symm
    exact ((realizes_all (hRn n) (hC n) (fun h => hCT h n) (fun h => hTls h n) hcov).mono_T
      (T' := R.Good) fun _ h => h.good).congr_Q hq
  have hfin0 : ∀ n1 n2 n3, E2E.runX (ArmStepX (XI.at 0) H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun us vals w nc hret => ?_, fun c htr => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
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
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
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
          exact trace_add (fun j hj => (ht0 j hj).good)
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
            (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp)] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          by_cases hsv : Reg.v n ∈ R.af.saves
          · exact hsvd _ hsv
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
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨hsemV, -⟩ := ISem.counted_some hsem
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub hsemV)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc (csemVI R.gv R.F R.ctx XI) (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
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

/-- **`regLevelCorrect_world` for the counted run**: for the allocated, lowered, emitted and
laid-out function, the machine realises the returns and traps of the counted VCode run
(`csemVI`, counter `0` at the body entry) from any initial vreg file, given the callee contracts
of every call index. -/
theorem regLevelCorrect_worldI {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : ∀ n, CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n, CalleeTryOkG
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
  obtain ⟨_, h⟩ := regLevelCorrect_world_atI hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

end Backend.Proof

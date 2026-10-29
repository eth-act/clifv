import FV.E2E.RegLevelTrapCall
import FV.E2E.TrapCallTryStop

/-!
# The register level of a `try_call`'s callee trap (S9b, #375)

`regLevel_trapCall_value` (S9a) needs VCode without `tryCall`: a raising `tryCall` of the value
semantics with unwinding continues at its landing pad (`.goto 0`), which the machine without
unwinding does not realise. A callee trap only needs the VCode run **up to** the raising call;
here the semantics that halts there:

* `haltTry XR sem`: `sem`, but a `tryCall` whose callee raises (`XR`) halts; `star_haltTry`: a
  VCode run of `sem` is one of `haltTry XR sem`, or passes a raising `tryCall` (an earlier stop);
* `CallTrapAtT`: `CallTrapAt` at a call site of either kind (`CallSite`: a `call` or a
  `tryCall`; the plain call's facts, which a `tryCall` site has: `clobbers_tryCall`,
  `assign_call_tryCall`); `CallTrapAt.toT`;
* `realizes_haltTry`: the machine realises `haltTry` of a semantics with halting raising calls
  (no `tryCall`-free premise);
* `regLevel_trapCall_coreT`, `regLevel_trapCall_valueT`: `regLevel_trapCall_core`/`_value` with
  a third end, a raising `tryCall`, and without `vcp.hasTryCall = false`.
-/

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup

/-! ## Halting at a raising `tryCall` -/

/-- **`sem` halting at a raising `tryCall`** (callee raising under `XR`; the defs zero). -/
noncomputable def haltTry (XR : XRaise) (sem : Sem) : Sem := fun i uses w =>
  match i with
  | .tryCall info _ =>
    match XR.raise (callDest info) uses w with
    | some (_, w') => some ((defCons i).map (fun _ => ofX 0), w', .halt)
    | none => sem i uses w
  | _ => sem i uses w

theorem haltTry_noRaise {XR : XRaise} {sem : Sem} {i : MInst} {uses : List CV}
    {w : Arm.ArmState} (h : NoRaise XR i uses w) : haltTry XR sem i uses w = sem i uses w := by
  unfold haltTry
  split
  · rename_i info ti
    rw [h info (.inr ⟨ti, rfl⟩)]
  · rfl

theorem haltTry_not_try {XR : XRaise} {sem : Sem} {i : MInst} (h : ∀ info ti, i ≠ .tryCall info ti)
    (uses : List CV) (w : Arm.ArmState) : haltTry XR sem i uses w = sem i uses w := by
  unfold haltTry
  split
  · rename_i info ti
    exact absurd rfl (h info ti)
  · rfl

theorem haltTry_raise {XR : XRaise} {sem : Sem} {info : CallInfo} {ti : TryInfo}
    {uses : List CV} {w : Arm.ArmState} {obj : BitVec 64} {w' : Arm.ArmState}
    (h : XR.raise (callDest info) uses w = some (obj, w')) :
    haltTry XR sem (.tryCall info ti) uses w =
      some ((defCons (.tryCall info ti)).map (fun _ => ofX 0), w', .halt) := by
  simp [haltTry, h]

/-- **A VCode run of `sem` is one of `haltTry XR sem`, or passes a raising `tryCall`.** -/
theorem star_haltTry {vc : VCode} {sem : Sem} {XR : XRaise} {a b : VConf CV Arm.ArmState}
    (h : Star (VStep vc sem) a b) :
    Star (VStep vc (haltTry XR sem)) a b ∨ ∃ v, a = .run v ∧ VTryRaiseFrom vc (haltTry XR sem) XR v := by
  induction h with
  | refl => exact .inl (.refl _)
  | step h1 _ ih =>
    cases h1 with
    | @step b k ρ w vb i ops outs w' ctl c' hvb hi hops hsem hlen hn =>
      by_cases hr : ∃ info ti, i = .tryCall info ti ∧
          (XR.raise (callDest info) (vuses ops ρ) w).isSome
      · obtain ⟨info, ti, rfl, hraise⟩ := hr
        obtain ⟨⟨obj, w2⟩, hraise⟩ := Option.isSome_iff_exists.1 hraise
        exact .inr ⟨_, rfl, b, k, ρ, w, vb, info, ti, ops, obj, w2, .refl _, hvb, hi, hops, hraise⟩
      · have hsem' : haltTry XR sem i (vuses ops ρ) w = sem i (vuses ops ρ) w := by
          unfold haltTry
          split
          · rename_i info ti
            cases hx : XR.raise (callDest info) (vuses ops ρ) w with
            | none => rfl
            | some x => exact absurd ⟨info, ti, rfl, by rw [hx]; rfl⟩ hr
          · rfl
        have h1' := VStep.step (vc := vc) (sem := haltTry XR sem) hvb hi hops (hsem'.trans hsem)
          hlen hn
        rcases ih with h | ⟨v, rfl, hv⟩
        · exact .inl (.step h1' h)
        · exact .inr ⟨_, rfl, VTryRaiseFrom.prefix (.single h1') hv⟩

/-! ## The callee-trap state at a call site of either kind -/

/-- **The callee-trap state at a call site** (`CallTrapAt` with the site a `call` or a `tryCall`
of `vc`: `CallSite`). -/
def CallTrapAtT (vc : VCode) (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (fa : FnAsm) (base : BitVec 64) (X : ExtSem) (gv : Nat → String → Prop)
    (XT : Option String → List CV → Arm.ArmState → Prop) (u : Arm.ArmState) : Prop :=
  ∃ info : CallInfo, vc.CallSite info ∧
    K ≤ (spOf u).toNat ∧ (∀ a, StackBelow K (spOf u) a → F a) ∧
    (∀ a, G a → u.mem a = s0.mem a) ∧
    ∃ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState),
      (MInst.call info).operands = .ok ops ∧
      c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok () ∧
      (MInst.call info).assign regs = .ok i' ∧ CallAt fa base (Arm.r .PC u) i' ∧
      SameWorld F u w ∧ Arm.CheckSPAlignment u ∧ Arm.r .ERR u = .None ∧
      gotGuard gv X info (useVals ops regs u) ∧ XT (callDest info) (useVals ops regs u) w

theorem CallTrapAt.toT {vc : VCode} {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop}
    {s0 : Arm.ArmState} {fa : FnAsm} {base : BitVec 64} {X : ExtSem} {gv : Nat → String → Prop}
    {XT : Option String → List CV → Arm.ArmState → Prop} {u : Arm.ArmState}
    (h : CallTrapAt vc F K G s0 fa base X gv XT u) : CallTrapAtT vc F K G s0 fa base X gv XT u := by
  obtain ⟨info, ⟨b, vb, k, hvb, hk⟩, rest⟩ := h
  exact ⟨info, ⟨b, vb, k, hvb, .inl hk⟩, rest⟩

/-- The callee-trap state of the activation `R` at a call site of either kind. -/
def RL.CallTrapPreT (R : RL) (XT : Option String → List CV → Arm.ArmState → Prop)
    (u : Arm.ArmState) : Prop :=
  CallTrapAtT R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT u

/-! ## Realising the semantics with halting raising calls -/

/-- **A realisation transfers to `haltTry` of a semantics with halting raising calls**:
`semU` agrees with `sem₀` off the raising calls and halts at a raising `call`; `haltTry XR semU`
also halts at a raising `tryCall`. -/
theorem realizes_haltTry {R : RL} {sem₀ semU : Sem} {XR : XRaise}
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (QA R) R.GoodX)
    (hagree : ∀ i uses w, NoRaise XR i uses w → semU i uses w = sem₀ i uses w)
    (hcall : ∀ info uses w r obj w', semU (.call info) uses w = some r →
      XR.raise (callDest info) uses w = some (obj, w') → r.2.2 = .halt) :
    Realizes R.vc R.rf (haltTry XR semU) ckeep R.step (QA R) R.GoodX := by
  intro s c c' hqa hm
  have old : MStep R.vc sem₀ ckeep R.rf c c' →
      (∀ b k allocs its m w vb i ops, c = .run ⟨b, .op k allocs :: its, m, w⟩ →
        R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
        NoRaise XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w) →
      ∃ n c'', MStep R.vc (haltTry XR semU) ckeep R.rf c c'' ∧
        QA R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
    intro hm0 hnr
    obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s c c' hqa hm0
    exact ⟨n, c'', mstep_congr hm'' fun b k allocs its m w vb i ops hc hvb hi hops => by
      have h := hnr b k allocs its m w vb i ops hc hvb hi hops
      rw [haltTry_noRaise h, hagree _ _ _ h], hq'', ht⟩
  cases hm with
  | move =>
    exact old .move fun _ _ _ _ _ _ _ _ _ hc => by cases hc
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc (haltTry XR semU) ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    by_cases hr : NoRaise XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w
    · refine old (mstep_congr hstep fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_)
        fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact (haltTry_noRaise hr).trans (hagree _ _ _ hr)
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hr
    · simp only [NoRaise, Classical.not_forall] at hr
      obtain ⟨info, hik, hraise⟩ := hr
      obtain ⟨⟨obj, w2⟩, hraise⟩ := Option.ne_none_iff_exists'.mp hraise
      have hhalt : ctl = .halt := by
        rcases hik with rfl | ⟨ti, rfl⟩
        · rw [haltTry_not_try (fun _ _ h => by cases h)] at hsem
          exact hcall info _ w (outs, w', ctl) obj w2 hsem hraise
        · rw [haltTry_raise hraise] at hsem
          simp only [Option.some.injEq, Prod.mk.injEq] at hsem
          exact hsem.2.2.symm
      subst hhalt
      cases hn with
      | halt => exact ⟨0, _, hstep, .inl ⟨trivial, trivial⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
/-! ## The core -/

/-- **The register level of the explicit and the callee traps, `try_call`s included**
(`regLevel_trapCall_core` for a semantics `semU` that also halts at a raising `tryCall`): an
explicit trap of the VCode run is a trap site of the machine run, and a raising `call` or
`tryCall` (a callee that traps, `XT`) is a callee-trap state at a call site of either kind
(`RL.CallTrapPreT`), every earlier state `GoodX`. -/
theorem regLevel_trapCall_coreT {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    {XT : Option String → List CV → Arm.ArmState → Prop}
    (hgot : GotSem R.gv R.X semU)
    (hRz : Realizes R.vc R.rf semU ckeep R.step (QA R) R.GoodX)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem R.F R.ctx R.X i uses w = some (outs, w', .halt))
    (hhaltT : ∀ info ti uses w obj w', (xrT XT).raise (callDest info) uses w = some (obj, w') →
      semU (.tryCall info ti) uses w =
        some ((defCons (.tryCall info ti)).map (fun _ => ofX 0), w', .halt))
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ c, VTraps R.vc semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt R.fb R.base c (E2E.runX R.step n R.s0)) ∧
    (∀ obj w', VUnwinds R.vc semU (xrT XT) (ρsel m₀) w₀ obj w' →
      ∃ n, R.CallTrapPreT XT (E2E.runX R.step n R.s0) ∧
        ∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) ∧
    (VTryRaiseFrom R.vc semU (xrT XT) ⟨0, 0, ρsel m₀, w₀⟩ →
      ∃ n, R.CallTrapPreT XT (E2E.runX R.step n R.s0) ∧
        ∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) := by
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
        ∀ i < n, R.GoodX (E2E.runX R.step i R.s0) := by
    intro b k ρ w1 vb i info ops outs w' hstar hvb hi hops hik hraise hsem hlen
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
      have hq2 := (qa_op hq2 hvb hi (fun _ h => by rcases hik with rfl | ⟨_, rfl⟩ <;> cases h)).1
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      -- a forwarding block's only instruction is a `jump`, no (try) call: `Q` is `Qs`
      rcases Q.cases hq2 with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins,
        hasgf, -⟩
      rotate_left
      · rw [hvb] at hvbf
        cases hvbf
        simp only [RItem.op.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hi1 := hi
        rw [hins] at hi1
        simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
        subst hi1
        rcases hik with rfl | ⟨ti, rfl⟩
        · obtain ⟨ic, he'⟩ := (assign_call_tryCall info regsf).1 _ hasgf
          cases he'
        · obtain ⟨ic, he', -⟩ := (assign_call_tryCall info regsf).2 ti _ hasgf
          cases he'
      obtain ⟨-, vb0, items, pre, code, -, -, -, -, -, hvb0, hit, hsplit, hchk, hcode, -, -, -, -,
        -, hst, -, -⟩ := hqs
      rw [hvb] at hvb0; cases hvb0
      obtain ⟨cA, -, hc1, -, -⟩ := itemsCode_cons hcode
      obtain ⟨regs, i0, i', hal, hi0, hasg, -⟩ := itemCode_op hc1
      rw [hi] at hi0; cases hi0
      obtain ⟨cc', wh, i2, ops'', hi2, hops'', hstat, -⟩ := op_checked hchk
      rw [hi] at hi2; cases hi2
      rw [hops] at hops''; cases hops''
      subst hal
      have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal u r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      have hraise' : (xrT XT).raise (callDest info) (useVals ops regs u) w1 = some (0, w1) := by
        rw [← useVals_of_store hstat hm', hU0]
        exact hraise
      have hrun : E2E.runX R.step (n0 + n1 + n2) R.s0 = u := by
        rw [← hu, runX_eq]
        simp only [iterN_add]
      have htrace : ∀ i < n0 + n1 + n2, R.GoodX (E2E.runX R.step i R.s0) := fun i hi => by
        rw [runX_eq]
        exact trace_add ht0 (trace_add ht1 ht2) i (by omega)
      rcases hik with rfl | ⟨ti, rfl⟩
      · have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
          rw [← useVals_of_store hstat hm', hU0]
          exact (hgot _ _ _ _).1 hsem
        have hcpc := callAt_of_q hR hq2 hvb hi call_hcall regs i' rfl hasg
        refine ⟨n0 + n1 + n2, ?_, htrace⟩
        rw [hrun]
        exact ⟨info, ⟨b, vb, k, hvb, .inl hi⟩, by rw [hst.sp]; exact RL.K_le hR,
          fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs,
          i', w1, hops, hstat, hasg, hcpc, hst.world, hst.align, hst.err, hgg,
          (xrT_some hraise').1⟩
      · have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
          rw [← useVals_of_store hstat hm', hU0]
          exact (hgot _ _ _ _).2 ti hsem
        have hcpc := callAt_of_q hR hq2 hvb hi tryCall_hcall regs i' rfl hasg
        have hcl0 : ti.clobberAll = false := trySite_clobberAll hR.alloc ⟨b, vb, k, hvb, hi⟩
        obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
        refine ⟨n0 + n1 + n2, ?_, htrace⟩
        rw [hrun]
        exact ⟨info, ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩, by rw [hst.sp]; exact RL.K_le hR,
          fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs,
          .call ic, w1, by rw [← operands_tryCall_call info ti]; exact hops,
          by rw [← clobbers_tryCall hcl0]; exact hstat, hasg', callAt_tryCall_call hcpc,
          hst.world, hst.align, hst.err, hgg, (xrT_some hraise').1⟩
  refine ⟨locVal R.fr (iterN R.step n0 R.s0), fun c htr => ?_, fun obj w' hu => ?_, fun hu => ?_⟩
  · -- an explicit trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, -⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨hnil, hform⟩ :=
      csem_halt (hhalt _ _ _ _ _ (by rw [htc]; exact Option.some_ne_none _) hsem)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w⟩) (.halt w') :=
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
            obtain ⟨n3, htrap, -, -⟩ := trap_trapIf hR hq2 hvb hi hops' hholds
            exact ⟨n0 + n1 + n2 + n3, by rw [hfin]; exact htrap⟩
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
/-! ## The activation of a compiled function -/

/-- **The register level of the explicit and the callee traps for the backend's code under the
value semantics, `try_call`s included** (`regLevel_trapCall_value` without
`vcp.hasTryCall = false`): for the VCode run under `valueSemU` with the trapping callees
`xrT XT`, an explicit trap is a trap site of the machine run from the ABI entry or (the run
passing a raising `tryCall` first) a callee-trap state; a raising `call` or `tryCall` is a
callee-trap state at a call site of either kind (`CallTrapAtT`), every earlier state of the
activation `GoodX`. -/
theorem regLevel_trapCall_valueT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (XT : Option String → List CV → Arm.ArmState → Prop)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} (hent : AbiEntry fb base ra s)
    (hres : StackAvail K af s) (hbe : BodyEntry af s w₀) :
    ∃ ρ₀ : Nat → CV,
    let Fw := frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
    let semV := valueSemU Fw ⟨fa.k, af.slotBase⟩ X (xrT XT)
    let Stop := fun n => CallTrapAtT vcp Fw K (fun _ => False) s fa base X (fun _ _ => False) XT
        (E2E.runX (ArmStepX X H fa) n s) ∧
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K (fun _ => False) (fun _ _ => False)
        (E2E.runX (ArmStepX X H fa) i s)
    (∀ c, VTraps vcp semV ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∨ Stop n) ∧
    (∀ obj w', VUnwinds vcp semV (xrT XT) ρ₀ w₀ obj w' → ∃ n, Stop n) ∧
    (VTryRaiseFrom vcp semV (xrT XT) ⟨0, 0, ρ₀, w₀⟩ → ∃ n, Stop n) := by
  obtain ⟨cc, ins, a0, hat, hok⟩ := hcheck
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨p, hp, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, p.ps, K, fun _ => False, fun _ _ => False⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hat, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨p, hp, rfl⟩,
    hent.program, fun _ h => h.elim⟩
  have hF : R.F = frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s :=
    frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  have hCg : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv := by
    rw [hF]; exact (hC s).g _ s _ _
  have hreal := realizes_value_all hR hCg
    (fun _ => calleeTryOkG_of_call (fun ctx info ti hS => hCg.os ctx info hS.callSite)
      (fun _ _ _ h => callAt_tryCall_call h) (fun _ _ hS => trySite_clobberAll halloc hS))
    (by rw [hF]; exact fun h => hTls h s) hcov
  have hRz := realizes_haltTry (semU := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) hreal
    (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr])
  have hbe' : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀ := by
    rw [hF]
    exact hbe.w _ fun r ⟨_, _, hvb, hi, _, hv⟩ =>
      ((ctlCheck_args (lowerRFunc_ok halloc).2.2 hvb hi).2.2 _ hv).2
  have hgot : GotSem R.gv R.X (haltTry (xrT XT) (valueSemVU R.gv R.F R.ctx R.X (xrT XT))) :=
    fun _ _ _ _ => ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim⟩
  have hnt : ∀ i, trapCode? i ≠ none → ∀ info ti, i ≠ .tryCall info ti := by
    intro i ht info ti e; subst e; simp [trapCode?] at ht
  obtain ⟨m₀, h1, h2, h3⟩ := regLevel_trapCall_coreT (XT := XT) hR hent.toCall hat hgot hRz
    (fun i _ _ _ _ ht h => valueSemVU_halt_trap ht (by rwa [haltTry_not_try (hnt i ht)] at h))
    (fun _ _ _ _ _ _ h => haltTry_raise h) hbe' (entryRho a0) (Inv_entryRho ckeep hok)
  have e1 : valueSemVU R.gv R.F R.ctx R.X (xrT XT) =
      valueSemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X (xrT XT) := by
    rw [hF]
    exact valueSemVU_bot _ _ _ _
  have hstop : ∀ n, R.CallTrapPreT XT (E2E.runX R.step n R.s0) →
      (∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) →
      CallTrapAtT vcp (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
          af s) K (fun _ => False) s fa base X (fun _ _ => False) XT
          (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K (fun _ => False) (fun _ _ => False)
          (E2E.runX (ArmStepX X H fa) i s) := by
    intro n hct ht
    refine ⟨?_, fun i hi => (ht i hi).act⟩
    have hct' : CallTrapAtT R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT
        (E2E.runX R.step n R.s0) := hct
    rw [hF] at hct'
    exact hct'
  -- an earlier raising `tryCall` on the way
  have hearly : ∀ v, (VConf.run ⟨0, 0, entryRho a0 m₀, w₀⟩ : VConf CV Arm.ArmState) = .run v →
      VTryRaiseFrom R.vc (haltTry (xrT XT) (valueSemVU R.gv R.F R.ctx R.X (xrT XT))) (xrT XT) v →
      ∃ n, R.CallTrapPreT XT (E2E.runX R.step n R.s0) ∧
        ∀ i < n, R.GoodX (E2E.runX R.step i R.s0) := by
    intro v hv htr
    cases hv
    exact h3 htr
  refine ⟨entryRho a0 m₀, fun c htr => ?_, fun obj w' hu => ?_, fun hu => ?_⟩
  · rw [← e1] at htr
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    rcases star_haltTry (XR := xrT XT) hstar with hs | ⟨v, hv, hT⟩
    · have hsem' := (haltTry_not_try (XR := xrT XT)
        (sem := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) (hnt i (by rw [htc]; simp)) _ _).trans hsem
      exact (h1 c ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem', htc⟩).imp
        fun _ h => .inl h
    · obtain ⟨n, hct, ht⟩ := hearly v hv hT
      exact ⟨n, .inr (hstop n hct ht)⟩
  · rw [← e1] at hu
    obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
    rcases star_haltTry (XR := xrT XT) hstar with hs | ⟨v, hv, hT⟩
    · have hsem' := (haltTry_not_try (XR := xrT XT)
        (sem := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) (i := .call info)
        (fun _ _ h => by cases h) _ _).trans hsem
      obtain ⟨n, hct, ht⟩ :=
        h2 obj w' ⟨b, k, ρ, w1, vb, info, ops, outs, hs, hvb, hi, hops, hraise, hsem', hlen⟩
      exact ⟨n, hstop n hct ht⟩
    · obtain ⟨n, hct, ht⟩ := hearly v hv hT
      exact ⟨n, hstop n hct ht⟩
  · rw [← e1] at hu
    obtain ⟨b, k, ρ, w1, vb, info, ti, ops, obj, w', hstar, hvb, hi, hops, hraise⟩ := hu
    rcases star_haltTry (XR := xrT XT) hstar with hs | ⟨v, hv, hT⟩
    · obtain ⟨n, hct, ht⟩ :=
        h3 ⟨b, k, ρ, w1, vb, info, ti, ops, obj, w', hs, hvb, hi, hops, hraise⟩
      exact ⟨n, hstop n hct ht⟩
    · obtain ⟨n, hct, ht⟩ := hearly v hv hT
      exact ⟨n, hstop n hct ht⟩

end Backend.Proof

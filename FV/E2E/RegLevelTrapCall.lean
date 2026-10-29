module

public import FV.E2E.RegLevelCorrectU
public import FV.E2E.UnwindValueSem

@[expose] public section

/-!
# The register level of a callee trap (S9a, #33)

A callee trap reaches the register level as an exceptional end of the VCode run under the value
semantics with unwinding (`valueSemU`) whose raising callees are the **trapping** ones
(`xrT XT`: a call raises exactly when its callee traps, `XT`): a `call` that ends the
activation (`VUnwinds`). On the machine **without** unwinding (`ArmStepX`), that is a state at
the call line whose callee traps — the callee contract's premises hold there as at every call
(`CallTrapAt`, `RL.CallPre`'s facts with the trapping callee instead of a returning one).

* `xrT`, `xrT_some`, `xrT_of`: the raising semantics of the trapping callees.
* `CallTrapAt`: **the callee-trap state** of an activation; `RL.CallTrapPre`.
* `realizes_trapT`: a realisation of a semantics `sem₀` by the machine is one of a semantics
  that agrees with it off the raising calls and halts at a raising `call`, for VCode without
  `tryCall`.
* `regLevel_trapCall_core`: an explicit trap of the VCode run is a trap site of the machine run
  (as in `regLevelCorrect_world_atX`); an exceptional end is a callee-trap state, every earlier
  state of the run `GoodX`.
* `regLevel_trapCall_value`: the activation of a compiled function under the dead-cleanup
  chain's value semantics (no kept addresses, no GOT pinning).
-/

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup

/-! ## The trapping callees as raising callees -/

open Classical in
/-- **The raising semantics of the trapping callees `XT`**: a call raises (object `0`, world
unchanged) exactly when its callee traps. -/
noncomputable def xrT (XT : Option String → List CV → Arm.ArmState → Prop) : XRaise :=
  ⟨fun d uses w => if XT d uses w then some (0, w) else none⟩

theorem xrT_some {XT : Option String → List CV → Arm.ArmState → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {obj : BitVec 64} {w' : Arm.ArmState}
    (h : (xrT XT).raise d uses w = some (obj, w')) : XT d uses w ∧ obj = 0 ∧ w' = w := by
  simp only [xrT] at h
  split at h
  · rename_i hx
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hx, h.1.symm, h.2.symm⟩
  · cases h

theorem xrT_of {XT : Option String → List CV → Arm.ArmState → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} (h : XT d uses w) : (xrT XT).raise d uses w = some (0, w) := by
  simp [xrT, h]

theorem xrT_none {XT : Option String → List CV → Arm.ArmState → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} (h : ¬ XT d uses w) : (xrT XT).raise d uses w = none := by
  simp [xrT, h]

/-! ## The callee-trap state -/

/-- **The callee-trap state of an activation** (VCode `vc`, addresses `F` outside its world,
callees' stack budget `K`, kept addresses `G` of the activation entered in `s0`, code `fa` at
`base`, callee semantics `X`, GOT pins `gv`): the pc is at the call line of a `call` of `vc`,
the callee contract's premises hold (as `RL.CallPre`: the dead stack below `sp`, the kept
addresses, the operand checks, the world `w`, an aligned `sp`, no error, the GOT guard) and the
callee traps (`XT`) on the call's operand values and `w`. -/
def CallTrapAt (vc : VCode) (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (fa : FnAsm) (base : BitVec 64) (X : ExtSem) (gv : Nat → String → Prop)
    (XT : Option String → List CV → Arm.ArmState → Prop) (u : Arm.ArmState) : Prop :=
  ∃ info : CallInfo, (∃ (b : Nat) (vb : VBlock) (k : Nat), vc.blocks[b]? = some vb ∧
      vb.insts[k]? = some (MInst.call info)) ∧
    K ≤ (spOf u).toNat ∧ (∀ a, StackBelow K (spOf u) a → F a) ∧
    (∀ a, G a → u.mem a = s0.mem a) ∧
    ∃ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState),
      (MInst.call info).operands = .ok ops ∧
      c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok () ∧
      (MInst.call info).assign regs = .ok i' ∧ CallAt fa base (Arm.r .PC u) i' ∧
      SameWorld F u w ∧ Arm.CheckSPAlignment u ∧ Arm.r .ERR u = .None ∧
      gotGuard gv X info (useVals ops regs u) ∧ XT (callDest info) (useVals ops regs u) w

/-- The callee-trap state of the activation `R`. -/
def RL.CallTrapPre (R : RL) (XT : Option String → List CV → Arm.ArmState → Prop)
    (u : Arm.ArmState) : Prop :=
  CallTrapAt R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT u

/-! ## Realising the semantics with the trapping callees -/

/-- **A realisation transfers to a semantics with halting calls**: `semU` agrees with `sem₀` off
the raising calls and halts at a raising `call`; the VCode has no `tryCall`. The machine is
unchanged (the activation's run stops at a raising call). -/
theorem realizes_trapT {R : RL} {sem₀ semU : Sem} {XR : XRaise}
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (fun s c => Q R s c ∧ AInv R c) R.GoodX)
    (hagree : ∀ i uses w, NoRaise XR i uses w → semU i uses w = sem₀ i uses w)
    (hcall : ∀ info uses w r obj w', semU (.call info) uses w = some r →
      XR.raise (callDest info) uses w = some (obj, w') → r.2.2 = .halt)
    (hnt : R.vc.hasTryCall = false) :
    Realizes R.vc R.rf semU ckeep R.step (fun s c => Q R s c ∧ AInv R c) R.GoodX := by
  intro s c c' ⟨hq, hA⟩ hm
  have old : MStep R.vc sem₀ ckeep R.rf c c' →
      (∀ b k allocs its m w vb i ops, c = .run ⟨b, .op k allocs :: its, m, w⟩ →
        R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
        NoRaise XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w) →
      ∃ n c'', MStep R.vc semU ckeep R.rf c c'' ∧
        (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
    intro hm0 hnr
    obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s c c' ⟨hq, hA⟩ hm0
    exact ⟨n, c'', mstep_congr hm'' fun b k allocs its m w vb i ops hc hvb hi hops =>
      (hagree _ _ _ (hnr b k allocs its m w vb i ops hc hvb hi hops)).symm, hq'', ht⟩
  cases hm with
  | move =>
    exact old .move fun _ _ _ _ _ _ _ _ _ hc => by cases hc
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc semU ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    by_cases hr : NoRaise XR i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w
    · refine old (mstep_congr hstep fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_)
        fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hagree _ _ _ hr
      · cases hc
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hr
    · simp only [NoRaise, Classical.not_forall] at hr
      obtain ⟨info, hik, hraise⟩ := hr
      obtain ⟨⟨obj, w2⟩, hraise⟩ := Option.ne_none_iff_exists'.mp hraise
      rcases hik with rfl | ⟨ti, rfl⟩
      · have hc := hcall info _ w (outs, w', ctl) obj w2 hsem hraise
        simp only at hc
        subst hc
        cases hn with
        | halt => exact ⟨0, _, hstep, ⟨trivial, trivial⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · have := hasTryCall_of_mem hvb hi
        rw [hnt] at this; cases this

/-! ## The core -/

/-- **The register level of the explicit and the callee traps**: for a semantics `semU` that the
machine realises (`hRz`) and that agrees with `csem` at the trapping instructions, an explicit
trap of the VCode run is a trap site of the machine run, and an exceptional end under the
trapping callees `xrT XT` (a `call` whose callee traps) is a callee-trap state of the machine
run (`RL.CallTrapPre`), every earlier state `GoodX`. -/
theorem regLevel_trapCall_core {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    {XT : Option String → List CV → Arm.ArmState → Prop}
    (hgot : GotSem R.gv R.X semU)
    (hRz : Realizes R.vc R.rf semU ckeep R.step (fun s c => Q R s c ∧ AInv R c) R.GoodX)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem R.F R.ctx R.X i uses w = some (outs, w', .halt))
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ c, VTraps R.vc semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt R.fb R.base c (E2E.runX R.step n R.s0)) ∧
    (∀ obj w', VUnwinds R.vc semU (xrT XT) (ρsel m₀) w₀ obj w' →
      ∃ n, R.CallTrapPre XT (E2E.runX R.step n R.s0) ∧
        ∀ i < n, R.GoodX (E2E.runX R.step i R.s0)) := by
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_init hR hent hbe
  obtain ⟨hSim, hinit, -⟩ := checkedAt_sound_match (sem := semU) (keep := ckeep) hcheck
    (locVal R.fr (iterN R.step n0 R.s0)) (ρsel (locVal R.fr (iterN R.step n0 R.s0))) w₀ (hsel _)
  have hfin : ∀ n1 n2 n3, E2E.runX R.step (n0 + n1 + n2 + n3) R.s0 =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 R.s0))) := by
    intro n1 n2 n3
    rw [runX_eq]
    simp only [iterN_add]
  refine ⟨locVal R.fr (iterN R.step n0 R.s0), fun c htr => ?_, fun obj w' hu => ?_⟩
  · -- an explicit trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, -⟩ := forward hSim hRz hstar hinit ⟨hq0, hA0⟩
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
  · -- an exceptional end: a `call` whose callee traps
    obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨hq0, hA0⟩
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w1⟩) (.halt w') :=
      VStep.step hvb hi hops hsem hlen VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, ht2⟩ :=
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
      -- the allocated code reads the VCode's uses: the same trapping callee
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      obtain ⟨j0, items, pre, regs, i', cA, cB, ls1, ls2, ps1, psm, ps2, T', cc', wh, ops'', hal, hit,
        hsplit, hasg, hc1', hops'', hstat, hchk', hcode2, h1', h2', htr', hdrop, hpc, hst⟩ :=
        q_op hq2 hvb hi
      rw [hops] at hops''; cases hops''
      subst hal
      have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal u r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      have hraise' : (xrT XT).raise (callDest info) (useVals ops regs u) w1 = some (obj, w') := by
        rw [← useVals_of_store hstat hm', hU0]
        exact hraise
      have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
        rw [← useVals_of_store hstat hm', hU0]
        exact (hgot _ _ _ _).1 hsem
      have hcpc := callAt_of_q hq2 hvb hi call_hcall regs i' rfl hasg
      have hrun : E2E.runX R.step (n0 + n1 + n2) R.s0 = u := by
        rw [← hu, runX_eq]
        simp only [iterN_add]
      refine ⟨n0 + n1 + n2, ?_, fun i hi => ?_⟩
      · rw [hrun]
        exact ⟨info, ⟨b, vb, k, hvb, hi⟩, by rw [hst.sp]; exact RL.K_le hR,
          fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs,
          i', w1, hops, hstat, hasg, hcpc, hst.world, hst.align, hst.err, hgg,
          (xrT_some hraise').1⟩
      · rw [runX_eq]
        exact trace_add ht0 (trace_add ht1 ht2) i (by omega)

/-! ## The activation of a compiled function -/

/-- **The register level of the explicit and the callee traps for the backend's code under the
value semantics** (`regLevelCorrect_backend_ex_value`'s counterpart; an `AllocChecked`
allocation, a function without `try_call`s, no kept addresses, no GOT pinning): for the VCode
run under `valueSemU` with the trapping callees `xrT XT`, an explicit trap is a trap site of the
machine run from the ABI entry, an exceptional end is a callee-trap state (`CallTrapAt`), every
earlier state of the activation `GoodX` (`actGoodX`). -/
theorem regLevel_trapCall_value {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hnt : vcp.hasTryCall = false) (XT : Option String → List CV → Arm.ArmState → Prop)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} (hent : AbiEntry fb base ra s)
    (hres : StackAvail K af s) (hbe : BodyEntry af s w₀) :
    ∃ ρ₀ : Nat → CV,
    (∀ c, VTraps vcp (valueSemU (frameW K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af s) ⟨fa.k, af.slotBase⟩ X (xrT XT)) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s)) ∧
    (∀ obj w', VUnwinds vcp (valueSemU (frameW K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af s) ⟨fa.k, af.slotBase⟩ X (xrT XT)) (xrT XT) ρ₀ w₀ obj w' →
      ∃ n, CallTrapAt vcp (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
          af s) K (fun _ => False) s fa base X (fun _ _ => False) XT
          (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K (fun _ => False) (fun _ _ => False)
          (E2E.runX (ArmStepX X H fa) i s)) := by
  obtain ⟨cc, ins, a0, hat, hok⟩ := hcheck
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hat, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩,
    hent.program, fun _ h => h.elim⟩
  have hF : R.F = frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s :=
    frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  have hreal := realizes_value_all hR (by rw [hF]; exact (hC s).g _ s _ _)
    (fun h => by rw [show R.vc = vcp from rfl, hnt] at h; cases h)
    (by rw [hF]; exact fun h => hTls h s) hcov
  have hRz := realizes_trapT (semU := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) hreal
    (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr]) hnt
  have hbe' : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀ := by
    rw [hF]
    exact hbe.w _ fun r ⟨_, _, hvb, hi, _, hv⟩ =>
      ((ctlCheck_args (lowerRFunc_ok halloc).2.2 hvb hi).2.2 _ hv).2
  obtain ⟨m₀, h1, h2⟩ := regLevel_trapCall_core (XT := XT) hR hent.toCall hat
    (gotSem_valueSemVU _ _ _ _ _) hRz (fun _ _ _ _ _ ht h => valueSemVU_halt_trap ht h) hbe'
    (entryRho a0) (Inv_entryRho ckeep hok)
  have e1 : valueSemVU R.gv R.F R.ctx R.X (xrT XT) =
      valueSemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X (xrT XT) := by
    rw [hF]
    exact valueSemVU_bot _ _ _ _
  refine ⟨entryRho a0 m₀, fun c htr => ?_, fun obj w' hu => ?_⟩
  · rw [← e1] at htr
    exact h1 c htr
  · rw [← e1] at hu
    obtain ⟨n, hct, ht⟩ := h2 obj w' hu
    refine ⟨n, ?_, fun i hi => (ht i hi).act⟩
    have hct' : CallTrapAt R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT
        (E2E.runX R.step n R.s0) := hct
    rw [hF] at hct'
    exact hct'

end Backend.Proof

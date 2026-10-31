import FV.Concurrency.CallRetsN
import FV.Concurrency.CallSeg
import FV.Concurrency.CallResume

/-!
# All layers from an activation's ABI entry, pausing at calls and returns (#473, step (4))

`CallRetsN.arm_isel_refines_entryCRN` starts the Arm run after the prologue. A callee entered by
the caller's `bl` starts at its ABI entry `RA.s0`, so the activation's first segment for
`CallComposeT.SegOkG` runs the prologue first:

* **`arm_isel_refines_abiCRN`**: every precise run of a machine `g` agreeing with the activation
  (`AgreesAt`) from the ABI entry is realized entirely, up to where the CLIF thread stops, up to a
  call with the three relations, or up to a done `return` with its contract `RetEnd`; the
  prologue's events are private plain writes refined by no CLIF step
  (`ArmAllocEntry.prun_prologue` on the agreeing machine: `CallSeg.prun_privF`,
  `CallSeg.linesAt_nonRet`), composed with `arm_isel_refines_entryCRN` by
  `CallCompose.Refines.app`.
-/

namespace Concurrency.CallSegAbi

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ThreadCompose IselCall IselCallRet CallRets CallRetsAlloc ArmAllocThread E2E IselStep
  CallLayers CallRetsEnd CallRetsN

/-- **The checker's entry values after the prologue** are the ABI entry's on the registers the
prologue pushes (it keeps the callee-saved registers): `rets_alloc`'s `hr₀`. -/
theorem hr₀_init {RA : RL} (hR : RA.Wf) {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
    {m₀ : Loc → CV} {w₀ : ArmState}
    (hq : Q RA (iterN RA.step (prologueLines RA.af.saves RA.af.frameSize RA.af.isCaller).length RA.s0)
      (MConf.init RA.rf m₀ w₀)) :
    ∀ r ∈ RA.af.saves, ckeep r (m₀ (.reg r)) = ckeep r (regVal RA.s0 r) := by
  obtain ⟨-, -, -, hsv, -⟩ := RL.frame_facts hR
  intro r hr
  have hcs := hsv.1 r hr
  simp only [MConf.init] at hq
  have hst := q_stRel hq
  rw [hst.store (.reg r) (fun r' e => by cases e; exact CallResumeL.calleeSaved_allocatable r hcs)
    trivial]
  simp only [locVal]
  rw [regVal_calleeSaved_congr (fun f h1 h2 h3 h4 h5 => prologue_fields hR hent f h1 h3 h5 h2) r hcs]

/-- **The prologue on an agreeing machine**: through the prologue's lines a precise run of `g`
under `OkPriv` is the single-core path, its events private plain writes. (#581: `hpf`
(`ProbeF`) is new: the stack probes' writes are private only when the probed bytes are in
`RA.F`.) -/
theorem prun_prologueG {RA : RL} (hR : RA.Wf) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0) (hpf : ProbeF RA) {mon : Mon}
    {L : List Lab}
    {t1 : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (RA.s0, mon) L t1)
    (hL : L.length ≤ (prologueLines RA.af.saves RA.af.frameSize RA.af.isCaller).length) :
    t1.1 = iterN RA.step L.length RA.s0 ∧ PrivW (PrivA RA) (evTr L) ∧
      ∀ p y, evAt (evTr L) p = some y → y.k = .plainW := by
  have hlat := prologue_linesAt hR hent
  have hpe := prologue_evs hR hent hpf hlat
  have hnr := CallSeg.linesAt_nonRet hR hlat (CallSeg.noRet_prologue _ _ _)
  obtain ⟨h1, hev, -⟩ := CallSeg.prun_privF hr fun i hi =>
    ⟨fun e he => ((hpe i (by omega)).1 e he).1, (hpe i (by omega)).2,
      hg _ (CallSeg.linesAt_program hR hlat i (by omega)) (hnr i (by omega))⟩
  refine ⟨h1, ?_, ?_⟩
  · rw [hev]
    exact privW_segEvs (fun i hi e he => ((hpe i (by omega)).1 e he).1)
      fun i hi => stepEvs_noRelXW (hpe i (by omega)).2
  · intro p y hy
    rw [hev] at hy
    obtain ⟨j, k⟩ := p
    simp only [evAt] at hy
    cases hj : (segEvs RA.step L.length RA.s0)[j]? with
    | none => rw [hj] at hy; cases hy
    | some x =>
      rw [hj] at hy
      simp only [Option.bind_some] at hy
      obtain ⟨i, hi, rfl⟩ := mem_segEvs (List.mem_of_getElem? hj)
      exact ((hpe i (by omega)).1 y (List.mem_of_getElem? hy)).2

/-- **All layers from the ABI entry, pausing at calls and at returns with their contract**
(module doc), the realized prefix exclusive-closed (the prologue has no `relXW`,
`arm_isel_refines_entryCRNX`). (#581: `hpf` (`ProbeF`) is new: the prologue's stack probes
refine no CLIF step only when the probed bytes are private.) -/
theorem arm_isel_refines_abiCRNX {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0) (hpf : ProbeF RA)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat}
    {syms : String → Option Nat}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk RA.F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    (hMem : MemRefines RA.F sb syms (csem RA.F RA.ctx RA.X)) (hMRs : MRStable RA.F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    (hm3 : ∀ (ρ₀ : Nat → CV) (w₀ : ArmState), PMatch vc RA.vc (csem RA.F RA.ctx RA.X)
      (cEvs RA.F RA.ctx) L ss' (VConf.init ρ₀ w₀) (VConf.init ρ₀ w₀))
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0)
    (hm4 : ∀ (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState),
      Backend.Proof.Match cc ins ckeep (fun r => m₀ (.reg r)) (MConf.init RA.rf m₀ w₀)
        (VConf.init ρ₀ w₀))
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {m₀ : Loc → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry RA.F f.sig args w₀)
    (hq : Q RA (iterN RA.step (prologueLines RA.af.saves RA.af.frameSize RA.af.isCaller).length RA.s0)
      (MConf.init RA.rf m₀ w₀)) (hA : AInv RA (MConf.init RA.rf m₀ w₀)) {mon : Mon}
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (RA.s0, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (RA.s0, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep (fun r => m₀ (.reg r)) cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (RA.s0, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots (fun r => m₀ (.reg r)) tE.1 s')) := by
  have hr₀ := hr₀_init hR hent hq
  generalize hP : (prologueLines RA.af.saves RA.af.frameSize RA.af.isCaller).length = P at hq
  have hpp : ∀ {L : List Lab} {t1 : ArmState × Mon},
      PRun Policy.arm g (OkPriv RA) (RA.s0, mon) L t1 → L.length ≤ P →
      t1.1 = iterN RA.step L.length RA.s0 ∧ PrivW (PrivA RA) (evTr L) ∧
        ∀ p y, evAt (evTr L) p = some y → y.k = .plainW :=
    fun h hL => prun_prologueG hR hg hent hpf h (hP ▸ hL)
  by_cases hle : ls.length ≤ P
  · obtain ⟨-, hpw, hpk0⟩ := hpp hr hle
    refine ⟨ls.length, [], _, id, Nat.le_refl _, ?_, .nil, ?_, .inl rfl⟩
    · rw [List.take_length]
      exact CallCompose.xClosed_of fun b y hy => by rw [hpk0 b y hy]; decide
    rw [List.take_length]
    exact refines_privW hpw
  · obtain ⟨v, hv, hrest⟩ := CallCompose.take_prun hr P
    have hPl : (ls.take P).length = P := by simp; omega
    obtain ⟨hv1, hpw, hpk⟩ := hpp hv (by omega)
    rw [hPl] at hv1
    obtain ⟨v1, vm⟩ := v
    simp only at hv1
    subst hv1
    obtain ⟨k2, trS, t, ψ2, hk2, hx2, hrun, href, hend⟩ := arm_isel_refines_entryCRNX hR hsc hgv hg hent
      H hchk hMR hMRw hX hX0 hMem hMRs hreg H3 hm3 hc hm4 hB0 hcall hfunc hslots hbody hterm hregs
      hty hsig hmr hr₀ hargs hq hA hrest
    have e : ∀ n, evTr (ls.take (P + n)) = evTr (ls.take P) ++ evTr ((ls.drop P).take n) := by
      intro n; rw [List.take_add, evTr_append]
    have etake : ∀ n, ls.take (P + n) = ls.take P ++ (ls.drop P).take n := fun n => List.take_add ..
    refine ⟨P + k2, trS, t, CallCompose.appMap 0 (evTr (ls.take P)).length id ψ2,
      by simp at hk2; omega, ?_, hrun, ?_, ?_⟩
    · rw [e]
      exact (CallCompose.xClosed_of fun b y hy => by rw [hpk b y hy]; decide).append hx2
    · rw [e]
      have := CallCompose.Refines.app (refines_privW (MK := Maps) hpw) href
        (.inr fun a x hx hk => by rw [hpk a x hx] at hk; cases hk)
      simpa using this
    · rcases hend with h | h | ⟨tE, s', vV', vP', cM', hpr, h2⟩ | ⟨tE, s', hpr, h2⟩
      · left; simp at h; omega
      · exact .inr (.inl h)
      · refine .inr (.inr (.inl ⟨tE, s', vV', vP', cM', ?_, h2⟩))
        rw [etake]; exact hv.append hpr
      · refine .inr (.inr (.inr ⟨tE, s', ?_, h2⟩))
        rw [etake]; exact hv.append hpr

/-- **All layers from the ABI entry, pausing at calls and returns with their contract**
(module doc; `arm_isel_refines_abiCRNX` without its exclusive-closed prefix). (#581: `hpf`
(`ProbeF`) is new: the prologue's stack probes refine no CLIF step only when the probed bytes are
private.) -/
theorem arm_isel_refines_abiCRN {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0) (hpf : ProbeF RA)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat}
    {syms : String → Option Nat}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk RA.F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    (hMem : MemRefines RA.F sb syms (csem RA.F RA.ctx RA.X)) (hMRs : MRStable RA.F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    (hm3 : ∀ (ρ₀ : Nat → CV) (w₀ : ArmState), PMatch vc RA.vc (csem RA.F RA.ctx RA.X)
      (cEvs RA.F RA.ctx) L ss' (VConf.init ρ₀ w₀) (VConf.init ρ₀ w₀))
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0)
    (hm4 : ∀ (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState),
      Backend.Proof.Match cc ins ckeep (fun r => m₀ (.reg r)) (MConf.init RA.rf m₀ w₀)
        (VConf.init ρ₀ w₀))
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {m₀ : Loc → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry RA.F f.sig args w₀)
    (hq : Q RA (iterN RA.step (prologueLines RA.af.saves RA.af.frameSize RA.af.isCaller).length RA.s0)
      (MConf.init RA.rf m₀ w₀)) (hA : AInv RA (MConf.init RA.rf m₀ w₀)) {mon : Mon}
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (RA.s0, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (RA.s0, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep (fun r => m₀ (.reg r)) cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (RA.s0, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots (fun r => m₀ (.reg r)) tE.1 s')) := by
  obtain ⟨k, trS, t, ψ, hk, -, h⟩ := arm_isel_refines_abiCRNX hR hsc hgv hg hent hpf H hchk hMR hMRw
    hX hX0 hMem hMRs hreg H3 hm3 hc hm4 hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs
    hq hA hr
  exact ⟨k, trS, t, ψ, hk, h⟩

end Concurrency.CallSegAbi

import FV.Concurrency.IselCall
import FV.Concurrency.ThreadCompose
import FV.Concurrency.ThreadProgress
import FV.Concurrency.RealizeCompiled
import FV.Concurrency.ArmAllocLinked

/-!
# Layers 2, 3 and 4a from related configurations, pausing at calls (#473, (3))

`ThreadCompose.isel_alloc_refinesR` composes layers 2–4a from the entry configurations, through
the traces (`Thin`) and without the relations at the end. A segment of an activation with calls
starts at related configurations (its entry, or after a call's return,
`CallResumeL.resume_layers`) and, where it pauses at a call, must end at related configurations
again (the callee's entry and the caller's resume start from them). So:

* **`isel_alloc_refinesC`**: from the CLIF state matched by layer 2 (`Driver.Match`) to a VCode
  configuration that `prepare`'s relation (`PMatch`) and the allocation checker's (`MatchRun`)
  relate to an allocated configuration, a run of the allocated code (`MTRun`) is realized
  (`Refines Maps`, no private location) on a prefix: the whole run with a step of the allocated
  code at its end (`MStep`) or ending where the CLIF thread stops, a CLIF thread that returned
  realizing the whole run (as `isel_alloc_refinesR`); or, with an external semantics without
  `call` step (`IselCall.NoCall`), **the whole run, ending at a call statement whose CLIF state
  is related to the run's last configuration by all three relations** (`prep_run`, `alloc_run`,
  `IselCall.isel_refinesC`, `match_atCall`, `vtrun_atCall`);
* `CoveredCodeC`/`srcStep_of_mstepC`: `ThreadProgress.CoveredCode`/`srcStep_of_mstep` admitting
  calls, whose allocated item has no step when the external semantics has none;
* **`arm_isel_refinesC`** (all layers, on a linked machine agreeing with the activation's step
  at its lines other than `ret`, `ArmAllocLinked.AgreesAt`): from `Q ∧ AInv` and the three
  relations at a segment's start, every precise run under `OkPriv` realizes (`Refines Maps`,
  private set `PrivA`) a CLIF thread run on a prefix: the whole run, or ending where the CLIF
  thread stops, or ending (all of layer 4b's prefix) at a state related by `RelQ` to the
  allocated code at a `call` item, the CLIF state at the call statement related to it by the
  three relations, or at a `rets` item (with layer 2's end there).
-/

namespace Concurrency.CallLayers

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ThreadCompose IselCall

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **Layers 2, 3 and 4a from related configurations, pausing at calls** (module doc). -/
theorem isel_alloc_refinesC (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hX0 : NoCall X)
    {vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc vcp L ss ss')
    {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt vcp rf c ins a0) {keep : Reg → CV → CV} {r₀ : Reg → CV}
    {s : Clif.State} {vV vP : VState CV ArmState} {cM : MState CV ArmState}
    (hm2 : Match f ctx R gn bl A MR slots s vV)
    (hm3 : PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' (.run vV) (.run vP))
    (hm4 : MatchRun c ins keep r₀ cM vP)
    {trM : List (List Ev)} {cE : MConf CV ArmState}
    (hr : MTRun vcp rf (csem F fc X) keep (cEvs F fc) (.run cM) trM cE) :
    ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
      ((((m = trM.length ∧ ∃ cM', MStep vcp (csem F fc X) keep rf cE cM') ∨ Stop env p t) ∧
          ∀ v, t = .ret v → m = trM.length) ∨
        (m = trM.length ∧ ∃ s' vV' vP' cM', t = .run s' ∧ AtCallS s' ∧ cE = .run cM' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' (.run vV') (.run vP') ∧
          MatchRun c ins keep r₀ cM' vP')) := by
  have hds := (driverSem_csem F fc X).toDriverSemG
  obtain ⟨trP, vPE, hrP, hmE, hthP⟩ := alloc_run (r₀ := r₀) hc hr (v := .run vP) hm4
  obtain ⟨trV, vVE, hrV, hpE, hthV⟩ := prep_run H3 hds (fun _ _ _ h => cEvs_setTargets F fc h)
    (fun _ _ _ _ _ _ h => csem_goto h) hrP hm3
  obtain ⟨n, trS, t, ψ, hn, hrun, href, hend⟩ := isel_refinesC H hchk hMR hMRw hX hm2 hrV
  have hth := Thin.trans hthV hthP
  obtain ⟨m, hm, htk, hfull⟩ := Thin.take hth n
  have hlenV := vtrun_len (cEvs_len F fc) hrV
  obtain ⟨ψ2, href2⟩ := refines_of_thin (htk.map ProgE2E.convEv) (by
    intro j hj
    have hj' : j < (trV.take n).length := by simpa using hj
    simp only [List.getElem_map, List.length_map, List.getElem_take]
    exact hlenV j (by simp at hj'; omega))
  have href3 := Refines.congr (Refines.trans href href2) (MK' := Maps) (P' := fun _ => False)
    (fun a c ⟨b, h1, h2⟩ => h2 ▸ h1) (fun l => ⟨fun h => by rcases h with h | h <;> exact h,
      fun h => h.elim⟩)
  refine ⟨m, trS, t, fun p => ψ2 (ψ p), hm, hrun, href3, ?_⟩
  rcases hend with ⟨hend, hret⟩ | ⟨s', vs', ht, hat, hm', hr'⟩
  · refine .inl ⟨?_, fun v hv => hfull (Nat.le_of_eq (hret v hv).symm)⟩
    rcases hend with ⟨h, cV', hv⟩ | h
    · refine .inl ⟨hfull (by omega), ?_⟩
      cases vVE with
      | run vv =>
        cases vPE with
        | run vp =>
          obtain ⟨tgt', hvp⟩ := prep_fwd H3 hds hpE hv
          cases cE with
          | run cm => exact sim_progress_at _ keep hc hmE hvp
          | ret => exact hmE.elim
          | halt => exact hmE.elim
        | ret => cases hpE
        | halt => cases hpE
      | ret => cases hv
      | halt => cases hv
    · exact .inr h
  · obtain ⟨vb, nm, us, ds, hvb, hi⟩ := match_atCall H hchk hm' hat
    obtain ⟨hnil, rfl⟩ := vtrun_atCall hX0 hvb hi hr'
    have hnV : trV.length ≤ n := by
      have := congrArg List.length hnil
      simp at this; omega
    refine .inr ⟨hfull hnV, s', vs', ?_⟩
    cases vPE with
    | run vp =>
      cases cE with
      | run cm => exact ⟨vp, cm, ht, hat, rfl, hm', hpE, hmE⟩
      | ret => exact hmE.elim
      | halt => exact hmE.elim
    | ret => cases hpE
    | halt => cases hpE

end

/-! ## Layer 4b -/

open ArmAllocThread

/-- **Every instruction of the activation's code is covered or a call.** -/
def CoveredCodeC (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → (∃ info, i = .call info) ∨ SegFoot.Covered R.ctx i

theorem coveredCodeC_of_lsC {R : RL} (h : MemScopeLSC R) : CoveredCodeC R := fun b vb k i hb hi =>
  (h b vb k i hb hi).elim (fun h => .inr (ThreadProgress.covered_of_memFormL h)) fun h =>
    h.elim (fun h => .inr (ThreadProgress.covered_of_brForm h)) fun h =>
      h.elim (fun h => .inr (ThreadProgress.covered_of_formOk h.1)) .inl

/-- **The allocated code's progress, as a thread, admitting calls** (`srcStep_of_mstep`): with an
external semantics without `call` step, a step of the allocated code is not a call. -/
theorem srcStep_of_mstepC {R : RL} (hcov : CoveredCodeC R) (hgv : R.gv = fun _ _ => False)
    (hX : TlsMemFree R.X) (hX0 : NoCall R.X) {s : ArmState}
    {c c' : MConf CV ArmState} (hq : Q R s c) (hs : MStep R.vc R.sem ckeep R.rf c c') :
    ∃ evs c'', SrcStep R c evs c'' := by
  cases hs with
  | move => exact ⟨[], _, .move⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hclob
      hnext =>
    rcases hcov b vb k i hvb hi with ⟨info, rfl⟩ | ⟨hnc, hnt, hcv⟩
    · exfalso
      have hsem' := hsem
      simp only [RL.sem, hgv, ThreadCompose.csemV_none, csem] at hsem'
      rw [hX0] at hsem'
      cases hsem'
    have hstr := q_stRel hq
    have herrw : Arm.r .ERR w = .None := by
      rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
    have halw : CheckSPAlignment w :=
      align_of_sp (show Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s from
        (hstr.world.1 (.GPR 31#5) (by simp [Masked])).symm) hstr.align
    obtain ⟨regs, -, hsz', -, huses⟩ := q_regs hq hvb hi hops
    have hst : i.isCtl = false →
        csemWF R.ctx i (itemUses ops allocs m) = true ∧ CheckSPAlignment w := by
      intro hctl
      have hfo : FormOk R.ctx i = true := by
        rcases hcv with h | h
        · rw [hctl] at h; cases h
        · exact h
      refine ⟨?_, halw⟩
      rw [huses]
      simp [csemWF, hfo, hops, useVals_length ops regs hsz']
    have hfoot := ifoot_csem (F := R.F) (ctx := R.ctx) (uses := itemUses ops allocs m) hX herrw
      hnc hnt hst
    have hsemC : csem R.F R.ctx R.X i (itemUses ops allocs m) w = some (outs, w', ctl) := by
      rw [← R.sem_eq hnc hnt]; exact hsem
    have hp := patch_of_agrees (ThreadProgress.agrees_cEvs herrw hfoot hsemC)
    refine ⟨cEvs R.F R.ctx i (itemUses ops allocs m) w, c', .op hvb hi hops ?_ ?_ ?_⟩
    · rw [hp]
    · rw [hp]
      unfold IFoot at hfoot ⊢
      simp only [R.sem_eq hnc hnt]
      exact hfoot
    · rw [hp]
      exact .op hvb hi hops hsz hsem hlen hho hclob hnext

/-- **All layers from a segment's start, layers 2–4a given, the pause relation on the allocated
configuration** (`arm_isel_refinesG`; `CallRets` pauses at returns too): layer 4b
(`arm_alloc_refines_lsCL`) from `Q ∧ AInv` at the allocated configuration `cM`, composed with any
realization `hL` of the allocated code's runs from `cM` by CLIF runs from `s`, which may pause
with the whole run realized at a CLIF state related by `Rel` to the run's last configuration. -/
theorem arm_isel_refinesG2 {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {env : Clif.Env} {p : Clif.Program} (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {s : Clif.State} {cM : MState CV ArmState} {Rel : Clif.State → MConf CV ArmState → Prop}
    (hL : ∀ {trM : List (List Ev)} {cE : MConf CV ArmState},
      MTRun RA.vc RA.rf (csem RA.F RA.ctx RA.X) ckeep (cEvs RA.F RA.ctx) (.run cM) trM cE →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        ((((m = trM.length ∧ ∃ cM', MStep RA.vc (csem RA.F RA.ctx RA.X) ckeep RA.rf cE cM') ∨
            Stop env p t) ∧ ∀ v, t = .ret v → m = trM.length) ∨
          (m = trM.length ∧ ∃ s', t = .run s' ∧ Rel s' cE)))
    {x : ArmState} {mon : Mon} (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          AtRets RA cE) ∨
        (∃ tE s' cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE cE ∧ Pause RA cE ∧ t = .run s' ∧ Rel s' cE)) := by
  have hsem : RA.sem = csem RA.F RA.ctx RA.X := by
    show csemV RA.gv RA.F RA.ctx RA.X = _
    rw [hgv, csemV_none]
  obtain ⟨nA, trM, cE, ψA, hnA, hM, hAr, hend⟩ := arm_alloc_refines_lsCL hR hsc hg hq hA hr
  rw [hsem] at hM
  obtain ⟨m, trS, t, ψ, hm, hrun, href, hendm⟩ := hL hM
  have h1 : ∀ j (hj : j < (conv (evTr (ls.take nA))).length),
      (conv (evTr (ls.take nA)))[j].length ≤ 1 := by
    intro j hj
    have hl := prun_len hr j (by simp [conv, evTr] at hj ⊢; omega)
    simp only [conv, evTr, List.getElem_map, List.length_map, List.getElem_take] at hl ⊢
    exact hl
  obtain ⟨k, hk, hAk, hkfull⟩ := Refines.take hAr h1 m
  have hlenA : (conv (evTr (ls.take nA))).length = nA := by
    simp [conv, evTr]; omega
  have htk : (conv (evTr (ls.take nA))).take k = conv (evTr (ls.take k)) := by
    simp only [conv, evTr, ← List.map_take, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  rw [htk] at hAk
  have hm' : (conv trM).take m = conv (trM.take m) := by simp [conv, List.map_take]
  rw [hm'] at hAk
  have href2 := Refines.congr (Refines.trans href hAk) (MK' := Maps) (P' := PrivA RA)
    (fun a c ⟨b, h1, h2⟩ => h2 ▸ h1)
    (fun l => ⟨fun h => by rcases h with h | h; exact h.elim; exact h, fun h => .inr h⟩)
  have hPA : ∀ {t : ArmState × Mon} {n : Nat}, n ≤ ls.length → k = n →
      PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take n) t →
      PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) t := fun _ e h => e ▸ h
  have hpair : ∀ a b, (evAt (conv (evTr (ls.take k))) a).isSome →
      (evAt (conv (evTr (ls.take k))) b).isSome →
      (MonPair (evTr (ls.take nA)) a b ↔ MonPair (evTr (ls.take k)) a b) := by
    intro a b _ hb
    refine RealizeCompiled.monPair_take (by omega : k ≤ nA) ?_
    obtain ⟨hb1, -⟩ := evAt_isSome (show (evAt (conv (evTr (ls.take k))) (b.1, b.2)).isSome from hb)
    have := hb1; simp [conv, evTr] at this; omega
  refine ⟨k, trS, t, _, by omega, hrun, RealizeCompiled.Refines.pairT_congr href2 hpair, ?_⟩
  rcases hendm with ⟨⟨h, cM', hmst⟩ | h, -⟩ | ⟨hfm, s', ht, hrel⟩
  · have hk' := hkfull (by simp [conv, h])
    rw [hlenA] at hk'
    rcases hend with h' | ⟨tE, hpre, hrq, hD | hcall | hrets⟩
    · exact .inl (hk'.trans h')
    · exfalso
      rw [← hsem] at hmst
      rcases hD with ⟨vals, m', w', rfl⟩ | ⟨w', rfl⟩ | hD
      · cases hmst
      · cases hmst
      · obtain ⟨evs, c'', hs⟩ : ∃ evs c'', SrcStep RA _ evs c'' := by
          rcases hrq with ⟨hq, -⟩ | hrt
          · exact srcStep_of_mstepC (coveredCodeC_of_lsC hsc) hgv hX hX0 hq hmst
          · exact srcStep_of_retTail hX hrt hmst
        exact hD evs c'' hs
    · exfalso
      obtain ⟨b, k0, allocs, its, mm, ww, vb, info, rfl, hvb, hi⟩ := hcall
      cases hmst with
      | op hvb1 hi1 _ _ hsem1 =>
        rw [hvb] at hvb1; cases hvb1
        rw [hi] at hi1; cases hi1
        simp only [csem] at hsem1
        rw [hX0] at hsem1
        cases hsem1
    · exact .inr (.inr (.inl ⟨tE, cE, hPA hnA hk' hpre, hrq, hrets⟩))
  · exact .inr (.inl h)
  · have hk' := hkfull (by simp [conv, hfm])
    rw [hlenA] at hk'
    rcases hend with h' | ⟨tE, hpre, hrq, hP⟩
    · exact .inl (hk'.trans h')
    · exact .inr (.inr (.inr ⟨tE, s', cE, hPA hnA hk' hpre, hrq, hP, ht, hrel⟩))

/-- **All layers from a segment's start, layers 2–4a given** (`arm_isel_refinesC`,
`arm_isel_refines_entryC`): `arm_isel_refinesG2` pausing at a call statement related by `Rel`
to the allocated configuration. -/
theorem arm_isel_refinesG {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {env : Clif.Env} {p : Clif.Program} (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {s : Clif.State} {cM : MState CV ArmState} {Rel : Clif.State → MState CV ArmState → Prop}
    (hL : ∀ {trM : List (List Ev)} {cE : MConf CV ArmState},
      MTRun RA.vc RA.rf (csem RA.F RA.ctx RA.X) ckeep (cEvs RA.F RA.ctx) (.run cM) trM cE →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        ((((m = trM.length ∧ ∃ cM', MStep RA.vc (csem RA.F RA.ctx RA.X) ckeep RA.rf cE cM') ∨
            Stop env p t) ∧ ∀ v, t = .ret v → m = trM.length) ∨
          (m = trM.length ∧ ∃ s' cM', t = .run s' ∧ AtCallS s' ∧ cE = .run cM' ∧ Rel s' cM')))
    {x : ArmState} {mon : Mon} (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          AtRets RA cE) ∨
        (∃ tE s' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Rel s' cM')) := by
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hend⟩ := arm_isel_refinesG2 hR hsc hgv hg hX hX0
    (Rel := fun s' cE => ∃ cM', AtCallS s' ∧ cE = .run cM' ∧ Rel s' cM')
    (fun hM => by
      obtain ⟨m, trS, t, ψ, hm, hrun, href, hendm⟩ := hL hM
      exact ⟨m, trS, t, ψ, hm, hrun, href, hendm.imp_right fun ⟨h1, s', cM', h2, h3, h4, h5⟩ =>
        ⟨h1, s', h2, cM', h3, h4, h5⟩⟩) hq hA hr
  refine ⟨k, trS, t, ψ, hk, hrun, href, ?_⟩
  rcases hend with h | h | h | ⟨tE, s', cE, h1, h2, h3, h4, cM', h5, rfl, h6⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨tE, s', cM', h1, h2, h3, h4, h5, h6⟩))

/-- **All layers from related configurations, pausing at calls** (module doc). -/
theorem arm_isel_refinesC {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat}
    {syms : String → Option Nat}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk RA.F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    {s : Clif.State} {vV vP : VState CV ArmState} {cM : MState CV ArmState} {x : ArmState}
    {mon : Mon}
    (hm2 : Match f ctx R gn bl A MR slots s vV)
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV) (.run vP))
    (hm4 : MatchRun cc ins ckeep r₀ cM vP) (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          AtRets RA cE) ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep r₀ cM' vP')) := by
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hend⟩ := arm_isel_refinesG hR hsc hgv hg hX hX0
    (Rel := fun s' cM' => ∃ vV' vP', Match f ctx R gn bl A MR slots s' vV' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
      MatchRun cc ins ckeep r₀ cM' vP')
    (fun hM => by
      obtain ⟨m, trS, t, ψ, hm, hrun, href, hendm⟩ :=
        isel_alloc_refinesC H hchk hMR hMRw hX hX0 H3 hc hm2 hm3 hm4 hM
      refine ⟨m, trS, t, ψ, hm, hrun, href, hendm.imp_right fun ⟨h1, s', vV', vP', cM', h2, h3, h4,
        h5, h6, h7⟩ => ⟨h1, s', cM', h2, h3, h4, vV', vP', h5, h6, h7⟩⟩) hq hA hr
  refine ⟨k, trS, t, ψ, hk, hrun, href, ?_⟩
  rcases hend with h | h | h | ⟨tE, s', cM', h1, h2, h3, h4, h5, vV', vP', h6, h7, h8⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨tE, s', vV', vP', cM', h1, h2, h3, h4, h5, h6, h7, h8⟩))

/-! ## The entry -/

/-- **The allocation checker's relation at the entry configurations** (as in
`AllocThread.alloc_thinP`), with the entry registers' values as `r₀`. -/
theorem alloc_init {vc : VCode} {rf : RFunc} (h : checkAlloc vc rf = .ok ())
    (keep : Reg → CV → CV) : ∃ cc ins a0, CheckedAt vc rf cc ins a0 ∧
      ∀ (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState),
        Backend.Proof.Match cc ins keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀)
          (VConf.init ρ₀ w₀) := by
  obtain ⟨c, ins, hc⟩ := checked_of_checkAlloc h
  obtain ⟨a0, hat, hle⟩ := hc.at
  refine ⟨c, ins, a0, hat, fun m₀ ρ₀ w₀ => ?_⟩
  have hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r)) := Inv_mono hle Inv_entryState
  obtain ⟨a, out, ha, hrb, hedges⟩ :=
    verifyBlock_ok (hat.blocks 0 (Nat.pos_of_ne_zero hat.nonempty))
  rw [hat.entry] at ha
  cases ha
  obtain ⟨vb, items, hvb, hitems, hrb'⟩ := runBlock_ok hrb
  rw [hat.rf_eq] at hitems
  have : rf.blocks[0]! = items := by simp [getElem!_def, hitems]
  simp only [MConf.init, VConf.init, this]
  exact ⟨rfl, rfl, vb, a0, out, hvb, hrb', hinv0, hedges⟩

/-- **`prepare`'s relation at the entry configurations** (as in `PrepThread.prep_thinP`). -/
theorem prep_init {vc vcp : VCode} (hcheck : prepCheck vc vcp = true) :
    ∃ (L : Nat → Prop) (ss ss' : Array (Array Nat)), PrepFacts vc vcp L ss ss' ∧
      ∀ (sem : ISem CV ArmState) (ev : MInst → List CV → ArmState → List Ev) (ρ₀ : Nat → CV)
        (w₀ : ArmState), PMatch vc vcp sem ev L ss' (VConf.init ρ₀ w₀) (VConf.init ρ₀ w₀) := by
  obtain ⟨L, ss, ss', H, hL0, h0⟩ := prepFacts_of_check hcheck
  exact ⟨L, ss, ss', H, fun _ _ _ _ => .blk hL0 h0⟩

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **Layers 2, 3 and 4a from the function's entry, pausing at calls** (`isel_alloc_refinesC`
with layer 2 from the entry, `IselCall.isel_refines_entryC`; the relations of layers 3/4a at the
entry configurations by `prep_init`/`alloc_init`). -/
theorem isel_alloc_refines_entryC (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hX0 : NoCall X) (hMem : MemRefines F sb syms (csem F fc X))
    (hMRs : MRStable F MR) (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    {vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc vcp L ss ss')
    {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt vcp rf c ins a0) {keep : Reg → CV → CV} {r₀ : Reg → CV}
    {cM : MState CV ArmState}
    (hm3 : PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' (VConf.init ρ₀ w₀) (VConf.init ρ₀ w₀))
    (hm4 : MatchRun c ins keep r₀ cM ⟨0, 0, ρ₀, w₀⟩)
    {trM : List (List Ev)} {cE : MConf CV ArmState}
    (hr : MTRun vcp rf (csem F fc X) keep (cEvs F fc) (.run cM) trM cE) :
    ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
      ((((m = trM.length ∧ ∃ cM', MStep vcp (csem F fc X) keep rf cE cM') ∨ Stop env p t) ∧
          ∀ v, t = .ret v → m = trM.length) ∨
        (m = trM.length ∧ ∃ s' vV' vP' cM', t = .run s' ∧ AtCallS s' ∧ cE = .run cM' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' (.run vV') (.run vP') ∧
          MatchRun c ins keep r₀ cM' vP')) := by
  have hds := (driverSem_csem F fc X).toDriverSemG
  obtain ⟨trP, vPE, hrP, hmE, hthP⟩ := alloc_run (r₀ := r₀) hc hr (v := .run ⟨0, 0, ρ₀, w₀⟩) hm4
  obtain ⟨trV, vVE, hrV, hpE, hthV⟩ := prep_run H3 hds (fun _ _ _ h => cEvs_setTargets F fc h)
    (fun _ _ _ _ _ _ h => csem_goto h) hrP hm3
  obtain ⟨n, trS, t, ψ, hn, hrun, href, hend⟩ := isel_refines_entryC H hchk hMR hMRw hX hMem hMRs
    hreg hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hrV
  have hth := Thin.trans hthV hthP
  obtain ⟨m, hm, htk, hfull⟩ := Thin.take hth n
  have hlenV := vtrun_len (cEvs_len F fc) hrV
  obtain ⟨ψ2, href2⟩ := refines_of_thin (htk.map ProgE2E.convEv) (by
    intro j hj
    have hj' : j < (trV.take n).length := by simpa using hj
    simp only [List.getElem_map, List.length_map, List.getElem_take]
    exact hlenV j (by simp at hj'; omega))
  have href3 := Refines.congr (Refines.trans href href2) (MK' := Maps) (P' := fun _ => False)
    (fun a c ⟨b, h1, h2⟩ => h2 ▸ h1) (fun l => ⟨fun h => by rcases h with h | h <;> exact h,
      fun h => h.elim⟩)
  refine ⟨m, trS, t, fun p => ψ2 (ψ p), hm, hrun, href3, ?_⟩
  rcases hend with ⟨hend, hret⟩ | ⟨s', vs', ht, hat, hm', hr'⟩
  · refine .inl ⟨?_, fun v hv => hfull (Nat.le_of_eq (hret v hv).symm)⟩
    rcases hend with ⟨h, cV', hv⟩ | h
    · refine .inl ⟨hfull (by omega), ?_⟩
      cases vVE with
      | run vv =>
        cases vPE with
        | run vp =>
          obtain ⟨tgt', hvp⟩ := prep_fwd H3 hds hpE hv
          cases cE with
          | run cm => exact sim_progress_at _ keep hc hmE hvp
          | ret => exact hmE.elim
          | halt => exact hmE.elim
        | ret => cases hpE
        | halt => cases hpE
      | ret => cases hv
      | halt => cases hv
    · exact .inr h
  · obtain ⟨vb, nm, us, ds, hvb, hi⟩ := match_atCall H hchk hm' hat
    obtain ⟨hnil, rfl⟩ := vtrun_atCall hX0 hvb hi hr'
    have hnV : trV.length ≤ n := by
      have := congrArg List.length hnil
      simp at this; omega
    refine .inr ⟨hfull hnV, s', vs', ?_⟩
    cases vPE with
    | run vp =>
      cases cE with
      | run cm => exact ⟨vp, cm, ht, hat, rfl, hm', hpE, hmE⟩
      | ret => exact hmE.elim
      | halt => exact hmE.elim
    | ret => cases hpE
    | halt => cases hpE

end

/-- **All layers from the activation's entry configuration, pausing at calls** (module doc):
`arm_isel_refinesC` where the segment is the activation's first, from the CLIF entry state `cs`
and `Q ∧ AInv` at the allocated entry configuration `MConf.init RA.rf m₀ w₀`; at a call pause
all three relations hold, ready for the callee's entry and the resume. -/
theorem arm_isel_refines_entryC {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
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
    (hargs : ArgsAtEntry RA.F f.sig args w₀) {x : ArmState} {mon : Mon}
    (hq : Q RA x (MConf.init RA.rf m₀ w₀)) (hA : AInv RA (MConf.init RA.rf m₀ w₀))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          AtRets RA cE) ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep (fun r => m₀ (.reg r)) cM' vP')) := by
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hend⟩ := arm_isel_refinesG hR hsc hgv hg hX hX0
    (s := cs) (cM := ⟨0, RA.rf.blocks[0]!.toList, m₀, w₀⟩)
    (Rel := fun s' cM' => ∃ vV' vP', Match f ctx R gn bl A MR slots s' vV' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
      MatchRun cc ins ckeep (fun r => m₀ (.reg r)) cM' vP')
    (fun hM => by
      obtain ⟨m, trS, t, ψ, hm, hrun, href, hendm⟩ :=
        isel_alloc_refines_entryC (ρ₀ := fun _ => 0) H hchk hMR hMRw hX hX0 hMem hMRs hreg hB0
          hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs H3 hc (hm3 _ _)
          (hm4 m₀ (fun _ => 0) w₀) hM
      refine ⟨m, trS, t, ψ, hm, hrun, href, hendm.imp_right fun ⟨h1, s', vV', vP', cM', h2, h3, h4,
        h5, h6, h7⟩ => ⟨h1, s', cM', h2, h3, h4, vV', vP', h5, h6, h7⟩⟩) hq hA hr
  refine ⟨k, trS, t, ψ, hk, hrun, href, ?_⟩
  rcases hend with h | h | h | ⟨tE, s', cM', h1, h2, h3, h4, h5, vV', vP', h6, h7, h8⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨tE, s', vV', vP', cM', h1, h2, h3, h4, h5, h6, h7, h8⟩))

end Concurrency.CallLayers

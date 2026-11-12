import FV.Concurrency.IselRetT
import FV.Concurrency.IselCallRet
import FV.Concurrency.CallResume

/-!
# The `rets` end of an activation (#473, (1))

At a `return` matched by layer 2 (`IselCallRet.isel_refinesCR`'s pause):

* **`ret_pause`**: the CLIF thread stops there (a trapping or stuck `return`), or the `return`
  is done with values `vals`, the VCode trace from the match is event-free, and the VCode
  returns (`VRetFrom`) values holding `vals` (`PrefixHold`) with the memory relation at the
  return (`IselRetT.term_stepRT`, `IselStep.term_retNT`, `IselSeg.vtrun_follow`).
-/

namespace Concurrency.CallRets

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine IselStep IselCall
  IselCallRet IselSeg AllocThread ThreadCompose
section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **Layer 2 at a matched `return`** (module doc). -/
theorem ret_pause (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) {s : Clif.State} {b k : Nat} {ρ : Nat → CV}
    {w : ArmState} (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hat : AtRetS s)
    {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    Stop env p (.run s) ∨ ∃ vals cm, Clif.step env p s = .done vals cm ∧ (∀ e ∈ tr, e = []) ∧
      ∃ us outs w', VRetFrom vc (csem F fc X) ⟨b, k, ρ, w⟩ us outs w' ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave := by
  obtain ⟨hbody, xs, hT⟩ := hat
  obtain ⟨-, -, -, -, B, j, hB, hterm, -, -, -, -, -⟩ := id hm
  obtain ⟨L, hL⟩ := H.blow hB
  have htk := termOk_ofC hchk hB hL
  simp only [termOkB, Bool.and_eq_true, Bool.not_eq_true'] at htk
  obtain ⟨⟨hnt, -⟩, hall⟩ := htk
  have hnt' : s.frame.term.isTry = false := by rw [hterm]; exact hnt
  have htk' : ∀ L', bl[b]? = some L' → ∀ i ∈ L'.tst'.emitted.toList, Code.akinds i = [] := by
    intro L' hL' i hi
    rw [hL] at hL'; cases hL'
    have := List.all_eq_true.mp hall i hi
    simpa using this
  cases hs : Clif.step env p s with
  | done vals cm =>
    right
    obtain ⟨n, us, w', hstar⟩ := term_retNT H hm hbody hnt' htk' hs
    have hnil : ∀ e ∈ tr, e = [] := by
      rcases vtrun_follow hstar hr with ⟨pre, rest', htr, -, hpe, -, h2⟩ | ⟨-, hpe⟩
      · cases h2 with
        | nil => rw [htr, List.append_nil]; exact hpe
        | cons h _ => cases h
      · exact hpe
    exact ⟨vals, cm, rfl, hnil, (IselRetT.term_stepRT H hm hbody hnt').2.1 vals cm hs⟩
  | next s' =>
    exfalso
    rw [Clif.step_term env p s hbody, hT] at hs
    obtain ⟨hcall, -⟩ := hm
    exact (stepTerm_ret (env := env) (p := p) hcall).1 s' hs
  | trapped c =>
    exact .inl (.inl (done_of_step (evShape_term hbody) (by rw [hs]; rfl)))
  | stuck m =>
    exact .inl (.inl (done_of_step (evShape_term hbody) (by rw [hs]; rfl)))

/-- **The CLIF return pop in a linked thread**: a bottom frame whose `return` is done with
`vals` and `cm`, under suspended callers `(caller, results) :: cs`, steps without events to the
caller with the results bound and the memory `cm` (`ClifCStepTerm.cstep_ret_pop`). -/
theorem ret_pop {env : Clif.Env} {p : Clif.Program} {s : Clif.State} (hcall : s.callers = [])
    (hbody : s.frame.body = []) {xs : List Clif.ValueId} (hT : s.frame.term = .ret xs)
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hs : Clif.step env p s = .done vals cm) {caller : Clif.Frame}
    {results : List Clif.ValueId} {cs : List (Clif.Frame × List Clif.ValueId)}
    {regs : Clif.Regs} (hr : caller.regs.setMany results vals = some regs) :
    CStep env p (.run (ClifLift.pushC ((caller, results) :: cs) s)) []
      (.run ⟨{ caller with regs := regs }, cs, cm⟩) := by
  rw [Clif.step_term env p s hbody, hT] at hs
  obtain ⟨-, -, hdn⟩ := stepTerm_ret (env := env) (p := p) (s := s) (xs := xs) hcall
  obtain ⟨hg, rfl⟩ := hdn vals cm hs
  have hs' := hs
  simp only [Clif.stepTerm, hg, Clif.StepResult.ofRes, Clif.returnValues, hcall] at hs'
  rcases checkTys_cases s!"return values of %{s.frame.func.name}" vals
    (Clif.AbiParam.tys s.frame.func.sig.returns) with ⟨hc, -⟩ | ⟨m, hc⟩
  · exact cstep_ret_pop (s := ClifLift.pushC ((caller, results) :: cs) s) hbody hT hg hc
      (by simp [ClifLift.pushC, hcall]) hr
  · rw [hc] at hs'; cases hs'

theorem thin_refl {α : Type} : ∀ (l : List (List α)), Thin l l
  | [] => .nil
  | _ :: l => .both (thin_refl l)

/-- A trace thins its extension by event-free steps. -/
theorem thin_append_nil {α : Type} :
    ∀ (l r : List (List α)), (∀ e ∈ r, e = []) → Thin l (l ++ r)
  | [], [], _ => .nil
  | [], _ :: r, h => by
    rw [h _ List.mem_cons_self]
    exact .tgt (thin_append_nil [] r fun e he => h e (List.mem_cons_of_mem _ he))
  | _ :: l, r, h => .both (thin_append_nil l r h)

variable {sb : Nat} {syms : String → Option Nat}

/-- **Layers 2, 3 and 4a, layer 2's realization given, pausing at calls and at done
`return`s** (`CallLayers.isel_alloc_refinesC` with any realization `hL2` of the VCode runs from
`vV` pausing as `IselCallRet.isel_refinesCR`, and `ret_pause`): at a `return`, the realized
prefix is the whole run, the CLIF state at the `return` matched by layer 2 to a VCode
configuration from which an event-free run reaches the configuration related by layers 3/4a to
the allocated run's last one, and from which the VCode returns its values. -/
theorem isel_alloc_refinesCRG (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hX0 : NoCall X)
    {vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc vcp L ss ss')
    {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt vcp rf c ins a0) {keep : Reg → CV → CV} {r₀ : Reg → CV}
    {s : Clif.State} {vV vP : VState CV ArmState} {cM : MState CV ArmState}
    (hL2 : ∀ {tr : List (List Ev)} {cT : VConf CV ArmState},
      VTRun vc (csem F fc X) (cEvs F fc) (.run vV) tr cT →
      ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
        ((((n = tr.length ∧ ∃ c', VStep vc (csem F fc X) cT c') ∨ Stop env p t) ∧
            ∀ v, t = .ret v → n = tr.length) ∨
          ∃ s' vs', t = .run s' ∧ AtCR s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
            VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT))
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
          MatchRun c ins keep r₀ cM' vP') ∨
        (m = trM.length ∧ ∃ s' vR trR vV' vP' vals cm, t = .run s' ∧ AtRetS s' ∧
          Match f ctx R gn bl A MR slots s' vR ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vR) trR vV' ∧ (∀ e ∈ trR, e = []) ∧
          PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' vV' vP' ∧
          Backend.Proof.Match c ins keep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
          ∃ us outs w', VRetFrom vc (csem F fc X) vR us outs w' ∧
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MR slots s'.mem w' ∧
            cm = (s'.mem.free (slots.map (·.2))).leave)) := by
  have hds := (driverSem_csem F fc X).toDriverSemG
  obtain ⟨trP, vPE, hrP, hmE, hthP⟩ := AllocThread.alloc_run (r₀ := r₀) hc hr (v := .run vP) hm4
  obtain ⟨trV, vVE, hrV, hpE, hthV⟩ := prep_run H3 hds (fun _ _ _ h => cEvs_setTargets F fc h)
    (fun _ _ _ _ _ _ h => csem_goto h) hrP hm3
  obtain ⟨n, trS, t, ψ, hn, hrun, href, hend⟩ := hL2 hrV
  have hth := Thin.trans hthV hthP
  have hlenV := vtrun_len (cEvs_len F fc) hrV
  -- the realization of the first `n` VCode steps, carried to a prefix of the allocated run
  have hcarry : ∀ {m : Nat}, Thin (trV.take n) (trM.take m) →
      ∃ ψ', Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS
        (conv (trM.take m)) ψ' := by
    intro m htk
    obtain ⟨ψ2, href2⟩ := refines_of_thin (htk.map ProgE2E.convEv) (by
      intro j hj
      have hj' : j < (trV.take n).length := by simpa using hj
      simp only [List.getElem_map, List.length_map, List.getElem_take]
      exact hlenV j (by simp at hj'; omega))
    exact ⟨_, Refines.congr (Refines.trans href href2) (MK' := Maps) (P' := fun _ => False)
      (fun a c ⟨b, h1, h2⟩ => h2 ▸ h1) (fun l => ⟨fun h => by rcases h with h | h <;> exact h,
        fun h => h.elim⟩)⟩
  obtain ⟨m, hm, htk, hfull⟩ := Thin.take hth n
  rcases hend with ⟨hend, hret⟩ | ⟨s', vs', ht, hat | hat, hm', hr'⟩
  · obtain ⟨ψ', href3⟩ := hcarry htk
    refine ⟨m, trS, t, ψ', hm, hrun, href3, .inl ⟨?_, fun v hv => hfull (Nat.le_of_eq (hret v hv).symm)⟩⟩
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
  · obtain ⟨ψ', href3⟩ := hcarry htk
    obtain ⟨vb, nm, us, ds, hvb, hi⟩ := match_atCall H hchk hm' hat
    obtain ⟨hnil, rfl⟩ := vtrun_atCall hX0 hvb hi hr'
    have hnV : trV.length ≤ n := by
      have := congrArg List.length hnil
      simp at this; omega
    refine ⟨m, trS, t, ψ', hm, hrun, href3, .inr (.inl ⟨hfull hnV, s', vs', ?_⟩)⟩
    cases vPE with
    | run vp =>
      cases cE with
      | run cm => exact ⟨vp, cm, ht, hat, rfl, hm', hpE, hmE⟩
      | ret => exact hmE.elim
      | halt => exact hmE.elim
    | ret => cases hpE
    | halt => cases hpE
  · obtain ⟨b, k, ρ, w⟩ := vs'
    rcases ret_pause H hchk hm' hat hr' with hstop | ⟨vals, cm, hs, hnil, hret⟩
    · obtain ⟨ψ', href3⟩ := hcarry htk
      exact ⟨m, trS, t, ψ', hm, hrun, href3, .inl ⟨.inr (ht ▸ hstop), fun v hv => by
        rw [ht] at hv; cases hv⟩⟩
    · -- the rest of the VCode run is event-free: the whole allocated run is realized
      have hth' : Thin (trV.take n) trM := by
        refine Thin.trans ?_ hth
        have := thin_append_nil (trV.take n) (trV.drop n) hnil
        rwa [List.take_append_drop] at this
      have htk' : Thin (trV.take n) (trM.take trM.length) := by rwa [List.take_length]
      obtain ⟨ψ', href3⟩ := hcarry htk'
      refine ⟨trM.length, trS, t, ψ', Nat.le_refl _, hrun, href3, .inr (.inr ⟨rfl, ?_⟩)⟩
      exact ⟨s', _, _, vVE, vPE, vals, cm, ht, hat, hm', hr', hnil, hpE, hmE, hs, hret⟩

/-- **Layers 2, 3 and 4a from related configurations, pausing at calls and at done `return`s**
(`isel_alloc_refinesCRG` with `IselCallRet.isel_refinesCR`). -/
theorem isel_alloc_refinesCR (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
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
          MatchRun c ins keep r₀ cM' vP') ∨
        (m = trM.length ∧ ∃ s' vR trR vV' vP' vals cm, t = .run s' ∧ AtRetS s' ∧
          Match f ctx R gn bl A MR slots s' vR ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vR) trR vV' ∧ (∀ e ∈ trR, e = []) ∧
          PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' vV' vP' ∧
          Backend.Proof.Match c ins keep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
          ∃ us outs w', VRetFrom vc (csem F fc X) vR us outs w' ∧
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MR slots s'.mem w' ∧
            cm = (s'.mem.free (slots.map (·.2))).leave)) :=
  isel_alloc_refinesCRG H hchk hX0 H3 hc (fun hrV => isel_refinesCR H hchk hMR hMRw hX hm2 hrV)
    hm3 hm4 hr


/-- **Layers 2, 3 and 4a from the function's entry, pausing at calls and at done `return`s**
(`isel_alloc_refinesCRG` with `IselCallRet.isel_refines_entryCR`; the relations of layers 3/4a
at the entry configurations by `CallLayers.prep_init`/`alloc_init`). -/
theorem isel_alloc_refines_entryCR (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
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
          MatchRun c ins keep r₀ cM' vP') ∨
        (m = trM.length ∧ ∃ s' vR trR vV' vP' vals cm, t = .run s' ∧ AtRetS s' ∧
          Match f ctx R gn bl A MR slots s' vR ∧
          VTRun vc (csem F fc X) (cEvs F fc) (.run vR) trR vV' ∧ (∀ e ∈ trR, e = []) ∧
          PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' vV' vP' ∧
          Backend.Proof.Match c ins keep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
          ∃ us outs w', VRetFrom vc (csem F fc X) vR us outs w' ∧
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MR slots s'.mem w' ∧
            cm = (s'.mem.free (slots.map (·.2))).leave)) :=
  isel_alloc_refinesCRG H hchk hX0 H3 hc (vV := ⟨0, 0, ρ₀, w₀⟩) (fun hrV =>
    isel_refines_entryCR H hchk hMR hMRw hX hMem hMRs hreg hB0 hcall hfunc hslots hbody hterm
      hregs hty hsig hmr hargs hrV) hm3 hm4 hr


end

end Concurrency.CallRets

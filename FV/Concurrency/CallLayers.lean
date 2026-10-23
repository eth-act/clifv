import FV.Concurrency.IselCall
import FV.Concurrency.ThreadCompose

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
  `IselCall.isel_refinesC`, `match_atCall`, `vtrun_atCall`).
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

end Concurrency.CallLayers

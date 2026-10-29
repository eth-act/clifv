import FV.Concurrency.CallRetsEnd

/-!
# All layers pausing at calls and returns, every `rets` end resolved (#473, step (2))

`CallRetsEnd.arm_isel_refinesCR` leaves two ends where layer 4b pauses at a return without the
return's contract: layer 4b at a `rets` item while layers 2–4a realize the whole run with a step
at its end (`AtRets`), and layer 4b done or at a call while layer 2 is at a done `return`. Here
both are excluded:

* layer 2 with the VCode end off `rets` (`IselCallRet.isel_refinesCRN`: where the whole trace is
  realized with a VCode step at its end, that end is not at a `rets`, since a `rets` steps to a
  return from which no running configuration is reached, `IselStep.vstep_of_starNR`), carried
  through layers 3/4a (`isel_alloc_refinesCRGN`: `CallRetsAlloc.pmatch_rets` and the allocation
  checker's `Match` at the end);
* layer 4b stops at its first pause (`ItemSim.avoid`, `arm_alloc_refines_lsCLA`), so its
  allocated run never steps a `rets` item and does not end returned (`srun_avoid_ret`);
* at a done `return`, the VCode's event-free tail to its `rets` steps or has returned
  (`vstep_or_ret_of_retFrom`), so the allocated configuration steps (`doneRet_mstep`:
  `PrepThread.prep_fwd`, `sim_progress_at`), which neither a done configuration
  (`CallLayers.srcStep_of_mstepC`) nor a call (`NoCall`) allows.

**`arm_isel_refinesCRN`**/**`arm_isel_refines_entryCRN`**: every precise run is realized
entirely, up to where the CLIF thread stops, up to a call with the three relations, or up to a
done `return` with the return contract `RetEnd`.
-/

namespace Concurrency.CallRetsN

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ThreadCompose IselCall IselCallRet CallRets CallRetsAlloc ArmAllocThread E2E IselStep
  CallLayers CallRetsEnd

/-! ## Layer 4b stops at its first pause -/

/-- An `ItemSim` steps only from configurations where the source has not terminated. -/
theorem ItemSim.avoid {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}
    {C : Type} {S : C → List Ev → C → Prop} {Rel : ArmState × Mon → C → Prop} {Term : C → Prop}
    {μ : C → Nat} {Priv : Nat → Prop} (h : ItemSim P f ok S Rel Term μ Priv) :
    ItemSim P f ok (fun c evs c' => ¬ Term c ∧ S c evs c') Rel Term μ Priv := by
  classical
  intro t c hR ls t' hr
  by_cases hT : Term c
  · exact .inl hT
  rcases h t c hR ls t' hr with h | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
      ⟨evs, c', φ, hs, hi⟩ | h
  · exact absurd h hT
  · exact .inr (.inl ⟨n, evs, c', t1, φ, hn, hpos, ⟨hT, hs⟩, hr1, hR1, hi⟩)
  · exact .inr (.inr (.inl ⟨evs, c', φ, ⟨hT, hs⟩, hi⟩))
  · exact .inr (.inr (.inr h))

theorem SRun.mono' {C : Type} {S S' : C → List Ev → C → Prop}
    (h : ∀ c e c', S c e c' → S' c e c') :
    ∀ {c : C} {tr : List (List Ev)} {c' : C}, SRun S c tr c' → SRun S' c tr c'
  | _, _, _, .nil => .nil
  | _, _, _, .cons hs hr => .cons (h _ _ _ hs) (SRun.mono' h hr)

/-- A step of the allocated code to a return is from a `rets` item. -/
theorem atRets_of_srcStep_ret {R : RL} {c : MConf CV ArmState} {evs : List Ev}
    {vals : List CV} {m : Loc → CV} {w : ArmState} (hs : SrcStep R c evs (.ret vals m w)) :
    AtRets R c := by
  cases hs with
  | op hvb hi hops _ _ hms =>
    cases hms with
    | op hvb' hi' _ _ _ _ _ _ hnext =>
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      cases hnext with
      | ret h => subst h; exact ⟨_, _, _, _, _, _, _, _, rfl, hvb, hi⟩

/-- A run of the allocated code that steps only from configurations not paused does not end
returned (unless it starts so). -/
theorem srun_avoid_ret {R : RL} :
    ∀ {c : MConf CV ArmState} {trS : List (List Ev)} {cE : MConf CV ArmState},
    SRun (fun c evs c' => ¬ Pause R c ∧ SrcStep R c evs c') c trS cE →
    (∀ v m w, c ≠ .ret v m w) → ∀ v m w, cE ≠ .ret v m w
  | _, _, _, .nil, hc => hc
  | _, _, _, .cons ⟨hP, hs⟩ hr, _ => srun_avoid_ret hr fun v m w he => by
      subst he
      exact hP (.inr (.inr (atRets_of_srcStep_ret hs)))

/-- A run stopping at the first pause, of ranked configurations, is one of the configurations. -/
theorem SRun.fstP {R : RL} : ∀ {c c' : RConf} {tr : List (List Ev)},
    SRun (fun c evs c' => ¬ PauseR R c ∧ SrcStepR R c evs c') c tr c' →
      SRun (fun c evs c' => ¬ Pause R c ∧ SrcStep R c evs c') c.1 tr c'.1
  | _, _, _, .nil => .nil
  | _, _, _, .cons hs hr => .cons hs (SRun.fstP hr)

/-- **`arm_alloc_refines_lsCL`, its allocated run stopping at the first pause**: the run does
not end returned. -/
theorem arm_alloc_refines_lsCLA {R : RL} (hR : R.Wf) (hsc : MemScopeLSC R)
    {g : ArmState → ArmState} (hg : AgreesAt R g)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      ThreadRefine.Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      ((∀ v m w, c ≠ .ret v m w) → ∀ v m w, cE ≠ .ret v m w) ∧
      (n = ls.length ∨ ∃ tE, PRun Policy.arm g (OkPriv R) (s, mon) (ls.take n) tE ∧
        RelQ R tE cE ∧ Pause R cE) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSimQ (ItemSim.avoid (itemSim_lsCL hR hsc hg)) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.mono' (fun _ _ _ h => h.2) (SRun.fstP hs)),
    href, srun_avoid_ret (SRun.fstP hs), hend.imp_right fun ⟨tE, h1, h2, h3⟩ => ⟨tE, h1, h2.1, h3⟩⟩

/-- **An exclusive-closed trace's prefixes are exclusive-closed.** -/
theorem xClosed_take {A : List (List Ev)} (h : CallCompose.XClosed A) (m : Nat) :
    CallCompose.XClosed (A.take m) := by
  intro b y hy hk
  obtain ⟨hb, hy'⟩ := evAt_take_some hy
  obtain ⟨a, x, hx, hxk, hab⟩ := h b y hy' hk
  refine ⟨a, x, ?_, hxk, hab⟩
  rw [evAt_take_of_lt (by simp only [Lt] at hab; omega)]
  exact hx

theorem evTr_take_take {ls : List Lab} {k n : Nat} (h : k ≤ n) :
    evTr (ls.take k) = (evTr (ls.take n)).take k := by
  simp only [evTr, ← List.map_take, List.take_take, Nat.min_eq_left h]

/-- **`arm_alloc_refines_lsCLA` with the realized prefix exclusive-closed**
(`refines_of_itemSimQX`). -/
theorem arm_alloc_refines_lsCLAX {R : RL} (hR : R.Wf) (hsc : MemScopeLSC R)
    {g : ArmState → ArmState} (hg : AgreesAt R g)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      ThreadRefine.Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      ((∀ v m w, c ≠ .ret v m w) → ∀ v m w, cE ≠ .ret v m w) ∧
      (n = ls.length ∨ ∃ tE, PRun Policy.arm g (OkPriv R) (s, mon) (ls.take n) tE ∧
        RelQ R tE cE ∧ Pause R cE) ∧ CallCompose.XClosed (evTr (ls.take n)) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend, hx⟩ :=
    refines_of_itemSimQX (ItemSim.avoid (itemSim_lsCL hR hsc hg)) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.mono' (fun _ _ _ h => h.2) (SRun.fstP hs)),
    href, srun_avoid_ret (SRun.fstP hs), hend.imp_right fun ⟨tE, h1, h2, h3⟩ => ⟨tE, h1, h2.1, h3⟩,
    hx⟩

/-! ## The VCode tail of a done `return` -/

theorem rets_noDefs {us : List (Reg × Reg)} {ops : Array Operand}
    (h : (MInst.rets us).operands = .ok ops) : ops.toList.filter Operand.isDef = [] := by
  rw [operands_eq] at h
  simp only [MInst.visitOperands, StateT.run_bind] at h
  cases hu : (us.mapM (fun (x : Reg × Reg) => do
      let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run #[] with
  | error e => rw [hu] at h; cases h
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [hu, Driver.except_ok_bind] at h
    simp only [StateT.run_pure, Driver.except_pure, Driver.except_ok_bind,
      Except.ok.injEq] at h
    subst h
    exact Kill.asm_mapM_use us #[] s1 a hu

/-- **The VCode on its event-free way to a return steps or has returned.** -/
theorem vstep_or_ret_of_retFrom {vc : VCode} {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {vR : VState CV ArmState} {trR : List (List Ev)} {vV : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run vR) trR vV) (hnil : ∀ e ∈ trR, e = [])
    {us : List (Reg × Reg)} {outs : List CV} {w' : ArmState}
    (hret : VRetFrom vc (csem F fc X) vR us outs w') :
    (∃ c', VStep vc (csem F fc X) vV c') ∨ ∃ v w, vV = .ret v w := by
  obtain ⟨b1, k1, ρ1, w1, vb1, ops1, outs1, hstar, hvb1, hi1, hops1, hvals, hsem1⟩ := hret
  have hsem1' := hsem1
  simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem1'
  obtain ⟨rfl, rfl, -⟩ := hsem1'
  have hR : VStep vc (csem F fc X) (.run ⟨b1, k1, ρ1, w1⟩) (.ret (vuses ops1 ρ1) w1) := by
    refine .step hvb1 hi1 hops1 (by rw [hvals] at hsem1; exact hsem1) ?_ (.ret rfl)
    rw [rets_noDefs hops1]; rfl
  have hstar2 := star_of_vtrun_nil hr hnil
  rcases star_det (r := VStep vc (csem F fc X)) (fun _ _ _ h1 h2 => IselStep.vstep_det h1 h2)
      hstar hstar2 with h | h
  · cases h with
    | refl => exact .inl ⟨_, hR⟩
    | step h1 h2 =>
      obtain ⟨v, w, rfl⟩ := vstep_rets_ret (retsRet_csem F fc X)
        ⟨_, _, _, _, _, _, rfl, hvb1, hi1⟩ h1
      cases h2 with
      | refl => exact .inr ⟨_, _, rfl⟩
      | step h _ => cases h
  · cases h with
    | refl => exact .inl ⟨_, hR⟩
    | step h1 _ => exact .inl ⟨_, h1⟩

/-- **At a done `return`, the allocated configuration related to the VCode's tail steps**
(unless it has returned). -/
theorem doneRet_mstep {vc vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)}
    (H3 : PrepFacts vc vcp L ss ss') {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {rf : RFunc} {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt vcp rf cc ins a0) {keep : Reg → CV → CV} {r₀ : Reg → CV}
    {vR : VState CV ArmState} {trR : List (List Ev)} {vV vP : VConf CV ArmState}
    {cE : MConf CV ArmState}
    (h6 : VTRun vc (csem F fc X) (cEvs F fc) (.run vR) trR vV) (h7 : ∀ e ∈ trR, e = [])
    (h8 : PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' vV vP)
    (h9 : Backend.Proof.Match cc ins keep r₀ cE vP)
    {us : List (Reg × Reg)} {outs : List CV} {w' : ArmState}
    (h11 : VRetFrom vc (csem F fc X) vR us outs w') (hnr : ∀ v m w, cE ≠ .ret v m w) :
    ∃ cM', MStep vcp (csem F fc X) keep rf cE cM' := by
  have hds := (driverSem_csem F fc X).toDriverSemG
  rcases vstep_or_ret_of_retFrom h6 h7 h11 with ⟨c', hv⟩ | ⟨v, w, rfl⟩
  · obtain ⟨tgt', hvp⟩ := prep_fwd H3 hds h8 hv
    cases vP with
    | run vp =>
      cases cE with
      | run cm => exact sim_progress_at _ keep hc h9 hvp
      | ret => exact h9.elim
      | halt => exact h9.elim
    | ret => cases hvp
    | halt => cases hvp
  · cases h8 with
    | ret =>
      cases cE with
      | ret v m w => exact absurd rfl (hnr v m w)
      | run => exact h9.elim
      | halt => exact h9.elim

/-! ## Layers 2–4a with the end off `rets` -/

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **`CallRets.isel_alloc_refinesCRG` with the allocated end off `rets`**: where layer 2's
realization ends with a VCode step off `rets`, so does the allocated run. -/
theorem isel_alloc_refinesCRGN (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hX0 : NoCall X)
    {vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc vcp L ss ss')
    {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt vcp rf c ins a0) {keep : Reg → CV → CV} {r₀ : Reg → CV}
    {s : Clif.State} {vV vP : VState CV ArmState} {cM : MState CV ArmState}
    (hL2 : ∀ {tr : List (List Ev)} {cT : VConf CV ArmState},
      VTRun vc (csem F fc X) (cEvs F fc) (.run vV) tr cT →
      ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
        ((((n = tr.length ∧ (∃ c', VStep vc (csem F fc X) cT c') ∧ ¬ VAtRets vc cT) ∨
            Stop env p t) ∧ ∀ v, t = .ret v → n = tr.length) ∨
          ∃ s' vs', t = .run s' ∧ AtCR s' ∧ Match f ctx R gn bl A MR slots s' vs' ∧
            VTRun vc (csem F fc X) (cEvs F fc) (.run vs') (tr.drop n) cT))
    (hm3 : PMatch vc vcp (csem F fc X) (cEvs F fc) L ss' (.run vV) (.run vP))
    (hm4 : MatchRun c ins keep r₀ cM vP)
    {trM : List (List Ev)} {cE : MConf CV ArmState}
    (hr : MTRun vcp rf (csem F fc X) keep (cEvs F fc) (.run cM) trM cE) :
    ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
      ((((m = trM.length ∧ (∃ cM', MStep vcp (csem F fc X) keep rf cE cM') ∧
          ¬ ∃ b k allocs its mm ww vb us, cE = OpC b k allocs its mm ww ∧
            vcp.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us)) ∨ Stop env p t) ∧
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
            us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MR slots s'.mem w' ∧
            cm = (s'.mem.free (slots.map (·.2))).leave)) := by
  have hds := (driverSem_csem F fc X).toDriverSemG
  obtain ⟨trP, vPE, hrP, hmE, hthP⟩ := AllocThread.alloc_run (r₀ := r₀) hc hr (v := .run vP) hm4
  obtain ⟨trV, vVE, hrV, hpE, hthV⟩ := prep_run H3 hds (fun _ _ _ h => cEvs_setTargets F fc h)
    (fun _ _ _ _ _ _ h => csem_goto h) hrP hm3
  obtain ⟨n, trS, t, ψ, hn, hrun, href, hend⟩ := hL2 hrV
  have hth := Thin.trans hthV hthP
  have hlenV := vtrun_len (cEvs_len F fc) hrV
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
    rcases hend with ⟨h, ⟨cV', hv⟩, hnrV⟩ | h
    · refine .inl ⟨hfull (by omega), ?_, ?_⟩
      · cases vVE with
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
      · rintro ⟨b, k, allocs, its, mm, ww, vb, us, rfl, hvb, hi⟩
        cases vPE with
        | ret => exact hmE.elim
        | halt => exact hmE.elim
        | run vp =>
          obtain ⟨b', k', ρ, w''⟩ := vp
          obtain ⟨hb, hw, vb', a, out, hvb', hrunI, -, -⟩ := hmE
          simp only at hb hw hvb' hrunI
          subst hb hw
          obtain ⟨-, hk', -⟩ := runItems_op hrunI
          subst hk'
          obtain ⟨b0, vb0, he, hvb0, hi0⟩ := pmatch_rets H3 hds hpE hvb hi
          exact hnrV ⟨b0, _, _, _, vb0, us, he, hvb0, hi0⟩
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
    · have hth' : Thin (trV.take n) trM := by
        refine Thin.trans ?_ hth
        have := thin_append_nil (trV.take n) (trV.drop n) hnil
        rwa [List.take_append_drop] at this
      have htk' : Thin (trV.take n) (trM.take trM.length) := by rwa [List.take_length]
      obtain ⟨ψ', href3⟩ := hcarry htk'
      refine ⟨trM.length, trS, t, ψ', Nat.le_refl _, hrun, href3, .inr (.inr ⟨rfl, ?_⟩)⟩
      exact ⟨s', _, _, vVE, vPE, vals, cm, ht, hat, hm', hr', hnil, hpE, hmE, hs, hret⟩

/-- **Layers 2, 3 and 4a from related configurations, the end off `rets`**
(`isel_alloc_refinesCRGN` with `IselCallRet.isel_refinesCRN`). -/
theorem isel_alloc_refinesCRN (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
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
      ((((m = trM.length ∧ (∃ cM', MStep vcp (csem F fc X) keep rf cE cM') ∧
          ¬ ∃ b k allocs its mm ww vb us, cE = OpC b k allocs its mm ww ∧
            vcp.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us)) ∨ Stop env p t) ∧
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
            us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MR slots s'.mem w' ∧
            cm = (s'.mem.free (slots.map (·.2))).leave)) :=
  isel_alloc_refinesCRGN H hchk hX0 H3 hc (fun hrV => isel_refinesCRN H hchk hMR hMRw hX hm2 hrV)
    hm3 hm4 hr

/-- **Layers 2, 3 and 4a from the function's entry, the end off `rets`**
(`isel_alloc_refinesCRGN` with `IselCallRet.isel_refines_entryCRN`). -/
theorem isel_alloc_refines_entryCRN (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
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
      ((((m = trM.length ∧ (∃ cM', MStep vcp (csem F fc X) keep rf cE cM') ∧
          ¬ ∃ b k allocs its mm ww vb us, cE = OpC b k allocs its mm ww ∧
            vcp.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us)) ∨ Stop env p t) ∧
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
            us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MR slots s'.mem w' ∧
            cm = (s'.mem.free (slots.map (·.2))).leave)) :=
  isel_alloc_refinesCRGN H hchk hX0 H3 hc (vV := ⟨0, 0, ρ₀, w₀⟩) (fun hrV =>
    isel_refines_entryCRN H hchk hMR hMRw hX hMem hMRs hreg hB0 hcall hfunc hslots hbody hterm
      hregs hty hsig hmr hargs hrV) hm3 hm4 hr

end

/-! ## All layers -/

theorem sem_eq {RA : RL} (hgv : RA.gv = fun _ _ => False) : RA.sem = csem RA.F RA.ctx RA.X := by
  show csemV RA.gv RA.F RA.ctx RA.X = _
  rw [hgv, csemV_none]

/-- **`arm_isel_refinesG2N` with the realized prefix exclusive-closed**
(`arm_alloc_refines_lsCLAX`, `xClosed_take`). -/
theorem arm_isel_refinesG2NX {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {env : Clif.Env} {p : Clif.Program} (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {s : Clif.State} {cM : MState CV ArmState} {Rel : Clif.State → MConf CV ArmState → Prop}
    (hL : ∀ {trM : List (List Ev)} {cE : MConf CV ArmState},
      MTRun RA.vc RA.rf (csem RA.F RA.ctx RA.X) ckeep (cEvs RA.F RA.ctx) (.run cM) trM cE →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        ((((m = trM.length ∧ (∃ cM', MStep RA.vc (csem RA.F RA.ctx RA.X) ckeep RA.rf cE cM') ∧
            ¬ AtRets RA cE) ∨ Stop env p t) ∧ ∀ v, t = .ret v → m = trM.length) ∨
          (m = trM.length ∧ ∃ s', t = .run s' ∧ Rel s' cE)))
    {x : ArmState} {mon : Mon} (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE cE ∧ Pause RA cE ∧ (∀ v m w, cE ≠ .ret v m w) ∧ t = .run s' ∧
          Rel s' cE)) := by
  have hsem := sem_eq hgv
  obtain ⟨nA, trM, cE, ψA, hnA, hM, hAr, hnret, hend, hxA⟩ :=
    arm_alloc_refines_lsCLAX hR hsc hg hq hA hr
  have hnret' := hnret (fun v m w h => by cases h)
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
  refine ⟨k, trS, t, _, by omega, by rw [evTr_take_take (by omega : k ≤ nA)]; exact xClosed_take hxA k,
    hrun, RealizeCompiled.Refines.pairT_congr href2 hpair, ?_⟩
  rcases hendm with ⟨⟨h, ⟨cM', hmst⟩, hnrA⟩ | h, -⟩ | ⟨hfm, s', ht, hrel⟩
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
          rcases hrq with ⟨hq', -⟩ | hrt
          · exact srcStep_of_mstepC (coveredCodeC_of_lsC hsc) hgv hX hX0 hq' hmst
          · exact ThreadProgress.srcStep_of_retTail hX hrt hmst
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
    · exact absurd hrets hnrA
  · exact .inr (.inl h)
  · have hk' := hkfull (by simp [conv, hfm])
    rw [hlenA] at hk'
    rcases hend with h' | ⟨tE, hpre, hrq, hP⟩
    · exact .inl (hk'.trans h')
    · exact .inr (.inr ⟨tE, s', cE, hPA hnA hk' hpre, hrq, hP, hnret', ht, hrel⟩)

/-- **`CallLayers.arm_isel_refinesG2` with layers 2–4a's end off `rets`** (module doc): no end
at a `rets` item without the pause relation; at a pause, the allocated configuration has not
returned. -/
theorem arm_isel_refinesG2N {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {env : Clif.Env} {p : Clif.Program} (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {s : Clif.State} {cM : MState CV ArmState} {Rel : Clif.State → MConf CV ArmState → Prop}
    (hL : ∀ {trM : List (List Ev)} {cE : MConf CV ArmState},
      MTRun RA.vc RA.rf (csem RA.F RA.ctx RA.X) ckeep (cEvs RA.F RA.ctx) (.run cM) trM cE →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        ((((m = trM.length ∧ (∃ cM', MStep RA.vc (csem RA.F RA.ctx RA.X) ckeep RA.rf cE cM') ∧
            ¬ AtRets RA cE) ∨ Stop env p t) ∧ ∀ v, t = .ret v → m = trM.length) ∨
          (m = trM.length ∧ ∃ s', t = .run s' ∧ Rel s' cE)))
    {x : ArmState} {mon : Mon} (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE cE ∧ Pause RA cE ∧ (∀ v m w, cE ≠ .ret v m w) ∧ t = .run s' ∧
          Rel s' cE)) := by
  obtain ⟨k, trS, t, ψ, hk, -, h⟩ := arm_isel_refinesG2NX hR hsc hgv hg hX hX0 hL hq hA hr
  exact ⟨k, trS, t, ψ, hk, h⟩

/-- **`arm_isel_refinesCRGN` with the realized prefix exclusive-closed**
(`arm_isel_refinesG2NX`). -/
theorem arm_isel_refinesCRGNX {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (r₀ r) = ckeep r (regVal RA.s0 r))
    {s : Clif.State} {cM : MState CV ArmState} {x : ArmState}
    {mon : Mon}
    (hLA : ∀ {trM : List (List Ev)} {cE : MConf CV ArmState},
      MTRun RA.vc RA.rf (csem RA.F RA.ctx RA.X) ckeep (cEvs RA.F RA.ctx) (.run cM) trM cE →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        ((((m = trM.length ∧ (∃ cM', MStep RA.vc (csem RA.F RA.ctx RA.X) ckeep RA.rf cE cM') ∧
            ¬ AtRets RA cE) ∨ Stop env p t) ∧
            ∀ v, t = .ret v → m = trM.length) ∨
          (m = trM.length ∧ ∃ s' vV' vP' cM', t = .run s' ∧ AtCallS s' ∧ cE = .run cM' ∧
            Match f ctx R gn bl A MR slots s' vV' ∧
            PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
            MatchRun cc ins ckeep r₀ cM' vP') ∨
          (m = trM.length ∧ ∃ s' vR trR vV' vP' vals cm, t = .run s' ∧ AtRetS s' ∧
            Match f ctx R gn bl A MR slots s' vR ∧
            VTRun vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) (.run vR) trR vV' ∧
            (∀ e ∈ trR, e = []) ∧
            PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' vV' vP' ∧
            Backend.Proof.Match cc ins ckeep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
            ∃ us outs w', VRetFrom vc (csem RA.F RA.ctx RA.X) vR us outs w' ∧
              us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
              PrefixHold vals outs ∧ MR slots s'.mem w' ∧
              cm = (s'.mem.free (slots.map (·.2))).leave)))
    (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep r₀ cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots r₀ tE.1 s')) := by
  have hsem := sem_eq hgv
  let RelR : Clif.State → MConf CV ArmState → Prop := fun s' cE =>
    (∃ cM' vV' vP', AtCallS s' ∧ cE = .run cM' ∧ Match f ctx R gn bl A MR slots s' vV' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
      MatchRun cc ins ckeep r₀ cM' vP') ∨
    (AtRetS s' ∧ ∃ vR trR vV' vP' vals cm, Match f ctx R gn bl A MR slots s' vR ∧
      VTRun vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) (.run vR) trR vV' ∧
      (∀ e ∈ trR, e = []) ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' vV' vP' ∧
      Backend.Proof.Match cc ins ckeep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
      ∃ us outs w', VRetFrom vc (csem RA.F RA.ctx RA.X) vR us outs w' ∧
        PrefixHold vals outs ∧ MR slots s'.mem w' ∧
        cm = (s'.mem.free (slots.map (·.2))).leave)
  obtain ⟨k, trS, t, ψ, hk, hxk, hrun, href, hend⟩ := arm_isel_refinesG2NX hR hsc hgv hg hX
    hX0 (Rel := RelR) (fun hM => by
      obtain ⟨m, trS, t, ψ, hm, hrun, href, hendm⟩ := hLA hM
      refine ⟨m, trS, t, ψ, hm, hrun, href, ?_⟩
      rcases hendm with h | ⟨h1, s', vV', vP', cM', ht, hat, hcE, h5, h6, h7⟩ |
        ⟨h1, s', vR, trR, vV', vP', vals, cm, ht, hat, h5, h6, h7, h8, h9, h10, us, outs, w', h11,
          -, -, h12, h13, h14⟩
      · exact .inl h
      · exact .inr ⟨h1, s', ht, .inl ⟨cM', vV', vP', hat, hcE, h5, h6, h7⟩⟩
      · exact .inr ⟨h1, s', ht, .inr ⟨hat, vR, trR, vV', vP', vals, cm, h5, h6, h7, h8, h9, h10,
          us, outs, w', h11, h12, h13, h14⟩⟩) hq hA hr
  refine ⟨k, trS, t, ψ, hk, hxk, hrun, href, ?_⟩
  rcases hend with h | h | ⟨tE, s', cE, hpre, hrq, hP, hnret, ht, hrel⟩
  · exact .inl h
  · exact .inr (.inl h)
  rcases hrel with ⟨cM', vV', vP', hat, rfl, h5, h6, h7⟩ |
    ⟨hat, vR, trR, vV', vP', vals, cm, h5, h6, h7, h8, h9, h10, us0, outs, w', h11, h12, h13, h14⟩
  · exact .inr (.inr (.inl ⟨tE, s', vV', vP', cM', hpre, hrq, hP, ht, hat, h5, h6, h7⟩))
  refine .inr (.inr (.inr ⟨tE, s', hpre, ht, hat, ?_⟩))
  obtain ⟨cM', hmst⟩ := doneRet_mstep H3 hc h6 h7 h8 h9 h11 hnret
  rcases hP with hD | hcall | ⟨b, kk, allocs, its, m, w, vb, us, rfl, hvb, hi⟩
  · exfalso
    rw [← hsem] at hmst
    rcases hD with ⟨vals, m', w', rfl⟩ | ⟨w', rfl⟩ | hD
    · cases hmst
    · cases hmst
    · obtain ⟨evs, c'', hs⟩ : ∃ evs c'', SrcStep RA _ evs c'' := by
        rcases hrq with ⟨hq', -⟩ | hrt
        · exact srcStep_of_mstepC (coveredCodeC_of_lsC hsc) hgv hX hX0 hq' hmst
        · exact ThreadProgress.srcStep_of_retTail hX hrt hmst
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
  -- the prepared code's configuration is at the `rets`
  cases vP' with
  | ret => exact h9.elim
  | halt => exact h9.elim
  | run vs =>
    obtain ⟨b', k', ρ, w''⟩ := vs
    have h9' := h9
    obtain ⟨hb, hw, vb', a, out, hvb', hrunI, -, -⟩ := h9'
    simp only at hb hw hvb' hrunI
    subst hb hw
    obtain ⟨-, hk', -⟩ := runItems_op hrunI
    subst hk'
    obtain ⟨ops, hops, rfl, rfl, rfl⟩ := ret_link H3 h6 h7 h8 hvb hi h11
    obtain ⟨n, ops2, hops2, hgood, hpc, herr, hsp, hmem, hprog, hcs, hres⟩ :=
      rets_alloc hR hent hc hr₀ hrq h9 hvb hi
    rw [hops] at hops2; cases hops2
    exact ⟨b, kk, allocs, its, m, _, vb, _, ops, ρ, vals, cm, n, hrq, hvb, hi, hops, h10, h12,
      h13, h14, hgood, hpc, herr, hsp, hmem, hprog, hcs, hres⟩

/-- **All layers from a segment's start, layers 2–4a given with the end off `rets`, pausing at
calls and at returns with their contract** (module doc; `CallRetsEnd.arm_isel_refinesCRG`
without its two unresolved ends). -/
theorem arm_isel_refinesCRGN {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (r₀ r) = ckeep r (regVal RA.s0 r))
    {s : Clif.State} {cM : MState CV ArmState} {x : ArmState}
    {mon : Mon}
    (hLA : ∀ {trM : List (List Ev)} {cE : MConf CV ArmState},
      MTRun RA.vc RA.rf (csem RA.F RA.ctx RA.X) ckeep (cEvs RA.F RA.ctx) (.run cM) trM cE →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        ((((m = trM.length ∧ (∃ cM', MStep RA.vc (csem RA.F RA.ctx RA.X) ckeep RA.rf cE cM') ∧
            ¬ AtRets RA cE) ∨ Stop env p t) ∧
            ∀ v, t = .ret v → m = trM.length) ∨
          (m = trM.length ∧ ∃ s' vV' vP' cM', t = .run s' ∧ AtCallS s' ∧ cE = .run cM' ∧
            Match f ctx R gn bl A MR slots s' vV' ∧
            PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
            MatchRun cc ins ckeep r₀ cM' vP') ∨
          (m = trM.length ∧ ∃ s' vR trR vV' vP' vals cm, t = .run s' ∧ AtRetS s' ∧
            Match f ctx R gn bl A MR slots s' vR ∧
            VTRun vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) (.run vR) trR vV' ∧
            (∀ e ∈ trR, e = []) ∧
            PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' vV' vP' ∧
            Backend.Proof.Match cc ins ckeep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
            ∃ us outs w', VRetFrom vc (csem RA.F RA.ctx RA.X) vR us outs w' ∧
              us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
              PrefixHold vals outs ∧ MR slots s'.mem w' ∧
              cm = (s'.mem.free (slots.map (·.2))).leave)))
    (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep r₀ cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots r₀ tE.1 s')) := by
  obtain ⟨k, trS, t, ψ, hk, -, h⟩ :=
    arm_isel_refinesCRGNX hR hsc hgv hg hent hX hX0 H3 hc hr₀ hLA hq hA hr
  exact ⟨k, trS, t, ψ, hk, h⟩

/-- **All layers from related configurations, pausing at calls and at returns with their
contract, every end resolved** (module doc). -/
theorem arm_isel_refinesCRN {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
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
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (r₀ r) = ckeep r (regVal RA.s0 r))
    {s : Clif.State} {vV vP : VState CV ArmState} {cM : MState CV ArmState} {x : ArmState}
    {mon : Mon}
    (hm2 : Match f ctx R gn bl A MR slots s vV)
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV) (.run vP))
    (hm4 : MatchRun cc ins ckeep r₀ cM vP) (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep r₀ cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots r₀ tE.1 s')) :=
  arm_isel_refinesCRGN hR hsc hgv hg hent hX hX0 H3 hc hr₀
    (fun hM => isel_alloc_refinesCRN H hchk hMR hMRw hX hX0 H3 hc hm2 hm3 hm4 hM) hq hA hr

/-- **All layers from the activation's entry configuration, pausing at calls and at returns
with their contract, every end resolved** (`arm_isel_refinesCRGN` with
`isel_alloc_refines_entryCRN`). -/
theorem arm_isel_refines_entryCRN {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
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
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (m₀ (.reg r)) = ckeep r (regVal RA.s0 r))
    (hargs : ArgsAtEntry RA.F f.sig args w₀) {x : ArmState} {mon : Mon}
    (hq : Q RA x (MConf.init RA.rf m₀ w₀)) (hA : AInv RA (MConf.init RA.rf m₀ w₀))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep (fun r => m₀ (.reg r)) cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots (fun r => m₀ (.reg r)) tE.1 s')) :=
  arm_isel_refinesCRGN hR hsc hgv hg hent hX hX0 H3 hc hr₀ (s := cs)
    (cM := ⟨0, RA.rf.blocks[0]!.toList, m₀, w₀⟩)
    (fun hM => isel_alloc_refines_entryCRN (ρ₀ := fun _ => 0) H hchk hMR hMRw hX hX0 hMem hMRs
      hreg hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs H3 hc (hm3 _ _)
      (hm4 m₀ (fun _ => 0) w₀) hM) hq hA hr

/-- **`arm_isel_refinesCRN` with the realized prefix exclusive-closed** (`arm_isel_refinesCRGNX`;
#473 step (4): a segment's `XClosed` for `CallComposeT.RealizedT`). -/
theorem arm_isel_refinesCRNX {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
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
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (r₀ r) = ckeep r (regVal RA.s0 r))
    {s : Clif.State} {vV vP : VState CV ArmState} {cM : MState CV ArmState} {x : ArmState}
    {mon : Mon}
    (hm2 : Match f ctx R gn bl A MR slots s vV)
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV) (.run vP))
    (hm4 : MatchRun cc ins ckeep r₀ cM vP) (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep r₀ cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots r₀ tE.1 s')) :=
  arm_isel_refinesCRGNX hR hsc hgv hg hent hX hX0 H3 hc hr₀
    (fun hM => isel_alloc_refinesCRN H hchk hMR hMRw hX hX0 H3 hc hm2 hm3 hm4 hM) hq hA hr

/-- **`arm_isel_refines_entryCRN` with the realized prefix exclusive-closed**
(`arm_isel_refinesCRGNX`). -/
theorem arm_isel_refines_entryCRNX {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
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
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (m₀ (.reg r)) = ckeep r (regVal RA.s0 r))
    (hargs : ArgsAtEntry RA.F f.sig args w₀) {x : ArmState} {mon : Mon}
    (hq : Q RA x (MConf.init RA.rf m₀ w₀)) (hA : AInv RA (MConf.init RA.rf m₀ w₀))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep (fun r => m₀ (.reg r)) cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ RetEnd RA ra env p MR slots (fun r => m₀ (.reg r)) tE.1 s')) :=
  arm_isel_refinesCRGNX hR hsc hgv hg hent hX hX0 H3 hc hr₀ (s := cs)
    (cM := ⟨0, RA.rf.blocks[0]!.toList, m₀, w₀⟩)
    (fun hM => isel_alloc_refines_entryCRN (ρ₀ := fun _ => 0) H hchk hMR hMRw hX hX0 hMem hMRs
      hreg hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs H3 hc (hm3 _ _)
      (hm4 m₀ (fun _ => 0) w₀) hM) hq hA hr

end Concurrency.CallRetsN

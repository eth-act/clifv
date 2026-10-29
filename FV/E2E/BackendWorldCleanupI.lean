import FV.E2E.IselSimICleanup
import FV.E2E.BackendWorldI
import FV.E2E.DeadCleanupGot
import FV.E2E.DeadCleanupRegLevelPRS

/-!
# The per-function theorem with the final world, counted, on the cleanup path (SEM1, `docs/plans/uninit.md` §5.9)

`backend_correct_world_cleanup` (`FV/E2E/DeadCleanupWorld.lean`) for the counted VCode run, as
`backend_correct_worldPRI` (`FV/E2E/BackendWorldI.lean`) is for the legacy path:

* CLIF → counted VCode: `iselSim_relWI_cleanup` (`valueSemI`);
* the dead-code cleanup: `prune_correctW` (`prune_correct` for any world: the simulation
  `star_sim` is world-generic) for `valueSemI` (`valueSemI_pure`, `cmpOverwrite_counted`);
* `prepare`: `prep_soundW` with `DriverSemG.counted`;
* the GOT sites: `vRetFrom_gotV_valueI`/`vTrapFrom_gotV_valueI` (`valueSemI` → `valueSemVI (GotV vcp)`);
* VCode → Arm: `regLevelCorrect_world_value_worldPRS`.

**`backend_correct_world_cleanupPRI`**: the same conclusion as `backend_correct_worldPRI`, for
`CompiledCleanup`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-! ## The cleanup for any world -/

section
variable {W : Type}

private theorem entry_existsW {vc : VCode} {sem : ISem CV W}
    {a : Nat → CV} {w : W} {b k : Nat} {a1 : Nat → CV} {w1 : W} {vb : VBlock}
    (hs : Star (VStep vc sem) (.run ⟨0, 0, a, w⟩) (.run ⟨b, k, a1, w1⟩))
    (hb : vc.blocks[b]? = some vb) : ∃ vb0, vc.blocks[0]? = some vb0 := by
  cases hs with
  | refl => exact ⟨vb, hb⟩
  | step h _ => cases h with | step he _ _ _ _ _ => exact ⟨_, he⟩

theorem returns_cleanW {vc : VCode} {sem : ISem CV W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {a : Nat → CV} {w0 w : W} {us : List (Reg × Reg)} {vals : List CV}
    (h : VRetFrom vc sem ⟨0, 0, a, w0⟩ us vals w) :
    VRetFrom (clean vc) sem ⟨0, 0, a, w0⟩ us vals w := by
  obtain ⟨b, k, a1, w1, vb, ops, outs, hstar, hb, hi, hop, hv, hs⟩ := h
  obtain ⟨vb0, hb0⟩ := entry_existsW hstar hb
  obtain ⟨c1, hstar', hr⟩ := star_sim hp hcmp ht (rel_entry hb0 a w0) hstar
  obtain ⟨k', a', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop rfl rfl rfl
  refine ⟨b, k', a', w1, cleanBlock vc 0 vb, ops, outs, hstar', hb', hi', hop, ?_, hs⟩
  exact hv.trans hu

theorem traps_cleanW {vc : VCode} {sem : ISem CV W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {a : Nat → CV} {w0 : W} {code : Clif.TrapCode}
    (h : VTrapFrom vc sem ⟨0, 0, a, w0⟩ code) :
    VTrapFrom (clean vc) sem ⟨0, 0, a, w0⟩ code := by
  obtain ⟨b, k, a1, w1, vb, i, ops, outs, w', hstar, hb, hi, hop, hs, hc⟩ := h
  have hkeep : pureForm i = false := by
    cases he : pureForm i
    · rfl
    · have hn := (hp _ _ _ _ _ _ he hs).2
      cases hn
  have hkeepc : cmpForm i = false := by
    cases he : cmpForm i
    · rfl
    · have hn := (hcmp.1 _ _ _ _ _ _ he hs).1
      cases hn
  have hkeepj : isJump i = false := by
    cases he : isJump i
    · rfl
    · obtain ⟨l, rfl⟩ : ∃ l, i = .jump l := by cases i <;> simp at he; exact ⟨_, rfl⟩
      obtain ⟨-, j, hj⟩ := hcmp.2 _ _ _ _ _ _ hs
      cases hj
  obtain ⟨vb0, hb0⟩ := entry_existsW hstar hb
  obtain ⟨c1, hstar', hr⟩ := star_sim hp hcmp ht (rel_entry hb0 a w0) hstar
  obtain ⟨k', a', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop hkeep hkeepc hkeepj
  refine ⟨b, k', a', w1, cleanBlock vc 0 vb, i, ops, outs, w', hstar', hb', hi', hop, ?_, hc⟩
  rw [← hu]
  exact hs

/-- **`prune_correct` for any world.** -/
theorem prune_correctW {vc : VCode} {sem : ISem CV W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem) (ρ₀ : Nat → CV) (w₀ : W) :
    (∀ us vals w, VRetFrom vc sem ⟨0, 0, ρ₀, w₀⟩ us vals w →
      VRetFrom (prune vc) sem ⟨0, 0, ρ₀, w₀⟩ us vals w) ∧
    (∀ c, VTrapFrom vc sem ⟨0, 0, ρ₀, w₀⟩ c → VTrapFrom (prune vc) sem ⟨0, 0, ρ₀, w₀⟩ c) := by
  unfold prune
  cases h : vc.cfg with
  | error e => exact ⟨fun _ _ _ h => h, fun _ h => h⟩
  | ok p =>
    exact ⟨fun _ _ _ h' => returns_cleanW hp hcmp (terminated_of_cfg h) h',
      fun _ h' => traps_cleanW hp hcmp (terminated_of_cfg h) h'⟩

end

/-! ## The counted semantics' facts for the cleanup and `prepare` -/

theorem pureForm_isCallI {i : MInst} (h : pureForm i = true) : i.isCallI = false := by
  cases i <;> first | rfl | simp [pureForm] at h

theorem cmpForm_isCallI {i : MInst} (h : cmpForm i = true) : i.isCallI = false := by
  cases i <;> first | rfl | simp [cmpForm] at h

theorem counted_pure {sem : Nat → Sem}
    (hp : ∀ n i us w outs w' ctl, pureForm i = true →
      sem n i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    {i : MInst} {us : List CV} {w : Arm.ArmState × Nat} {outs : List CV}
    {w' : Arm.ArmState × Nat} {ctl : Ctl} (hi : pureForm i = true)
    (h : ISem.counted sem i us w = some (outs, w', ctl)) : w' = w ∧ ctl = .next := by
  obtain ⟨h1, h2⟩ := ISem.counted_some h
  obtain ⟨e1, e2⟩ := hp _ _ _ _ _ _ _ hi h1
  rw [pureForm_isCallI hi] at h2
  exact ⟨Prod.ext e1 h2, e2⟩

/-- **The counted semantics lets a compare's flags be overwritten** when every `sem n` does. -/
theorem cmpOverwrite_counted {sem : Nat → Sem} (h : ∀ n, CmpOverwrite (sem n)) :
    CmpOverwrite (ISem.counted sem) := by
  refine ⟨fun i us w outs w' ctl hi hs => ?_, fun l us w outs w' ctl hs => ?_⟩
  · obtain ⟨⟨w1, n⟩, ⟨w1', n'⟩⟩ := (w, w')
    obtain ⟨h1, h2⟩ := ISem.counted_some hs
    simp only [cmpForm_isCallI hi, Bool.false_eq_true, ↓reduceIte] at h2 h1
    obtain ⟨hc, hK, hJ⟩ := (h w.2).1 _ _ _ _ _ _ hi h1
    obtain ⟨wa, na⟩ := w
    obtain ⟨wb, nb⟩ := w'
    simp only at h1 h2 hK hJ
    subst h2
    refine ⟨hc, fun K us' r hK' hs' => ?_, fun j us' outs' ctl' hj hs' => ?_⟩
    · simp only [ISem.counted, Option.map_eq_some_iff] at hs' ⊢
      obtain ⟨r', hr', e⟩ := hs'
      exact ⟨r', hK K us' r' hK' hr', e⟩
    · obtain ⟨g1, g2⟩ := ISem.counted_some hs'
      simp only at g1 g2
      have hnc : j.isCallI = false := by
        cases hjc : j.isCallI with
        | false => rfl
        | true => rw [hjc] at g2; simp at g2
      have := hJ j us' outs' ctl' hj g1
      simp only [ISem.counted, this, Option.map_some, hnc, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨h1, h2⟩ := ISem.counted_some hs
    obtain ⟨e1, j, e2⟩ := (h w.2).2 _ _ _ _ _ _ h1
    refine ⟨Prod.ext e1 ?_, j, e2⟩
    rw [h2]; rfl

/-- **`DriverSemG` of a counted family** from `DriverSemG` of every member. -/
theorem DriverSemG.counted {sem : Nat → Sem} (h : ∀ n, DriverSemG (sem n)) :
    DriverSemG (ISem.counted sem) where
  jump := fun l w => by
    obtain ⟨w, n⟩ := w
    simp only [ISem.counted, (h n).jump l w, Option.map_some]
    rfl
  rename := fun g gn hg i => by
    funext uses w
    obtain ⟨w, n⟩ := w
    simp only [ISem.counted, (h n).rename g gn hg i, MInst.isCallI_mapRegs]
  retarget := fun i ls i' hs => by
    funext uses w
    obtain ⟨w, n⟩ := w
    simp only [ISem.counted, (h n).retarget i ls i' hs, MInst.isCallI_setTargets hs]

/-! ## The GOT sites of the counted value run -/

theorem valueSemV_sub {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {i : MInst} {uses : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl}
    (h : valueSemV gv F ctx X i uses w = some r) : valueSem F ctx X i uses w = some r := by
  by_cases hp : specForm i = true
  · simpa [valueSemV, valueSem, hp] using h
  · simp only [valueSemV, hp, Bool.false_eq_true, ↓reduceIte] at h
    simp only [valueSem, hp, Bool.false_eq_true, ↓reduceIte]
    exact csemV_sub h

section
variable {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {XI : ExtSemI}

/-- **One counted value step** keeps the GOT invariant and is a step of `valueSemVI (GotV vc)`. -/
theorem gotInvI_step_value {s : VState CV (Arm.ArmState × Nat)}
    {c' : VConf CV (Arm.ArmState × Nat)}
    (hI : GotInvI vc XI s) (h : VStep vc (valueSemI F ctx XI) (.run s) c') :
    VStep vc (valueSemVI (GotV vc) F ctx XI) (.run s) c' ∧
      ∀ s', c' = .run s' → GotInvI vc XI s' := by
  obtain ⟨b, k, ρ, ⟨w, m⟩⟩ := s
  cases h with
  | @step _ _ _ _ vb i ops outs w' ctl _ hvb hi hops hsem hlen hnext =>
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => valueSem F ctx (XI.at n)) hsem
  have hst1 : VStep vc (valueSem F ctx (XI.at m)) (.run ⟨b, k, ρ, w⟩) (c'.mapW Prod.fst) :=
    VStep.step hvb hi hops hs1 hlen (VNext_mapW hnext)
  have hI' : GotInv vc (XI.at m) ⟨b, k, ρ, w⟩ := hI
  obtain ⟨hst2, hinv⟩ := gotInv_step_value hI' hst1
  refine ⟨?_, fun s' hc => ?_⟩
  · cases hst2 with
    | step hvb2 hi2 hops2 hsem2 hlen2 hnext2 =>
      rw [hvb] at hvb2; cases hvb2
      rw [hi] at hi2; cases hi2
      rw [hops] at hops2; cases hops2
      have e := valueSemV_sub hsem2
      rw [show valueSem F ctx (XI.at m) _ _ w = some (outs, w'.1, ctl) from hs1] at e
      cases e
      refine VStep.step hvb hi hops ?_ hlen hnext
      show (valueSemV (GotV vc) F ctx (XI.at m) i _ w).map _ = _
      rw [hsem2]
      simp only [Option.map_some]
      rw [← hs2]
  · subst hc
    exact hinv _ rfl

theorem gotInvI_star_value {s s' : VState CV (Arm.ArmState × Nat)} (hI : GotInvI vc XI s)
    (h : Star (VStep vc (valueSemI F ctx XI)) (.run s) (.run s')) :
    Star (VStep vc (valueSemVI (GotV vc) F ctx XI)) (.run s) (.run s') ∧ GotInvI vc XI s' := by
  generalize ha : (VConf.run s : VConf CV (Arm.ArmState × Nat)) = a at h
  generalize hb : (VConf.run s' : VConf CV (Arm.ArmState × Nat)) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := gotInvI_step_value hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

/-- **A returning counted value run is one of `valueSemVI (GotV vc)`.** -/
theorem vRetFrom_gotV_valueI {ρ₀ : Nat → CV} {w₀ : Arm.ArmState × Nat} {us : List (Reg × Reg)}
    {vals : List CV} {w : Arm.ArmState × Nat}
    (h : VRetFrom vc (valueSemI F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w) :
    VRetFrom vc (valueSemVI (GotV vc) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := gotInvI_star_value
    (show GotInvI vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1) hs
  refine ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, ?_⟩
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => valueSem F ctx (XI.at n)) hsem
  have hv : valueSemV (GotV vc) F ctx (XI.at w₁.2) (.rets us) vals w₁.1 =
      some (outs, w.1, .ret) := by
    simp only [valueSemV, specForm, pureForm, cmpForm, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte]
    rw [csemV_eq fun info h => by rcases h with h | ⟨_, h⟩ <;> cases h]
    simpa [valueSem, specForm, pureForm, cmpForm] using hs1
  simp only [valueSemVI, ISem.counted, hv, Option.map_some]
  rw [← hs2]

/-- **A trapping counted value run is one of `valueSemVI (GotV vc)`.** -/
theorem vTrapFrom_gotV_valueI {ρ₀ : Nat → CV} {w₀ : Arm.ArmState × Nat} {c : Clif.TrapCode}
    (h : VTrapFrom vc (valueSemI F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c) :
    VTrapFrom vc (valueSemVI (GotV vc) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨hs', -⟩ := gotInvI_star_value
    (show GotInvI vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc⟩
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => valueSem F ctx (XI.at n)) hsem
  have hp : specForm i = false := by
    cases he : specForm i
    · rfl
    · have hs : mspec ctx.slotBase i (vuses ops ρ) w.1 = some (outs, w'.1, .halt) := by
        simpa [valueSem, he] using hs1
      have hn := mspec_spec_next he hs
      cases hn
  have hsem0 : csem F ctx (XI.at w.2) i (vuses ops ρ) w.1 = some (outs, w'.1, .halt) := by
    simpa [valueSem, hp] using hs1
  obtain ⟨-, hform⟩ := csem_halt hsem0
  have hv : valueSemV (GotV vc) F ctx (XI.at w.2) i (vuses ops ρ) w.1 =
      some (outs, w'.1, .halt) := by
    simp only [valueSemV, hp, Bool.false_eq_true, ↓reduceIte]
    rw [csemV_eq fun info h => by
      rcases h with rfl | ⟨_, rfl⟩ <;> rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> cases e]
    exact hsem0
  simp only [valueSemVI, ISem.counted, hv, Option.map_some]
  rw [← hs2]

end

/-! ## The per-function theorem -/

/-- **The per-function theorem with the final world, counted, on the cleanup path** (see the
module doc; `backend_correct_worldPRI` for `CompiledCleanup`). -/
theorem backend_correct_world_cleanupPRI {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s)) := by
  have hI := iselSim_relWI_cleanup hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs
    htr fuel
  have hPr := prune_correctW (vc := vc) (sem := valueSemI F ⟨fa.k, af.slotBase⟩ XI)
    (fun _ _ _ _ _ _ hi hs => counted_pure (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) hi hs)
    (cmpOverwrite_counted fun n => valueSem_cmpOverwrite _ _ _) (fun _ => 0) (w₀, 0)
  have hP := prep_soundW (DriverSemG.counted fun m =>
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk (fun _ => 0)
    (w₀, 0)
  have hM6 : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
      (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
      ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ → _ :=
    fun H G base ra Kp cc P R s he => by
      have h := regLevelCorrect_world_value_worldPRS hc.check hc.alloc hc.emit hc.layout
        (XI := XI) (H := H) (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree
        he.proph he.regp (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
        (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra Kp cc P R s he => ?_⟩
  · obtain ⟨us, outs, ⟨w, nc⟩, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra Kp cc P R s he => ?_⟩
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      (hM6 H G base ra Kp cc P R s he).1 us outs w nc
        (vRetFrom_gotV_valueI (hP.1 _ _ _ (hPr.1 _ _ _ hv)))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · exact (hM6 H G base ra Kp cc P R s he).2 c'
      (vTrapFrom_gotV_valueI (hP.2 c' (hPr.2 c' (hI.2 c' hrun))))

end E2E

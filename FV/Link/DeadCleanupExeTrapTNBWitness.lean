import FV.Link.DeadCleanupExeTrapTWitness
import FV.Link.DeadCleanupExeTrapTNB

/-!
# Witness: the `try_call` callee-trap source theorems without the memory bound apply (A2/B1)

`DeadCleanupExeTrapTWitness`'s executable (`f(x, y)` does `try_call h(x, y)`, `h(x, y) = x / y`,
compiled by `compileExeU`): its source program is the compiled program `{f, h}` (no `i128`), and

* `src_run_trapsT`: the source run of `f` on `(41, 0)` traps with `int_divz` inside `h`;
* `src_noMemTrapT`: it has no load/store trap (`NoMemTrap`);
* `cs0_trapsDT_all`: the run premise `TrapsDT` holds at every depth;
* `peak_trapsDT_all`: the peak run premise holds: `(L.std.peak F).TrapsDT 1 fF cs0` for every
  fuel `F` (`LinkSys.peak`), and `src_depthLeT`: the source run's call depth is at most `1`;
* `exec_source_trapsT`, `exec_source_trapsT_peak`:
  `Link.DeadCleanup.compileExe_correct_source_trapT_nobnd` and
  `compileExe_correct_source_trapT_peak_nobnd` with every premise discharged but the entry
  contract (`Image.Intact`, `OutsideCall`, `ClifRun` of `r`) — in particular without the source
  run's memory bound: the executable machine's run reaches a state at a trap with `int_divz`
  (`TrapAtE`).
-/

namespace Link.DeadCleanup.TrapTWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver Opt.Legalize128
open Link.DeadCleanup.TrapWitness (srcH fiH sig2 divStmt fH extH v41 v0 regs0 csH csH_step
  csH_reach)

/-- A step fact transfers across equal programs. -/
theorem step_prog_congr {E : Clif.Env} {p q : Clif.Program} {o : Clif.StepResult}
    (hpq : p = q) (h : Clif.step E p cs0 = o) : Clif.step E q cs0 = o := by
  cases hpq; exact h

/-- A stuck step of `cs0` in an environment: no further step, so the run only reaches `cs0`. -/
theorem cs0_reach_stuck {E : Clif.Env} {p : Clif.Program} {m : String}
    (h : Clif.step E p cs0 = .stuck m) :
    ∀ s, Reach E p cs0 s → s = cs0 := by
  intro s hr
  cases hr with
  | refl => rfl
  | step h1 _ =>
    rw [h] at h1
    cases h1

/-- A trapped step of `cs0` in an environment: no further step, so the run only reaches `cs0`. -/
theorem cs0_reach_trap {E : Clif.Env} {p : Clif.Program} {c : Clif.TrapCode}
    (h : Clif.step E p cs0 = .trapped c) :
    ∀ s, Reach E p cs0 s → s = cs0 := by
  intro s hr
  cases hr with
  | refl => rfl
  | step h1 _ =>
    rw [h] at h1
    cases h1

/-! ## The receipt of the source program -/

/-- The source program is `{f, h}`, in the source domain (`SrcScopeB`), without `i128`. -/
def chkS : Bool :=
  decide (spec.inputCleanup.srcProg = P0) && SrcScopeB spec.inputCleanup &&
    decide (mentions128 fF = false) && decide (mentions128 fH = false)

set_option maxRecDepth 100000 in
theorem chkS_true : chkS = true := by native_decide

theorem srcP : spec.inputCleanup.srcProg = P0 := by
  have h := chkS_true
  simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem hsrc : SrcScopeB spec.inputCleanup = true := by
  have h := chkS_true
  simp only [chkS, Bool.and_eq_true] at h
  exact h.1.1.2

theorem fF_plain : mentions128 fF = false := by
  have h := chkS_true
  simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem fH_plain : mentions128 fH = false := by
  have h := chkS_true
  simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem hlf : legalize fF = fF := Opt.Legal.Complete.legalize_of_not_mentions fF_plain

theorem hfP0 : P0.func? "f" = some fF := by
  have h := hf
  rw [P_eq] at h
  exact h

/-! ## The source run -/

/-- `h`'s activation entered from `f`'s `try_call` (the source run's second state): `f`'s frame
waits at the normal-return `jump`, the callee's results go to the fresh value `4`. -/
def cs1 : Clif.State :=
  ⟨⟨fH, regs0, [], [divStmt], .ret [2]⟩,
    [(⟨fF, regs0, [], [], .jump {block := 1, args := [4]}⟩, [4])], {}⟩

theorem cs0_step_src (E : Clif.Env) : Clif.step E P0 cs0 = .next cs1 := by
  rw [Clif.step_try E P0 cs0 rfl rfl]
  show Opt.callCont E P0 (Clif.tryState cs0 bc0) [] [4] extH [v41, v0] = _
  simp only [Opt.callCont, extH, show P0.func? "h" = some fH from rfl,
    beq_self_eq_true, Bool.and_self, eq_self_iff_true, if_true]
  rfl

theorem cs1_step (E : Clif.Env) (p : Clif.Program) : Clif.step E p cs1 = .trapped .intDivz :=
  Opt.step_eq_lift_of (r := .trap .intDivz) rfl (fun _ h => nomatch h)

/-- **The source run of `f` on `(41, 0)` traps with `int_divz`** (in `h`). -/
theorem src_run_traps :
    Clif.runLoop closedBase.env spec.inputCleanup.srcProg 3 cs0 = .trapped .intDivz := by
  rw [srcP, Clif.runLoop_succ', cs0_step_src]
  show Clif.runLoop closedBase.env P0 (1 + 1) cs1 = _
  rw [Clif.runLoop_succ', cs1_step]; rfl

/-- **No load/store trap** in the source run. -/
theorem src_noMemTrap :
    Opt.Legal.NoMemTrap closedBase.env spec.inputCleanup.srcProg cs0 := by
  rw [srcP]
  intro s hs
  have hs' : s = cs0 ∨ s = cs1 := by
    cases hs with
    | refl => exact .inl rfl
    | step h1 h2 =>
      rw [cs0_step_src] at h1
      cases h1
      cases h2 with
      | refl => exact .inr rfl
      | step h3 _ => rw [cs1_step] at h3; cases h3
  rcases hs' with rfl | rfl
  · intro c st rest h
    rw [cs0_step_src] at h
    cases h
  · intro c st rest _ hb
    simp only [cs1, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact ⟨fun _ _ _ _ _ h => (nomatch h), fun _ _ _ _ _ _ h => (nomatch h)⟩

/-- **The source run of `f` on `(41, 0)` has call depth at most `1`**. -/
theorem src_depthLe : Clif.DepthLe closedBase.env spec.inputCleanup.srcProg 1 cs0 := by
  rw [srcP]
  intro u hu
  cases hu with
  | refl => exact Nat.zero_le _
  | next h1 h2 =>
    rw [cs0_step_src] at h1
    cases h1
    cases h2 with
    | refl => exact Nat.le_refl _
    | next h3 _ => rw [cs1_step] at h3; cases h3

/-! ## The run premise at every depth -/

/-- The callee `h`'s entry makes no calls, so its run has call depth `0`. -/
theorem depthH0 : Clif.DepthLe L.base P0 0 csH := by
  intro u hu
  cases hu with
  | refl => exact Nat.le_refl _
  | next h1 _ => rw [csH_step] at h1; cases h1

theorem peakP (F : Nat) : (L.std.peak F).P = P0 := stdP

theorem peakPb (F : Nat) : (L.std.peak F).P.bare = P0.bare := by rw [peakP]

theorem LP : L.P = P0 := stdP

/-- At callee-fuel `0`, `h`'s run from its entry on `(41, 0)` runs out of fuel. -/
theorem link_h0 :
    ∃ G, (Clif.linkEnvR L.std.P L.std.base (L.std.crun 0)).extern "h" = some G ∧
      G [v41, v0] cs0.mem = .outOfFuel := by
  rw [stdP, Clif.linkEnvR_some (show P0.func? "h" = some fH from rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [csH_init]
  dsimp only
  rfl

/-- At callee-fuel `F ≥ 1` under `LinkSys.peak F` (callee runs of fuel `F` and depth `1`), `h`'s
run from its entry on `(41, 0)` traps with `int_divz`. -/
theorem link_hD (F : Nat) (hF : 0 < F) :
    ∃ G, (Clif.linkEnvR L.std.P L.std.base (Clif.runD L.std.base L.std.P F 1)).extern "h" =
      some G ∧ G [v41, v0] cs0.mem = .trapped .intDivz := by
  rw [stdP, Clif.linkEnvR_some (show P0.func? "h" = some fH from rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [csH_init]
  dsimp only
  show Clif.runD L.base P0 F 1 csH = _
  rw [Clif.runD, if_pos ⟨by omega, depthH0⟩]
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  rw [Clif.runLoop_succ', csH_step]; rfl

/-- Under `LinkSys.peak 0` (callee runs of fuel `0`), `h`'s run from its entry on `(41, 0)` runs
out of fuel. -/
theorem link_hD0 :
    ∃ G, (Clif.linkEnvR L.P L.base (Clif.runD L.base L.P 0 1)).extern "h" = some G ∧
      G [v41, v0] cs0.mem = .outOfFuel := by
  rw [LP, Clif.linkEnvR_some (show P0.func? "h" = some fH from rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [csH_init]
  dsimp only
  show Clif.runD L.base P0 0 1 csH = _
  rw [Clif.runD, if_pos ⟨by omega, depthH0⟩]
  rfl

/-- `f`'s step is stuck when the `try_call`'s callee runs out of fuel. -/
theorem cs0_step_oof (E : Clif.Env) {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hE : E.extern "h" = some G) (hG : G [v41, v0] cs0.mem = .outOfFuel) :
    ∃ m, Clif.step E P0.bare cs0 = .stuck m := by
  refine ⟨s!"extern %{extH.name} ran out of fuel", ?_⟩
  rw [Clif.step_try E P0.bare cs0 rfl rfl,
    show Clif.tryPre cs0.frame 0 et = .ok (1, 4, bc0) from rfl]
  simp only [Clif.StepResult.ofRes_ok]
  rw [show Opt.callArgs (Clif.tryState cs0 bc0).frame 0 [0, 1] = .ok (extH, [v41, v0]) from rfl]
  simp only [Clif.StepResult.ofRes_ok, Opt.callCont, show extH.name = "h" from rfl,
    show (Clif.tryState cs0 bc0).mem = cs0.mem from rfl,
    show P0.bare.func? "h" = none from rfl, hE, hG]

/-- **The run premise `TrapsDT` holds at every depth** for `f`'s run on `(41, 0)`: at depth `0`
the `try_call`'s callee runs out of fuel (no trap), at depth `K + 1` its trap is the call of
`h`, whose activation satisfies the premise (`csH_trapsDT` for every depth). -/
theorem cs0_trapsDT_all (K : Nat) : L.std.TrapsDT K fF cs0 := by
  rw [LinkSys.trapsDT_eq]
  have hreach : ∀ s, Reach (Clif.linkEnvR L.std.P L.std.base (L.std.crun K)) L.std.P.bare cs0 s →
      s = cs0 := by
    intro s hr
    cases hr with
    | refl => rfl
    | step h1 _ =>
      cases K with
      | zero =>
        obtain ⟨G, hG, hGt⟩ := link_h0
        obtain ⟨m, hm⟩ := cs0_step_oof _ hG hGt
        rw [stdP] at h1 hm
        rw [hm] at h1; cases h1
      | succ K =>
        obtain ⟨G, hG, hGt⟩ := link_h (K + 1) (by omega)
        have := cs0_step _ hG hGt
        rw [stdP] at h1 this
        rw [this] at h1; cases h1
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s st rest _ _ _ hr hb _ => ?_,
    fun s _ _ _ hr _ ht => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := hreach s hr; cases hb
  · obtain rfl := hreach s hr; cases hb
  · obtain rfl := hreach s hr; cases ht
  · cases K with
    | zero =>
      obtain ⟨G, hG, hGt⟩ := link_h0
      have hE : (L.std.envR 0 fF).extern "h" = some G := by
        rw [L.std.envR_of (.inr mayCall_h)]; exact hG
      obtain ⟨m, hm⟩ := cs0_step_oof _ hE hGt
      cases fuel with
      | zero => cases hrun
      | succ n =>
        rw [Clif.runLoop_succ', stdP, hm] at hrun
        cases hrun
    | succ K =>
      obtain ⟨G, hG, hGt⟩ := link_h (K + 1) (by omega)
      have hE : (L.std.envR (K + 1) fF).extern "h" = some G := by
        rw [L.std.envR_of (.inr mayCall_h)]; exact hG
      have hstepR : Clif.step (L.std.envR (K + 1) fF) L.std.P.bare cs0 = .trapped .intDivz := by
        rw [stdP]; exact cs0_step _ hE hGt
      have hQ : L.std.covQ (L.std.TrapsDTn (K + 1)) "h" [v41, v0] cs0.mem := by
        intro h cs hpf hinit
        rw [stdP, show P0.func? "h" = some fH from rfl] at hpf
        cases hpf
        rw [stdP, csH_init] at hinit
        cases hinit
        exact csH_trapsDT K
      have hEc : (cutEnv (L.std.envR (K + 1) fF)
          (L.std.covQ (L.std.TrapsDTn (K + 1)))).extern "h" =
          some fun vals cm => cutO (L.std.covQ (L.std.TrapsDTn (K + 1))) "h" vals cm (G vals cm) := by
        simp only [cutEnv, hE, Option.map_some]
      have hGc : cutO (L.std.covQ (L.std.TrapsDTn (K + 1))) "h" [v41, v0] cs0.mem
          (G [v41, v0] cs0.mem) = .trapped .intDivz := by
        unfold cutO
        rw [if_neg (fun h => h.2 hQ)]
        exact hGt
      cases fuel with
      | zero => cases hrun
      | succ n =>
        rw [Clif.runLoop_succ', hstepR] at hrun
        rw [Clif.runLoop_succ', stdP, cs0_step _ hEc hGc]
        exact hrun

/-! ## The run premise at depth `1` under `LinkSys.peak F`, for every fuel `F` -/

/-- `h`'s activation satisfies the run premise at depth `0` under `LinkSys.peak F` for every
fuel `F`: its run traps at its division, an explicitly trapping instruction (the callee
environment is never consulted, whatever its fuel). -/
theorem peak_trapsDT0 (F : Nat) : (L.std.peak F).TrapsDT 0 fH csH := by
  rw [LinkSys.trapsDT_eq]
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · rw [peakP] at hr; obtain rfl := csH_reach hr
    simp only [csH, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inl rfl
  · rw [peakP] at hr; obtain rfl := csH_reach hr
    simp only [csH, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · rw [peakP] at hr; obtain rfl := csH_reach hr; cases hb
  · cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ', csH_step] at hrun ⊢
      exact hrun

/-- **The run premise under `LinkSys.peak 0`**: the `try_call`'s callee runs out of fuel, so
`f`'s step is stuck and the run has no trap site. -/
theorem peak_trapsDT1_0 : (L.std.peak 0).TrapsDT 1 fF cs0 := by
  rw [LinkSys.trapsDT_eq]
  obtain ⟨G, hG, hGt⟩ := link_hD0
  have hE' : ((L.std.peak 0).envR 1 fF).extern "h" = some G := by
    rw [(L.std.peak 0).envR_of (.inr mayCall_h)]; exact hG
  obtain ⟨m, hm⟩ := cs0_step_oof (Clif.linkEnvR (L.std.peak 0).P (L.std.peak 0).base
    ((L.std.peak 0).crun 1)) hG hGt
  have hEL : Clif.step (Clif.linkEnvR (L.std.peak 0).P (L.std.peak 0).base
      ((L.std.peak 0).crun 1)) (L.std.peak 0).P.bare cs0 = .stuck m :=
    step_prog_congr (peakPb 0).symm hm
  obtain ⟨m2, hm2⟩ := cs0_step_oof _ hE' hGt
  have hmE : Clif.step ((L.std.peak 0).envR 1 fF) (L.std.peak 0).P.bare cs0 = .stuck m2 :=
    step_prog_congr (peakPb 0).symm hm2
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s st rest _ _ _ hr hb _ => ?_,
    fun s _ _ _ hr _ ht => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := cs0_reach_stuck hEL s hr; cases hb
  · obtain rfl := cs0_reach_stuck hEL s hr; cases hb
  · obtain rfl := cs0_reach_stuck hEL s hr; cases ht
  · cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ'] at hrun
      rw [hmE] at hrun
      cases hrun

/-- **The run premise under `LinkSys.peak F` for `0 < F`**: `f`'s trap is the `try_call` of `h`,
whose activation satisfies the premise at depth `0` (`peak_trapsDT0`). -/
theorem peak_trapsDT1_pos (F : Nat) (hF : 0 < F) : (L.std.peak F).TrapsDT 1 fF cs0 := by
  rw [LinkSys.trapsDT_eq]
  obtain ⟨G, hG, hGt⟩ := link_hD F hF
  have hE : ((L.std.peak F).envR 1 fF).extern "h" = some G := by
    rw [(L.std.peak F).envR_of (.inr mayCall_h)]; exact hG
  have hm := cs0_step (Clif.linkEnvR (L.std.peak F).P (L.std.peak F).base
    ((L.std.peak F).crun 1)) hG hGt
  have hEL : Clif.step (Clif.linkEnvR (L.std.peak F).P (L.std.peak F).base
      ((L.std.peak F).crun 1)) (L.std.peak F).P.bare cs0 = .trapped .intDivz :=
    step_prog_congr (peakPb F).symm hm
  have hstepR : Clif.step ((L.std.peak F).envR 1 fF) (L.std.peak F).P.bare cs0 =
      .trapped .intDivz := by
    rw [peakP]; exact cs0_step _ hE hGt
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s st rest _ _ _ hr hb _ => ?_,
    fun s _ _ _ hr _ ht => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := cs0_reach_trap hEL s hr; cases hb
  · obtain rfl := cs0_reach_trap hEL s hr; cases hb
  · obtain rfl := cs0_reach_trap hEL s hr; cases ht
  · have hQ : (L.std.peak F).covQ ((L.std.peak F).TrapsDTn 1) "h" [v41, v0] cs0.mem := by
      intro h cs hpf hinit
      rw [peakP, show P0.func? "h" = some fH from rfl] at hpf
      cases hpf
      rw [peakP, csH_init] at hinit
      cases hinit
      exact peak_trapsDT0 F
    have hEc : (cutEnv ((L.std.peak F).envR 1 fF)
        ((L.std.peak F).covQ ((L.std.peak F).TrapsDTn 1))).extern "h" =
        some fun vals cm => cutO ((L.std.peak F).covQ ((L.std.peak F).TrapsDTn 1)) "h" vals cm
          (G vals cm) := by
      simp only [cutEnv, hE, Option.map_some]
    have hGc : cutO ((L.std.peak F).covQ ((L.std.peak F).TrapsDTn 1)) "h" [v41, v0] cs0.mem
        (G [v41, v0] cs0.mem) = .trapped .intDivz := by
      unfold cutO
      rw [if_neg (fun h => h.2 hQ)]
      exact hGt
    cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ', hstepR] at hrun
      rw [Clif.runLoop_succ', peakP, cs0_step _ hEc hGc]
      exact hrun

/-- **The peak run premise at every fuel** for `f`'s run on `(41, 0)`. -/
theorem peak_trapsDT_all (F : Nat) : (L.std.peak F).TrapsDT 1 fF cs0 := by
  rcases Nat.eq_zero_or_pos F with rfl | hF
  · exact peak_trapsDT1_0
  · exact peak_trapsDT1_pos F hF

/-! ## The source theorems apply -/

/-- **Non-vacuity of `Link.DeadCleanup.compileExe_correct_source_trapT_nobnd`**: the source run
of `f` on `(41, 0)` traps with `int_divz` inside the `try_call`'s callee `h`, and for every
machine state `r` meeting the entry contract of an outside call of `f` (`Image.Intact`,
`OutsideCall`, `ClifRun`), the run of the written executable `file` from `r` reaches a state at
a trap with `int_divz` (every other premise discharged, without a memory bound of the source
run). -/
theorem exec_source_trapsT {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [v41, v0] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [v41, v0] cs0) :
    Clif.runLoop closedBase.env spec.inputCleanup.srcProg 3 cs0 = .trapped .intDivz ∧
    ∃ k, TrapAtE spec.inputCleanup closedBase .intDivz
      (runX (step spec.inputCleanup closedBase file) k r) := by
  rw [← hlf] at ho hr
  have hfS : spec.inputCleanup.srcProg.func? "f" = some fF := by rw [srcP]; exact hfP0
  have hcs : ClifEntry fF [v41, v0] cs0 := clifEntry_initState (p := P0) rfl cs0_init
  have hs : sig128 fF.sig = false := rfl
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fF.sig.params).getD []) [v41, v0] [v41, v0] := by
    obtain ⟨gs, hgs, hG⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_params hs)
    rw [hgs, Option.getD_some]
    exact Opt.Legal.expRel_refl_plain hG (Opt.Legal.sig128_params hs) rfl
  have hlegal : (∃ f ∈ spec.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk closedBase.env ∧ Opt.Legal.ExtLegal closedBase.env ∧
        Opt.Legal.EnvKeepsBounded closedBase.env := by
    rintro ⟨g, hg, hm⟩
    rw [srcP] at hg
    simp only [P0, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [fF_plain] at hm; cases hm
    · rw [fH_plain] at hm; cases hm
  have H := (compileExe_correct_source_trapT_nobnd compile_eq hsrc closedBase baseOk
    (hooksSim_closed _) baseTrapsOk hlegal (fun _ _ => rfl) hfS hc hX ho hr hcs hexp rfl rfl 3).2
    cs0_trapsDT_all src_noMemTrap .intDivz src_run_traps
  exact ⟨src_run_traps, H⟩

/-- **Non-vacuity of `Link.DeadCleanup.compileExe_correct_source_trapT_peak_nobnd`**: the same
run, with the peak variant: the outside caller provides `frameDrop + D * 1` bytes of stack, the
peak run premise holds at every fuel, and the executable machine's run from `r` reaches a state
at a trap with `int_divz`. -/
theorem exec_source_trapsT_peak {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (frameDrop (art spec.inputCleanup fF).af + (spec.inputCleanup.D * 1 + pbMax spec.inputCleanup))
      r [v41, v0] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [v41, v0] cs0) :
    Clif.runLoop closedBase.env spec.inputCleanup.srcProg 3 cs0 = .trapped .intDivz ∧
    ∃ k, TrapAtE spec.inputCleanup closedBase .intDivz
      (runX (step spec.inputCleanup closedBase file) k r) := by
  rw [← hlf] at ho hr
  have hfS : spec.inputCleanup.srcProg.func? "f" = some fF := by rw [srcP]; exact hfP0
  have hcs : ClifEntry fF [v41, v0] cs0 := clifEntry_initState (p := P0) rfl cs0_init
  have hs : sig128 fF.sig = false := rfl
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups fF.sig.params).getD []) [v41, v0] [v41, v0] := by
    obtain ⟨gs, hgs, hG⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_params hs)
    rw [hgs, Option.getD_some]
    exact Opt.Legal.expRel_refl_plain hG (Opt.Legal.sig128_params hs) rfl
  have hlegal : (∃ f ∈ spec.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk closedBase.env ∧ Opt.Legal.ExtLegal closedBase.env ∧
        Opt.Legal.EnvKeepsBounded closedBase.env := by
    rintro ⟨g, hg, hm⟩
    rw [srcP] at hg
    simp only [P0, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [fF_plain] at hm; cases hm
    · rw [fH_plain] at hm; cases hm
  have H := (compileExe_correct_source_trapT_peak_nobnd compile_eq hsrc closedBase baseOk
    (hooksSim_closed _) baseTrapsOk hlegal (fun _ _ => rfl) hfS 1 hX ho hr hcs hexp rfl rfl
    src_depthLe 3).2 peak_trapsDT_all src_noMemTrap .intDivz src_run_traps
  exact ⟨src_run_traps, H⟩

end Link.DeadCleanup.TrapTWitness

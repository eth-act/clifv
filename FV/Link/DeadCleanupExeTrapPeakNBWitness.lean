import FV.Link.DeadCleanupExeTrapNBWitness
import FV.Link.DeadCleanupExeTrapNB

/-!
# Witness: the peak callee-trap source theorem without the memory bound applies (A2/B1)

`DeadCleanupExeTrapWitness`'s executable (`f(x, y) = h(x, y)`, `h(x, y) = x / y`, compiled by
`compileExeU`): its source program is the compiled program `{f, h}` (no `i128`), and the peak
run premise holds: for every fuel `F` of `LinkSys.peak`, `(L.std.peak F).TrapsD 1 fF cs0` —
at peak fuel `0` the callee `h` runs out of fuel (so `f`'s step is stuck), at any other fuel
`h`'s run traps with `int_divz` (so `f`'s step is the same trap), and `h`'s activation satisfies
the premise at depth `0` in both cases. Also `src_depthLe`: the source run's call depth is at
most `1`.

* `exec_source_traps_peak`: `Link.DeadCleanup.compileExe_correct_source_trap_peak_nobnd` with
  every premise discharged but the entry contract (`Image.Intact`, `OutsideCall` with
  `frameDrop + D * 1` bytes of stack, `ClifRun` of `r`) — in particular without the source run's
  memory bound: the executable machine's run reaches a state at a trap with `int_divz`
  (`TrapAtE`).
-/

namespace Link.DeadCleanup.TrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver Opt.Legalize128

/-! ## The peak system's callee runs -/

theorem peakP (F : Nat) : (L.std.peak F).P = P0 := stdP

theorem LP : L.P = P0 := stdP

/-- A step fact transfers across equal programs. -/
theorem step_prog_congr {E : Clif.Env} {p q : Clif.Program} {o : Clif.StepResult}
    (hpq : p = q) (h : Clif.step E p cs0 = o) : Clif.step E q cs0 = o := by
  cases hpq; exact h

theorem peakPb (F : Nat) : (L.std.peak F).P.bare = P0.bare := by rw [peakP]

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

/-- The callee `h`'s entry makes no calls, so its run has call depth `0`. -/
theorem depthH0 : Clif.DepthLe L.base P0 0 csH := by
  intro u hu
  cases hu with
  | refl => exact Nat.le_refl _
  | next h1 _ => rw [csH_step] at h1; cases h1

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

/-- Under `LinkSys.peak F` for `0 < F`, `h`'s run from its entry on `(41, 0)` traps with
`int_divz` (one step of `runLoop`, `h` makes no calls). -/
theorem link_hD (F : Nat) (hF : 0 < F) :
    ∃ G, (Clif.linkEnvR L.P L.base (Clif.runD L.base L.P F 1)).extern "h" = some G ∧
      G [v41, v0] cs0.mem = .trapped .intDivz := by
  rw [LP, Clif.linkEnvR_some (show P0.func? "h" = some fH from rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [csH_init]
  dsimp only
  show Clif.runD L.base P0 F 1 csH = _
  rw [Clif.runD, if_pos ⟨by omega, depthH0⟩]
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  rw [Clif.runLoop_succ', csH_step]; rfl

/-- `h`'s activation satisfies the run premise at depth `0` under `LinkSys.peak F` for every
fuel `F`: its run traps at its division, an explicitly trapping instruction (the callee
environment is never consulted, whatever its fuel). -/
theorem peak_trapsD0 (F : Nat) : (L.std.peak F).TrapsD 0 fH csH := by
  rw [LinkSys.trapsD_eq]
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · rw [peakP] at hr; obtain rfl := csH_reach hr
    simp only [csH, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inl rfl
  · rw [peakP] at hr; obtain rfl := csH_reach hr; cases hb
  · rw [peakP] at hr; obtain rfl := csH_reach hr; cases hb
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

/-! ## The run premise of `f` at depth `1` under `LinkSys.peak F`, for every fuel `F` -/

/-- **The run premise under `LinkSys.peak 0`**: `f`'s callee runs out of fuel, so `f`'s step is
stuck and the run has no trap site. -/
theorem peak_trapsD1_0 : (L.std.peak 0).TrapsD 1 fF cs0 := by
  rw [LinkSys.trapsD_eq]
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
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := cs0_reach_stuck hEL s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inr (.inl ⟨0, [0, 1], rfl⟩)
  · obtain rfl := cs0_reach_stuck hEL s hr; cases hb
  · obtain rfl := cs0_reach_stuck hEL s hr; cases hb
  · obtain rfl := cs0_reach_stuck hEL s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · obtain rfl := cs0_reach_stuck hEL s hr; cases hb
  · cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ'] at hrun
      rw [hmE] at hrun
      cases hrun

/-- **The run premise under `LinkSys.peak F` for `0 < F`**: `f`'s trap is the call of `h`, whose
activation satisfies the premise at depth `0` (`peak_trapsD0`). -/
theorem peak_trapsD1_pos (F : Nat) (hF : 0 < F) : (L.std.peak F).TrapsD 1 fF cs0 := by
  rw [LinkSys.trapsD_eq]
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
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := cs0_reach_trap hEL s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inr (.inl ⟨0, [0, 1], rfl⟩)
  · obtain rfl := cs0_reach_trap hEL s hr; cases hb
  · obtain rfl := cs0_reach_trap hEL s hr; cases hb
  · obtain rfl := cs0_reach_trap hEL s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · obtain rfl := cs0_reach_trap hEL s hr; cases hb
  · have hQ : (L.std.peak F).covQ ((L.std.peak F).TrapsDn 1) "h" [v41, v0] cs0.mem := by
      intro h cs hpf hinit
      rw [peakP, show P0.func? "h" = some fH from rfl] at hpf
      cases hpf
      rw [peakP, csH_init] at hinit
      cases hinit
      exact peak_trapsD0 F
    have hEc : (cutEnv ((L.std.peak F).envR 1 fF)
        ((L.std.peak F).covQ ((L.std.peak F).TrapsDn 1))).extern "h" =
        some fun vals cm => cutO ((L.std.peak F).covQ ((L.std.peak F).TrapsDn 1)) "h" vals cm
          (G vals cm) := by
      simp only [cutEnv, hE, Option.map_some]
    have hGc : cutO ((L.std.peak F).covQ ((L.std.peak F).TrapsDn 1)) "h" [v41, v0] cs0.mem
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
theorem peak_trapsD_all (F : Nat) : (L.std.peak F).TrapsD 1 fF cs0 := by
  rcases Nat.eq_zero_or_pos F with rfl | hF
  · exact peak_trapsD1_0
  · exact peak_trapsD1_pos F hF

/-! ## The source run's depth -/

/-- **The source run of `f` on `(41, 0)` has call depth at most `1`**: the entry (`0` callers)
and `h`'s activation (`1`). -/
theorem src_depthLe : Clif.DepthLe closedBase.env spec.inputCleanup.srcProg 1 cs0 := by
  rw [srcP]
  intro u hu
  cases hu with
  | refl => exact Nat.zero_le _
  | next h1 h2 =>
    rw [cs0_src_step] at h1
    cases h1
    cases h2 with
    | refl => exact Nat.le_refl _
    | next h3 _ => rw [cs1_step] at h3; cases h3

/-! ## The peak source theorem applies -/

/-- **Non-vacuity of `Link.DeadCleanup.compileExe_correct_source_trap_peak_nobnd`**: the source
run of `f` on `(41, 0)` traps with `int_divz` inside the callee `h`, and for every machine state
`r` meeting the entry contract of an outside call of `f` with `frameDrop + D * 1` bytes of stack
(`Image.Intact`, `OutsideCall`, `ClifRun`), the run of the written executable `file` from `r`
reaches a state at a trap with `int_divz` (every other premise discharged, without a memory
bound of the source run). -/
theorem exec_source_traps_peak {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (frameDrop (art spec.inputCleanup fF).af + (spec.inputCleanup.D * 1 + pbMax spec.inputCleanup))
      r [v41, v0] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [v41, v0] cs0) :
    Clif.runLoop closedBase.env spec.inputCleanup.srcProg 3 cs0 = .trapped .intDivz ∧
    ∃ k, TrapAtE spec.inputCleanup closedBase .intDivz
      (runX (step spec.inputCleanup closedBase file) k r) := by
  rw [← hlf] at ho hr
  have hfS : spec.inputCleanup.srcProg.func? "f" = some fF := by rw [srcP]; rfl
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
  have H := (compileExe_correct_source_trap_peak_nobnd compile_eq hsrc closedBase baseOk
    (hooksSim_closed _) baseTrapsOk (fun g hg => (funcs_facts g hg).2) hlegal
    (fun _ _ => rfl) hfS 1 hX ho hr hcs hexp rfl rfl src_depthLe 3).2
    peak_trapsD_all src_noMemTrap .intDivz src_run_traps
  exact ⟨src_run_traps, H⟩

end Link.DeadCleanup.TrapWitness

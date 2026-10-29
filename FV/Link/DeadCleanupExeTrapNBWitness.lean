module

public import FV.Link.DeadCleanupExeTrapWitness
public import FV.Link.DeadCleanupExeTrapNB

@[expose] public section

/-!
# Witness: the source theorem with callee traps, without the memory bound, applies (A2/B1)

`DeadCleanupExeTrapWitness`'s executable (`f(x, y) = h(x, y)`, `h(x, y) = x / y`, compiled by
`compileExeU`): its source program is the compiled program `{f, h}` (no `i128`), and

* `src_run_traps`: the source run of `f` on `(41, 0)` traps with `int_divz` inside `h`;
* `src_noMemTrap`: it has no load/store trap (`NoMemTrap`);
* `cs0_trapsD_all`: the run premise `TrapsD` holds at every depth;
* `exec_source_traps`: `Link.DeadCleanup.compileExe_correct_source_trap_nobnd` with every premise
  discharged but the entry contract (`Image.Intact`, `OutsideCall`, `ClifRun` of `r`) — in
  particular without the source run's memory bound: the executable machine's run reaches a state
  at a trap with `int_divz` (`TrapAtE`).
-/

namespace Link.DeadCleanup.TrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver Opt.Legalize128

/-- **The receipt of the source program**: it is `{f, h}`, in the source domain (`SrcScopeB`),
`h` without `i128`. -/
def chkS : Bool :=
  decide (spec.inputCleanup.srcProg = P0) && SrcScopeB spec.inputCleanup && !mentions128 fH

set_option maxRecDepth 100000 in
theorem chkS_true : chkS = true := by native_decide

theorem srcP : spec.inputCleanup.srcProg = P0 := by
  have h := chkS_true
  simp only [chkS, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem hsrc : SrcScopeB spec.inputCleanup = true := by
  have h := chkS_true
  simp only [chkS, Bool.and_eq_true] at h
  exact h.1.2

theorem fH_plain : mentions128 fH = false := by
  have h := chkS_true
  simp only [chkS, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

theorem fF_plain : mentions128 fF = false := by decide

theorem hlf : legalize fF = fF := Opt.Legal.Complete.legalize_of_not_mentions fF_plain

/-! ## The source run -/

/-- `h`'s activation entered from `f`'s call (the source run's second state). -/
def cs1 : Clif.State :=
  ⟨⟨fH, regs0, [], [divStmt], .ret [2]⟩, [(⟨fF, regs0, [], [], .ret [2]⟩, [2])], {}⟩

theorem cs0_src_step (E : Clif.Env) : Clif.step E P0 cs0 = .next cs1 := rfl

theorem cs1_step (E : Clif.Env) (p : Clif.Program) : Clif.step E p cs1 = .trapped .intDivz :=
  Opt.step_eq_lift_of (r := .trap .intDivz) rfl (fun _ h => nomatch h)

/-- **The source run of `f` on `(41, 0)` traps with `int_divz`** (in `h`). -/
theorem src_run_traps :
    Clif.runLoop closedBase.env spec.inputCleanup.srcProg 3 cs0 = .trapped .intDivz := by
  rw [srcP, Clif.runLoop_succ', cs0_src_step]
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
      rw [cs0_src_step] at h1
      cases h1
      cases h2 with
      | refl => exact .inr rfl
      | step h3 _ => rw [cs1_step] at h3; cases h3
  rcases hs' with rfl | rfl
  · intro c st rest h
    rw [cs0_src_step] at h
    cases h
  · intro c st rest _ hb
    simp only [cs1, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact ⟨fun _ _ _ _ _ h => (nomatch h), fun _ _ _ _ _ _ h => (nomatch h)⟩

/-! ## The run premise at every depth -/

theorem link_h0 :
    ∃ G, (Clif.linkEnvR L.std.P L.std.base (L.std.crun 0)).extern "h" = some G ∧
      G [v41, v0] cs0.mem = .outOfFuel := by
  rw [stdP, Clif.linkEnvR_some (show P0.func? "h" = some fH from rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [csH_init]
  rfl

/-- `f`'s step is stuck when the callee runs out of fuel. -/
theorem cs0_step_oof (E : Clif.Env) {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hE : E.extern "h" = some G) (hG : G [v41, v0] cs0.mem = .outOfFuel) :
    ∃ m, Clif.step E P0.bare cs0 = .stuck m := by
  rw [Opt.step_eq_lift_of (r := .call extH [v41, v0] [2] []) rfl (fun _ h => nomatch h)]
  simp only [Opt.LRes.lift, Opt.callCont, extH, show P0.bare.func? "h" = none from rfl, hE, hG]
  exact ⟨_, rfl⟩

/-- **The run premise `TrapsD` holds at every depth** for `f`'s run on `(41, 0)`: at depth `0`
the callee runs out of fuel (no trap), at depth `K + 1` its trap is the call of `h`, whose
activation satisfies the premise (`cs0_trapsD` for every depth). -/
theorem cs0_trapsD_all (K : Nat) : L.std.TrapsD K fF cs0 := by
  rw [LinkSys.trapsD_eq]
  have hreach : ∀ s, Reach (Clif.linkEnvR L.std.P L.std.base (L.std.crun K)) L.std.P.bare cs0 s →
      s = cs0 := fun s hr => by
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
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := hreach s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inr (.inl ⟨0, [0, 1], rfl⟩)
  · obtain rfl := hreach s hr; cases hb
  · obtain rfl := hreach s hr; cases hb
  · obtain rfl := hreach s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · obtain rfl := hreach s hr; cases hb
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
      have hQ : L.std.covQ (L.std.TrapsDn (K + 1)) "h" [v41, v0] cs0.mem := by
        intro h cs hpf hinit
        rw [stdP, show P0.func? "h" = some fH from rfl] at hpf
        cases hpf
        rw [stdP, csH_init] at hinit
        cases hinit
        exact csH_trapsD K
      have hEc : (cutEnv (L.std.envR (K + 1) fF) (L.std.covQ (L.std.TrapsDn (K + 1)))).extern "h" =
          some fun vals cm => cutO (L.std.covQ (L.std.TrapsDn (K + 1))) "h" vals cm (G vals cm) := by
        simp only [cutEnv, hE, Option.map_some]
      have hGc : cutO (L.std.covQ (L.std.TrapsDn (K + 1))) "h" [v41, v0] cs0.mem
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

/-! ## The source theorem applies -/

/-- **Non-vacuity of `Link.DeadCleanup.compileExe_correct_source_trap_nobnd`**: the source run of
`f` on `(41, 0)` traps with `int_divz` inside the callee `h`, and for every machine state `r`
meeting the entry contract of an outside call of `f` (`Image.Intact`, `OutsideCall`, `ClifRun`),
the run of the written executable `file` from `r` reaches a state at a trap with `int_divz`
(every other premise discharged, without a memory bound of the source run). -/
theorem exec_source_traps {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [v41, v0] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [v41, v0] cs0) :
    Clif.runLoop closedBase.env spec.inputCleanup.srcProg 3 cs0 = .trapped .intDivz ∧
    ∃ k, TrapAtE spec.inputCleanup closedBase .intDivz
      (runX (step spec.inputCleanup closedBase file) k r) := by
  rw [← hlf] at ho hr
  have hfS : spec.inputCleanup.srcProg.func? "f" = some fF := by rw [srcP]; rfl
  have hc' : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls spec.inputCleanup spec.inputCleanup.resultsCleanup)
      (legalize fF) := by rw [hlf]; exact hc
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
  have H := (compileExe_correct_source_trap_nobnd compile_eq hsrc closedBase baseOk
    (hooksSim_closed _) baseTrapsOk (fun g hg => (funcs_facts g hg).2) hlegal
    (fun _ _ => rfl) hfS hc' hX ho hr hcs hexp rfl rfl 3).2
    (fun K => by rw [hlf]; exact cs0_trapsD_all K) src_noMemTrap .intDivz src_run_traps
  exact ⟨src_run_traps, H⟩

end Link.DeadCleanup.TrapWitness

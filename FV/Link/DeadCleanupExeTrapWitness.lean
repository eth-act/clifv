import FV.Link.ExeUnwindWitness
import FV.Link.DeadCleanupExeTrap

/-!
# Witness: the executable theorem with callee traps applies to a compiled executable (S9d)

`f(x, y) = h(x, y)` and `h(x, y) = x / y` (`udiv`), compiled by the shipped compiler with the
unwind tables checked (`compileExeU`, what `lake exe lean-link` decides: `compile_eq`,
`native_decide`) into a small static executable laid out as `ExeUnwindWitness`'s. With no code
outside the program (`closedBase`):

* `run_traps`: the whole-program run of `f` on `(41, 0)` traps with `int_divz` **inside the
  callee `h`** (its division by zero);
* `cs0_trapsD`: the new run premise `TrapsD` holds for it; `cs0_not_trapsExplicit`: the old
  premise `TrapsExplicit` (of `compileExe_correct`) does not — the run was excluded before;
* `exec_traps`: `Link.DeadCleanup.compileExe_correct_trap` with every premise discharged but the
  entry contract (`Image.Intact`, `OutsideCall`, `ClifRun` of the machine state `r`): the
  executable machine's run of the written `file` from `r` reaches a state at a trap with
  `int_divz` (`TrapAtE`).
-/

namespace Link.DeadCleanup.TrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

def srcH : String := "function %h(i64, i64) -> i64 system_v {
block0(v0: i64, v1: i64):
    v2 = udiv v0, v1
    return v2
}
"

def srcF : String := "function %f(i64, i64) -> i64 system_v {
    fn0 = colocated %h(i64, i64) -> i64 system_v
block0(v0: i64, v1: i64):
    v2 = call fn0(v0, v1)
    return v2
}
"

def fiF : FnInput := { clif := srcF, ra := "{}" }
def fiH : FnInput := { clif := srcH, ra := "{}" }

/-- `f` and `h` placed from 16 MiB with the sizes the cleanup pipeline compiles them to. -/
def spec : LinkSpec :=
  let fs := [fiF, fiH]
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

/-- The compiled functions (`compileExe`'s). -/
def arts : List Art := (tabOf (parResultsCleanupT spec.input0)).map (·.2)

/-- **The executable before the compiler** (as `ExeUnwindWitness.file0`). -/
def file0 : ByteArray :=
  UnwindWitness.exeWith spec.R spec.size
    [(UnwindWitness.hdrAddr, UnwindWitness.ehSegOf arts UnwindWitness.hdrAddr
        UnwindWitness.gccAddr 0x2200000),
      (UnwindWitness.gccAddr, (UnwindWitness.gccOf arts).1 ++ [0, 0, 0, 0])]
    (12 + 8 * arts.length) (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem compile_ok : (compileExeU spec file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (compileExeU spec file0)

/-- **The shipped compiler (unwind tables checked) compiles `{f, h}` to `file`.** -/
theorem compile_eq : compileExeU spec file0 = .ok file := getOk_eq compile_ok

/-! ## The program -/

/-- `(i64, i64) -> i64 system_v`. -/
def sig2 : Clif.Signature :=
  { params := [{ ty := .i64 }, { ty := .i64 }], returns := [{ ty := .i64 }],
    callConv := some .systemV }

/-- `v2 = udiv v0, v1`. -/
def divStmt : Clif.Stmt := { results := [2], inst := .div .udiv .i64 0 1 }

/-- The parsed `h`. -/
def fH : Clif.Function :=
  { name := "h", sig := sig2,
    blocks := [{ id := 0, params := [(0, .i64), (1, .i64)], body := [divStmt], term := .ret [2] }] }

/-- `v2 = call fn0(v0, v1)`. -/
def callStmt : Clif.Stmt := { results := [2], inst := .call 0 [0, 1] }

def extH : Clif.ExtFunc := { name := "h", sig := sig2, colocated := true }

/-- The parsed `f`. -/
def fF : Clif.Function :=
  { name := "f", sig := sig2, externs := [(0, extH)],
    blocks := [{ id := 0, params := [(0, .i64), (1, .i64)], body := [callStmt], term := .ret [2] }] }

def P0 : Clif.Program := { funcs := [fF, fH] }

/-- **The receipt**: the compiled program is `{f, h}`, no TLS, no `try_call`, and `f` reaches no
call cycle (`goodN`). -/
def chk : Bool :=
  decide (prog spec.inputCleanup = P0) && [fF, fH].all (fun g => !hasTls g &&
    g.blocks.all fun B => !B.term.isTry) && DeadCleanupStackBound.goodN spec.inputCleanup "f"

set_option maxRecDepth 100000 in
theorem chk_true : chk = true := by native_decide

theorem P_eq : prog spec.inputCleanup = P0 := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem funcs_facts : ∀ g ∈ (prog spec.inputCleanup).funcs, hasTls g = false ∧
    ∀ B ∈ g.blocks, B.term.isTry = false := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  intro g hg
  rw [P_eq] at hg
  exact ⟨(h.1.2 g hg).1, (h.1.2 g hg).2⟩

theorem hf : (prog spec.inputCleanup).func? "f" = some fF := by rw [P_eq]; rfl

theorem hc : ¬ DeadCleanupStackBound.CycleFrom
    (DeadCleanupStackBound.Calls spec.inputCleanup spec.inputCleanup.resultsCleanup) fF := by
  obtain ⟨he, -⟩ := compileExeU_spec compile_eq
  obtain ⟨hin, hl⟩ := compileExe_spec he
  have hg : DeadCleanupStackBound.goodN spec.inputCleanup "f" = true := by
    have h := chk_true
    simp only [chk, Bool.and_eq_true] at h
    exact h.2
  obtain ⟨f', hf', hcyc⟩ := (DeadCleanupStackBound.goodN_iff (okB_leanLink hin hl)).1 hg
  have : (prog spec.inputCleanup).func? "f" = some f' := hf'
  rw [hf] at this
  cases this
  exact hcyc

/-! ## The base environment: no code outside the program -/

abbrev L : LinkSys := sys spec.inputCleanup closedBase

theorem baseOk : BaseOk L := baseOk_closedR fun g hg => (funcs_facts g hg).1

/-- **The outside code's trap contract** (no extern outside the program; `closedBase`'s hooks
keep an error state). -/
theorem baseTrapsOk : L.BaseTrapsOk where
  xt _ _ _ _ _ _ := ⟨fun _ _ _ _ _ _ _ _ _ _ _ hg => (nomatch hg),
    fun _ _ _ _ _ _ _ _ _ _ _ hg => (nomatch hg)⟩
  stop _ _ _ _ _ h := by
    obtain ⟨-, -, -, _, _, _, _, _, _, _, -, -, -, -, -, -, ⟨_, _, _, _, _, _, _, hg, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, hg, -⟩⟩ := h
    · exact nomatch hg
    · exact nomatch hg
  err _ s h := by
    show Arm.r .ERR (Arm.w .PC (Arm.r .PC s + 4) s) ≠ .None
    rw [Arm.r_of_w_different (by simp)]; exact h
  tlsErr _ _ _ h := h

/-! ## A run trapping inside the callee: `f(41, 0)` divides by zero in `h` -/

def v41 : Clif.Val := ⟨.i64, 41⟩
def v0 : Clif.Val := ⟨.i64, 0⟩

def regs0 : Clif.Regs := Clif.Regs.set (Clif.Regs.set Clif.Regs.empty 0 v41) 1 v0

/-- `f`'s entry state on `(41, 0)` (empty memory). -/
def cs0 : Clif.State := ⟨⟨fF, regs0, [], [callStmt], .ret [2]⟩, [], {}⟩

theorem cs0_init : Clif.initState P0 "f" [v41, v0] {} = .ok cs0 := rfl

/-- `h`'s entry state for `f`'s call. -/
def csH : Clif.State := ⟨⟨fH, regs0, [], [divStmt], .ret [2]⟩, [], {}⟩

theorem csH_init : Clif.initState P0 "h" [v41, v0] cs0.mem = .ok csH := rfl

/-- `h`'s step divides by zero under every environment. -/
theorem csH_step (E : Clif.Env) (p : Clif.Program) : Clif.step E p csH = .trapped .intDivz :=
  Opt.step_eq_lift_of (r := .trap .intDivz) rfl (fun _ h => nomatch h)

/-- `f`'s step is the call of `h`: it traps when that extern traps. -/
theorem cs0_step (E : Clif.Env) {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hE : E.extern "h" = some G) (hG : G [v41, v0] cs0.mem = .trapped .intDivz) :
    Clif.step E P0.bare cs0 = .trapped .intDivz := by
  rw [Opt.step_eq_lift_of (r := .call extH [v41, v0] [2] []) rfl (fun _ h => nomatch h)]
  simp only [Opt.LRes.lift, Opt.callCont, extH, show P0.bare.func? "h" = none from rfl, hE, hG]

theorem csH_reach {E : Clif.Env} {s : Clif.State} (h : Reach E P0.bare csH s) : s = csH := by
  cases h with
  | refl => rfl
  | step h1 _ => rw [csH_step] at h1; cases h1

/-- **The whole-program run of `f` on `(41, 0)` traps with `int_divz`** (in `h`). -/
theorem run_traps : Clif.runLoop closedBase.env (prog spec.inputCleanup) (9 + 1) cs0 =
    .trapped .intDivz := by
  rw [P_eq]; rfl

theorem stdP : L.std.P = P0 := P_eq

theorem link_h (M : Nat) (hM : 0 < M) :
    ∃ G, (Clif.linkEnvR L.std.P L.std.base (L.std.crun M)).extern "h" = some G ∧
      G [v41, v0] cs0.mem = .trapped .intDivz := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [stdP, Clif.linkEnvR_some (show P0.func? "h" = some fH from rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [csH_init]
  dsimp only
  show Clif.runLoop L.base L.P (M' + 1) csH = _
  rw [Clif.runLoop_succ', csH_step]; rfl

/-- The callee's activation satisfies the run premise at every depth: its run traps at its
division, an explicitly trapping instruction. -/
theorem csH_trapsD (M : Nat) : L.std.TrapsD M fH csH := by
  rw [LinkSys.trapsD_eq]
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · rw [stdP] at hr; obtain rfl := csH_reach hr
    simp only [csH, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inl rfl
  · rw [stdP] at hr; obtain rfl := csH_reach hr; cases hb
  · rw [stdP] at hr; obtain rfl := csH_reach hr; cases hb
  · rw [stdP] at hr; obtain rfl := csH_reach hr
    simp only [csH, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · rw [stdP] at hr; obtain rfl := csH_reach hr; cases hb
  · cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ', csH_step] at hrun ⊢
      exact hrun

theorem mayCall_h : L.std.MayCall fF "h" := .inl (by simp [DeclN, fF, extH])

/-- **The run premise `TrapsD` holds** for `f`'s run on `(41, 0)` (callee runs of at most `9`
steps): its trap is the call of `h`, whose activation satisfies the premise. -/
theorem cs0_trapsD : L.std.TrapsD 9 fF cs0 := by
  rw [LinkSys.trapsD_eq]
  obtain ⟨G, hG, hGt⟩ := link_h 9 (by omega)
  have hstep : Clif.step (Clif.linkEnvR L.std.P L.std.base (L.std.crun 9)) L.std.P.bare cs0 =
      .trapped .intDivz := by
    have := cs0_step _ hG hGt
    rw [stdP]
    rw [stdP] at this
    exact this
  have hreach : ∀ s, Reach (Clif.linkEnvR L.std.P L.std.base (L.std.crun 9)) L.std.P.bare cs0 s →
      s = cs0 := fun s hr => by
    cases hr with
    | refl => rfl
    | step h1 _ => rw [hstep] at h1; cases h1
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
  · have hE : (L.std.envR 9 fF).extern "h" = some G := by
      rw [L.std.envR_of (.inr mayCall_h)]; exact hG
    have hstepR : Clif.step (L.std.envR 9 fF) L.std.P.bare cs0 = .trapped .intDivz := by
      rw [stdP]; exact cs0_step _ hE hGt
    have hQ : L.std.covQ (L.std.TrapsDn 9) "h" [v41, v0] cs0.mem := by
      intro h cs hpf hinit
      rw [stdP, show P0.func? "h" = some fH from rfl] at hpf
      cases hpf
      rw [stdP, csH_init] at hinit
      cases hinit
      exact csH_trapsD 8
    have hEc : (cutEnv (L.std.envR 9 fF) (L.std.covQ (L.std.TrapsDn 9))).extern "h" =
        some fun vals cm => cutO (L.std.covQ (L.std.TrapsDn 9)) "h" vals cm (G vals cm) := by
      simp only [cutEnv, hE, Option.map_some]
    have hGc : cutO (L.std.covQ (L.std.TrapsDn 9)) "h" [v41, v0] cs0.mem (G [v41, v0] cs0.mem) =
        .trapped .intDivz := by
      unfold cutO
      rw [if_neg (fun h => h.2 hQ)]
      exact hGt
    cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ', hstepR] at hrun
      rw [Clif.runLoop_succ', stdP, cs0_step _ hEc hGc]
      exact hrun

/-- **`TrapsExplicit` does not hold** for `f`'s run on `(41, 0)`: the premise of
`compileExe_correct` excludes this run (its trapping statement is a call). -/
theorem cs0_not_trapsExplicit :
    ¬ TrapsExplicit (Clif.linkEnvN (prog spec.inputCleanup) closedBase.env 9)
      (prog spec.inputCleanup).bare cs0 := by
  intro h
  obtain ⟨G, hG, hGt⟩ := link_h 9 (by omega)
  have hstep : Clif.step (Clif.linkEnvN (prog spec.inputCleanup) closedBase.env 9)
      (prog spec.inputCleanup).bare cs0 = .trapped .intDivz := by
    have := cs0_step _ hG hGt
    rw [P_eq]
    rw [stdP] at this
    exact this
  have := h.stmt cs0 _ callStmt [] (.refl _) hstep rfl
  simp [callStmt, explicitTrapInst] at this

/-! ## The executable theorem applies -/

/-- **The executable reaches the division-by-zero trap**: for every machine state `r` meeting
the entry contract of an outside call of `f` on `(41, 0)` (`Image.Intact`, `OutsideCall`,
`ClifRun`), the run of the written executable `file` from `r` reaches a state at a trap with
`int_divz` (`Link.DeadCleanup.compileExe_correct_trap`, every other premise discharged). -/
theorem exec_traps {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [v41, v0] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [v41, v0] cs0) :
    ∃ k, TrapAtE spec.inputCleanup closedBase .intDivz
      (runX (step spec.inputCleanup closedBase file) k r) := by
  have := compileExe_correct_trap compile_eq closedBase baseOk (hooksSim_closed _) baseTrapsOk
    (fun g hg => (funcs_facts g hg).2) hf hc 9 hX ho hr cs0_trapsD
  rw [run_traps] at this
  exact this

end Link.DeadCleanup.TrapWitness

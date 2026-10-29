module

public import FV.Link.DeadCleanupExeTrapWitness
public import FV.Link.DeadCleanupExeTrapT

@[expose] public section

/-!
# Witness: the executable theorem with `try_call` callee traps applies to a compiled executable (S9e)

`f(x, y)` does `try_call h(x, y)` (a `tag0` handler) and `h(x, y) = x / y` (`udiv`), compiled by
the shipped compiler with the unwind tables checked (`compileExeU`, what `lake exe lean-link`
decides: `compile_eq`, `native_decide`) into a small static executable laid out as
`DeadCleanupExeTrapWitness`'s. With no code outside the program (`closedBase`):

* `run_traps`: the whole-program run of `f` on `(41, 0)` traps with `int_divz` **inside the
  callee `h` of the `try_call`**;
* `cs0_trapsDT`: the new run premise `TrapsDT` holds for it; `cs0_not_trapsD`: S9d's premise
  `TrapsD` does not, and `not_noTry`: S9d's premise "no `try_call` terminator" fails — the run
  and the executable were excluded before;
* `exec_traps`: `Link.DeadCleanup.compileExe_correct_trapT` with every premise discharged but
  the entry contract (`Image.Intact`, `OutsideCall`, `ClifRun` of the machine state `r`): the
  executable machine's run of the written `file` from `r` reaches a state at a trap with
  `int_divz` (`TrapAtE`).
-/

namespace Link.DeadCleanup.TrapTWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver
open Link.DeadCleanup.TrapWitness (srcH fiH sig2 divStmt fH extH v41 v0 regs0 csH csH_step
  csH_reach)

def srcF : String := "function %f(i64, i64) -> i64 system_v {
    sig0 = (i64, i64) -> i64 system_v
    fn0 = colocated %h(i64, i64) -> i64 system_v
block0(v0: i64, v1: i64):
    try_call fn0(v0, v1), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v2: i64):
    return v2
block2(v3: i64):
    return v3
}
"

def fiF : FnInput := { clif := srcF, ra := "{}" }

/-- `f` and `h` placed from 16 MiB with the sizes the cleanup pipeline compiles them to. -/
def spec : LinkSpec :=
  let fs := [fiF, fiH]
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

/-- The compiled functions (`compileExe`'s). -/
def arts : List Art := (tabOf (parResultsCleanupT spec.input0)).map (·.2)

/-- **The executable before the compiler** (as `DeadCleanupExeTrapWitness.file0`; `f` has a
landing pad, so `.gcc_except_table` holds its LSDA). -/
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

/-- The exception table: `sig0, block1(ret0), [ tag0: block2(exn0) ]`. -/
def et : Clif.ExnTable :=
  { sig := 0, normal := { block := 1, args := [.ret 0] },
    items := [.tag 0 { block := 2, args := [.exn 0] }] }

/-- The parsed `f`. -/
def fF : Clif.Function :=
  { name := "f", sig := sig2, externs := [(0, extH)], sigDecls := [(0, sig2)],
    blocks := [
      { id := 0, params := [(0, .i64), (1, .i64)], term := .tryCall 0 [0, 1] et },
      { id := 1, params := [(2, .i64)], term := .ret [2] },
      { id := 2, params := [(3, .i64)], term := .ret [3] }] }

def P0 : Clif.Program := { funcs := [fF, fH] }

/-- **The receipt**: the compiled program is `{f, h}`, no TLS, and `f` reaches no call cycle
(`goodN`). -/
def chk : Bool :=
  decide (prog spec.inputCleanup = P0) && [fF, fH].all (fun g => !hasTls g) &&
    DeadCleanupStackBound.goodN spec.inputCleanup "f"

set_option maxRecDepth 100000 in
theorem chk_true : chk = true := by native_decide

theorem P_eq : prog spec.inputCleanup = P0 := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem funcs_tls : ∀ g ∈ (prog spec.inputCleanup).funcs, hasTls g = false := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  intro g hg
  rw [P_eq] at hg
  exact h.1.2 g hg

/-- **S9d's premise "no `try_call` terminator" fails** for this program. -/
theorem not_noTry : ¬ ∀ g ∈ (prog spec.inputCleanup).funcs, ∀ B ∈ g.blocks, B.term.isTry = false := by
  intro h
  rw [P_eq] at h
  have := h fF (List.mem_cons_self ..) _ (List.mem_cons_self ..)
  simp [fF, Clif.Terminator.isTry] at this

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

theorem baseOk : BaseOk L := baseOk_closedR funcs_tls

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

/-! ## A run trapping inside the `try_call`'s callee: `f(41, 0)` divides by zero in `h` -/

/-- `f`'s entry state on `(41, 0)` (empty memory). -/
def cs0 : Clif.State := ⟨⟨fF, regs0, [], [], .tryCall 0 [0, 1] et⟩, [], {}⟩

theorem cs0_init : Clif.initState P0 "f" [v41, v0] {} = .ok cs0 := rfl

theorem csH_init : Clif.initState P0 "h" [v41, v0] cs0.mem = .ok csH := rfl

/-- The normal-return edge of the `try_call` (`tryNormal`). -/
def bc0 : Clif.BlockCall := { block := 1, args := [4] }

/-- `f`'s step is the `try_call` of `h`: it traps when that extern traps. -/
theorem cs0_step (E : Clif.Env) {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hE : E.extern "h" = some G) (hG : G [v41, v0] cs0.mem = .trapped .intDivz) :
    Clif.step E P0.bare cs0 = .trapped .intDivz := by
  rw [Clif.step_try E P0.bare cs0 rfl rfl]
  show Opt.callCont E P0.bare (Clif.tryState cs0 bc0) [] [4] extH [v41, v0] = _
  simp only [Opt.callCont, extH, show P0.bare.func? "h" = none from rfl, hE]
  exact hG ▸ rfl

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
theorem csH_trapsDT (M : Nat) : L.std.TrapsDT M fH csH := by
  rw [LinkSys.trapsDT_eq]
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · rw [stdP] at hr; obtain rfl := csH_reach hr
    simp only [csH, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inl rfl
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

theorem cs0_stepL : Clif.step (Clif.linkEnvR L.std.P L.std.base (L.std.crun 9)) L.std.P.bare cs0 =
    .trapped .intDivz := by
  obtain ⟨G, hG, hGt⟩ := link_h 9 (by omega)
  have := cs0_step _ hG hGt
  rw [stdP]
  rw [stdP] at this
  exact this

theorem cs0_reachL (s : Clif.State)
    (hr : Reach (Clif.linkEnvR L.std.P L.std.base (L.std.crun 9)) L.std.P.bare cs0 s) : s = cs0 := by
  cases hr with
  | refl => rfl
  | step h1 _ => rw [cs0_stepL] at h1; cases h1

/-- **The run premise `TrapsDT` holds** for `f`'s run on `(41, 0)` (callee runs of at most `9`
steps): its trap is the `try_call` of `h`, whose activation satisfies the premise. -/
theorem cs0_trapsDT : L.std.TrapsDT 9 fF cs0 := by
  rw [LinkSys.trapsDT_eq]
  obtain ⟨G, hG, hGt⟩ := link_h 9 (by omega)
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s st rest _ _ _ hr hb _ => ?_,
    fun s _ _ _ hr _ ht => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := cs0_reachL s hr; cases hb
  · obtain rfl := cs0_reachL s hr; cases hb
  · obtain rfl := cs0_reachL s hr; cases ht
  · have hE : (L.std.envR 9 fF).extern "h" = some G := by
      rw [L.std.envR_of (.inr mayCall_h)]; exact hG
    have hstepR : Clif.step (L.std.envR 9 fF) L.std.P.bare cs0 = .trapped .intDivz := by
      rw [stdP]; exact cs0_step _ hE hGt
    have hQ : L.std.covQ (L.std.TrapsDTn 9) "h" [v41, v0] cs0.mem := by
      intro h cs hpf hinit
      rw [stdP, show P0.func? "h" = some fH from rfl] at hpf
      cases hpf
      rw [stdP, csH_init] at hinit
      cases hinit
      exact csH_trapsDT 8
    have hEc : (cutEnv (L.std.envR 9 fF) (L.std.covQ (L.std.TrapsDTn 9))).extern "h" =
        some fun vals cm => cutO (L.std.covQ (L.std.TrapsDTn 9)) "h" vals cm (G vals cm) := by
      simp only [cutEnv, hE, Option.map_some]
    have hGc : cutO (L.std.covQ (L.std.TrapsDTn 9)) "h" [v41, v0] cs0.mem (G [v41, v0] cs0.mem) =
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

/-- **S9d's run premise `TrapsD` does not hold** for `f`'s run on `(41, 0)`: its `try_call`
clause excludes a trapping `try_call` of the entered function. -/
theorem cs0_not_trapsD : ¬ L.std.TrapsD 9 fF cs0 := by
  intro h
  rw [LinkSys.trapsD_eq] at h
  exact h.1.tryCall cs0 _ 0 [0, 1] et (.refl _) cs0_stepL rfl rfl _ (List.mem_cons_self ..) rfl

/-! ## The executable theorem applies -/

/-- **The executable reaches the division-by-zero trap in the `try_call`'s callee**: for every
machine state `r` meeting the entry contract of an outside call of `f` on `(41, 0)`
(`Image.Intact`, `OutsideCall`, `ClifRun`), the run of the written executable `file` from `r`
reaches a state at a trap with `int_divz` (`Link.DeadCleanup.compileExe_correct_trapT`, every
other premise discharged). -/
theorem exec_traps {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [v41, v0] cs0.mem)
    (hr : ClifRun spec.inputCleanup closedBase fF r [v41, v0] cs0) :
    ∃ k, TrapAtE spec.inputCleanup closedBase .intDivz
      (runX (step spec.inputCleanup closedBase file) k r) := by
  have := compileExe_correct_trapT compile_eq closedBase baseOk (hooksSim_closed _) baseTrapsOk
    hf hc 9 hX ho hr cs0_trapsDT
  rw [run_traps] at this
  exact this

end Link.DeadCleanup.TrapTWitness

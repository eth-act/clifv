import FV.E2E.LinkTrapCallInd
import FV.E2E.DeadCleanupLinkCheck

/-!
# Non-vacuity of the linked-program theorem with callee traps (S9c, #376)

A concrete linked program for which every premise of `E2E.backend_correct_program_trap_budget`
but the entry state's holds, and whose whole-program run traps **inside a program callee**:
`P = {f, h}` (parsed from `srcF`, `srcH`, compiled by the shipped dead-cleanup pipeline with its
spill fallback, loaded at `0x10000`, `0x20000`, no extern outside `P`: `closedBase`), where `f`
calls the program function `h` and `h` is `trap user1`.

* `L_ok`, `trapsOk`, `baseTrapsOk`: `LinkSys.Ok` (the checker `okBCleanup`), the per-function
  facts (`CompiledCleanup`, the lowering's unwinding validator, no `try_call`) and the outside
  code's trap contract (vacuous but for the hooks keeping an error state: `closedBase`).
* `run_traps`: the whole-program run from `f` on `41` traps with `user1` (in `h`).
* `cs0_trapsD`: the run premise `TrapsD` holds for it (`f`'s trap is a call whose callee's
  activation traps explicitly); `cs0_not_trapsExplicit`: the old program theorem's premise
  `TrapsExplicit` does not (the trapping statement of `f` is a call): **the run is covered by the
  new theorem and was excluded by `backend_correct_program_budget`**.
* `program_trap_applies`: the theorem specialised to this system (left open: the entry state's
  premises, as in `LinkArmUProgWitness.budgetU_applies`).
-/

namespace E2E.LinkTrapCallWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.LinkCheck

def srcH : String := "function %h(i64) -> i64 system_v {
block0(v0: i64):
    trap user1
}
"

def srcF : String := "function %f(i64) -> i64 system_v {
    fn0 = colocated %h(i64) -> i64 system_v
block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
"

def fiF : FnInput := { clif := srcF, ra := "{}" }
def fiH : FnInput := { clif := srcH, ra := "{}" }

/-- The input: `f` and `h`, compiled by the shipped pipeline. -/
def I : LinkInput where
  funcs := [fiF, fiH]
  addrs := [("f", 0x10000), ("h", 0x20000)]
  syms := []
  raStar := 0x40000
  D := 4096
  fallback := true

/-- `(i64) -> i64 system_v`. -/
def sigI : Clif.Signature :=
  { params := [{ ty := .i64 }], returns := [{ ty := .i64 }], callConv := some .systemV }

/-- The parsed `h`. -/
def fH : Clif.Function :=
  { name := "h", sig := sigI,
    blocks := [{ id := 0, params := [(0, .i64)], body := [], term := .trap (.user 1) }] }

/-- The call statement `v1 = call fn0(v0)`. -/
def callStmt : Clif.Stmt := { results := [1], inst := .call 0 [0] }

/-- The declaration of `h` in `f`. -/
def extH : Clif.ExtFunc := { name := "h", sig := sigI, colocated := true }

/-- The block of `f`. -/
def blockF : Clif.Block := { id := 0, params := [(0, .i64)], body := [callStmt], term := .ret [1] }

/-- The parsed `f`. -/
def fF : Clif.Function :=
  { name := "f", sig := sigI, externs := [(0, extH)], blocks := [blockF] }

/-- The linked system (no extern outside the program). -/
def L0 (F : BitVec 64 → Prop) : LinkSys := LinkSys.ofInputCleanup I closedBase F

/-- **The closed receipt**: the link checker, the parsed functions, and the per-function facts
of the trap theorem (no TLS, the lowering's unwinding validator, no `try_call` terminator). -/
def chk : Bool :=
  okBCleanup I && decide (fiF.func = fF) && decide (fiH.func = fH) &&
  [fF, fH].all fun g =>
    !hasTls g && lowerCheckU g (artOf I.resultsCleanup g).vc && g.blocks.all fun B => !B.term.isTry

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem chk_true : chk = true := by native_decide

theorem facts : okBCleanup I = true ∧ fiF.func = fF ∧ fiH.func = fH ∧
    ∀ g ∈ [fF, fH], hasTls g = false ∧ lowerCheckU g (artOf I.resultsCleanup g).vc = true ∧
      ∀ B ∈ g.blocks, B.term.isTry = false := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun g hg => ⟨(h4 g hg).1.1, (h4 g hg).1.2, fun B hB => (h4 g hg).2 B hB⟩⟩

/-- The program `{f, h}`. -/
def P0 : Clif.Program := { funcs := [fF, fH] }

theorem P_eq (F : BitVec 64 → Prop) : (L0 F).P = P0 := by
  show progOf I.resultsCleanup = P0
  simp only [progOf, P0, LinkInput.resultsCleanup, I, List.map_cons, List.map_nil, facts.2.1,
    facts.2.2.1]

theorem funcs_eq (F : BitVec 64 → Prop) : (L0 F).P.funcs = [fF, fH] := by rw [P_eq]; rfl

/-- **`LinkSys.Ok` holds** for every `F` containing the code. -/
theorem L_ok (F : BitVec 64 → Prop) (hF : ∀ a, (L0 F).Img a → F a) : (L0 F).Ok :=
  okBCleanup_sound facts.1 (baseOk_closedR fun g hg => by
    have hg' : g ∈ (L0 F).P.funcs := hg
    rw [funcs_eq] at hg'
    exact (facts.2.2.2 g hg').1) hF

/-- **The per-function facts of the trap theorem** (the shipped pipeline). -/
theorem trapsOk (F : BitVec 64 → Prop) : (L0 F).TrapsOk where
  cleanup g hg := by
    have hf := factsCleanup facts.1 hg
    exact ⟨hf.pipe.1, hf.lowerOk, hf.pipe.2.1, hf.prepOk, hf.check, hf.pipe.2.2.1,
      hf.pipe.2.2.2.1, hf.pipe.2.2.2.2.1⟩
  lowerU g hg := by
    have hg' := hg
    rw [funcs_eq] at hg'
    exact (facts.2.2.2 g hg').2.1
  noTry g hg := by
    rw [funcs_eq] at hg
    exact (facts.2.2.2 g hg).2.2

/-- **The outside code's trap contract** (no extern outside the program; `closedBase`'s hooks
keep an error state). -/
theorem baseTrapsOk (F : BitVec 64 → Prop) : (L0 F).BaseTrapsOk where
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

/-! ## A run trapping inside the program callee -/

def v41 : Clif.Val := ⟨.i64, 41⟩

/-- The entry registers on `41`. -/
def regs0 : Clif.Regs := Clif.Regs.set Clif.Regs.empty 0 v41

/-- `f`'s entry state on `41` (empty memory). -/
def cs0 : Clif.State := ⟨⟨fF, regs0, [], [callStmt], .ret [1]⟩, [], {}⟩

theorem cs0_init : Clif.initState P0 "f" [v41] {} = .ok cs0 := rfl

theorem cs0_entry : ClifEntry fF [v41] cs0 := clifEntry_initState (f := fF) rfl cs0_init

/-- `h`'s entry state for `f`'s call. -/
def csH : Clif.State := ⟨⟨fH, regs0, [], [], .trap (.user 1)⟩, [], {}⟩

theorem csH_init : Clif.initState P0 "h" [v41] cs0.mem = .ok csH := rfl

/-- `h`'s step traps with `user1` under every environment. -/
theorem csH_step (E : Clif.Env) (p : Clif.Program) : Clif.step E p csH = .trapped (.user 1) :=
  Opt.step_eq_lift_of (r := .trap (.user 1)) rfl (fun _ h => nomatch h)

/-- `f`'s step is the call of `h` on `41`: it traps when that extern traps. -/
theorem cs0_step (E : Clif.Env) {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hE : E.extern "h" = some G) (hG : G [v41] cs0.mem = .trapped (.user 1)) :
    Clif.step E P0.bare cs0 = .trapped (.user 1) := by
  rw [Opt.step_eq_lift_of (r := .call extH [v41] [1] [])
    rfl (fun _ h => nomatch h)]
  simp only [Opt.LRes.lift, Opt.callCont, extH, show P0.bare.func? "h" = none from rfl, hE, hG]

theorem cs0_reach {E : Clif.Env} {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hE : E.extern "h" = some G) (hG : G [v41] cs0.mem = .trapped (.user 1)) {s : Clif.State}
    (h : Reach E P0.bare cs0 s) : s = cs0 := by
  cases h with
  | refl => rfl
  | step h1 _ => rw [cs0_step E hE hG] at h1; cases h1

theorem csH_reach {E : Clif.Env} {s : Clif.State} (h : Reach E P0.bare csH s) : s = csH := by
  cases h with
  | refl => rfl
  | step h1 _ => rw [csH_step] at h1; cases h1

/-- **The whole-program run from `f` on `41` traps with `user1`** (inside `h`). -/
theorem run_traps (F : BitVec 64 → Prop) :
    Clif.runLoop (L0 F).base (L0 F).P 10 cs0 = .trapped (.user 1) := by
  rw [P_eq]; rfl

theorem stdP (F : BitVec 64 → Prop) : (L0 F).std.P = P0 := P_eq F

/-- The linked environment's extern `h` (callee runs of at most `M` steps) traps on `f`'s call. -/
theorem link_h (M : Nat) (hM : 0 < M) (F : BitVec 64 → Prop) :
    ∃ G, (Clif.linkEnvR (L0 F).std.P (L0 F).std.base ((L0 F).std.crun M)).extern "h" = some G ∧
      G [v41] cs0.mem = .trapped (.user 1) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [stdP, Clif.linkEnvR_some (show P0.func? "h" = some fH from rfl)]
  refine ⟨_, rfl, ?_⟩
  rw [csH_init]
  dsimp only
  show Clif.runLoop (L0 F).base (L0 F).P (M' + 1) csH = _
  rw [Clif.runLoop_succ', csH_step]; rfl

/-- The callee's activation satisfies the run premise at every depth (its run traps explicitly at
its first step). -/
theorem csH_trapsD (F : BitVec 64 → Prop) (M : Nat) : (L0 F).std.TrapsD M fH csH := by
  rw [LinkSys.trapsD_eq]
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb _ => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · rw [stdP] at hr; obtain rfl := csH_reach hr; cases hb
  · rw [stdP] at hr; obtain rfl := csH_reach hr; intro ht; cases ht
  · rw [stdP] at hr; obtain rfl := csH_reach hr; intro ht; cases ht
  · rw [stdP] at hr; obtain rfl := csH_reach hr; cases hb
  · rw [stdP] at hr; obtain rfl := csH_reach hr; intro ht; cases ht
  · cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ', csH_step] at hrun ⊢
      exact hrun

theorem mayCall_h (F : BitVec 64 → Prop) : (L0 F).std.MayCall fF "h" :=
  .inl (by simp [DeclN, fF, extH])

/-- **The run premise `TrapsD` holds** for `f`'s run on `41` (at depth `9`: callee runs of at most
`9` steps): its trap is the call of `h`, whose activation satisfies the premise. -/
theorem cs0_trapsD (F : BitVec 64 → Prop) : (L0 F).std.TrapsD 9 fF cs0 := by
  rw [LinkSys.trapsD_eq]
  obtain ⟨G, hG, hGt⟩ := link_h 9 (by omega) F
  have hstep : Clif.step (Clif.linkEnvR (L0 F).std.P (L0 F).std.base ((L0 F).std.crun 9))
      (L0 F).std.P.bare cs0 = .trapped (.user 1) := by
    have := cs0_step _ hG hGt
    rw [stdP]
    rw [stdP] at this
    exact this
  have hreach : ∀ s, Reach (Clif.linkEnvR (L0 F).std.P (L0 F).std.base ((L0 F).std.crun 9))
      (L0 F).std.P.bare cs0 s → s = cs0 := fun s hr => by
    cases hr with
    | refl => rfl
    | step h1 _ => rw [hstep] at h1; cases h1
  refine ⟨⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s _ _ _ _ hr _ hb => ?_, fun s st rest _ _ _ hr hb hi => ?_,
    fun s _ _ _ hr hb => ?_⟩, fun fuel tc hrun => ?_⟩
  · obtain rfl := hreach s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inr (.inl ⟨0, [0], rfl⟩)
  · obtain rfl := hreach s hr; cases hb
  · obtain rfl := hreach s hr; cases hb
  · obtain rfl := hreach s hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · obtain rfl := hreach s hr; cases hb
  · -- the run of `f`'s activation: the call of `h` traps, under `envR` and with the cut
    have hE : ((L0 F).std.envR 9 fF).extern "h" = some G := by
      rw [(L0 F).std.envR_of (.inr (mayCall_h F))]; exact hG
    have hstepR : Clif.step ((L0 F).std.envR 9 fF) (L0 F).std.P.bare cs0 = .trapped (.user 1) := by
      rw [stdP]; exact cs0_step _ hE hGt
    have hQ : (L0 F).std.covQ ((L0 F).std.TrapsDn 9) "h" [v41] cs0.mem := by
      intro h cs hpf hinit
      rw [stdP, show P0.func? "h" = some fH from rfl] at hpf
      cases hpf
      rw [stdP, csH_init] at hinit
      cases hinit
      exact csH_trapsD F 8
    have hEc : (cutEnv ((L0 F).std.envR 9 fF) ((L0 F).std.covQ ((L0 F).std.TrapsDn 9))).extern "h" =
        some fun vals cm => cutO ((L0 F).std.covQ ((L0 F).std.TrapsDn 9)) "h" vals cm (G vals cm) := by
      simp only [cutEnv, hE, Option.map_some]
    have hGc : cutO ((L0 F).std.covQ ((L0 F).std.TrapsDn 9)) "h" [v41] cs0.mem (G [v41] cs0.mem) =
        .trapped (.user 1) := by
      unfold cutO
      rw [if_neg (fun h => h.2 hQ)]
      exact hGt
    cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ', hstepR] at hrun
      rw [Clif.runLoop_succ', stdP, cs0_step _ hEc hGc]
      exact hrun

/-- **`TrapsExplicit` does not hold** for `f`'s run on `41`: the premise of
`backend_correct_program_budget` excludes this run (its trapping statement is a call). -/
theorem cs0_not_trapsExplicit (F : BitVec 64 → Prop) :
    ¬ TrapsExplicit (Clif.linkEnvN (L0 F).P (L0 F).base 9) (L0 F).P.bare cs0 := by
  intro h
  obtain ⟨G, hG, hGt⟩ := link_h 9 (by omega) F
  have hstep : Clif.step (Clif.linkEnvN (L0 F).P (L0 F).base 9) (L0 F).P.bare cs0 =
      .trapped (.user 1) := by
    have := cs0_step _ hG hGt
    rw [P_eq]
    rw [stdP] at this
    exact this
  have := h.stmt cs0 _ callStmt [] (.refl _) hstep rfl
  simp [callStmt, explicitTrapInst] at this

/-! ## The theorem applies -/

/-- **`backend_correct_program_trap_budget` applies**: for every `F` containing the code, the
linked system satisfies `Ok`, `TrapsOk`, `BaseTrapsOk` and the stack budget `fun M _ => K M`;
`f`'s whole-program run on `41` traps inside the program callee `h` under the run premise `TrapsD`
(and outside the old premise `TrapsExplicit`); so for every entry state of `f` whose CLIF run
traps, the linked machine has the trap observable. -/
theorem program_trap_applies (F : BitVec 64 → Prop) (hF : ∀ a, (L0 F).Img a → F a) :
    (L0 F).Ok ∧ (L0 F).TrapsOk ∧ (L0 F).BaseTrapsOk ∧ (L0 F).Budget (fun M _ => (L0 F).K M) ∧
    fF ∈ (L0 F).P.funcs ∧ fH ∈ (L0 F).P.funcs ∧ ClifEntry fF [v41] cs0 ∧
    Clif.runLoop (L0 F).base (L0 F).P (9 + 1) cs0 = .trapped (.user 1) ∧
    (L0 F).std.TrapsD 9 fF cs0 ∧
    ¬ TrapsExplicit (Clif.linkEnvN (L0 F).P (L0 F).base 9) (L0 F).P.bare cs0 ∧
    ∀ (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
      {tc : Clif.TrapCode},
      AbiEntry ((L0 F).A fF).fb ((L0 F).A fF).base ra s →
      StackAvail ((L0 F).K M) ((L0 F).A fF).af s →
      (L0 F).F = frameWG ((L0 F).K M) (RAFrame.compute ((L0 F).A fF).vcp ((L0 F).A fF).rf).intBase
        (RAFrame.compute ((L0 F).A fF).vcp ((L0 F).A fF).rf).size ((L0 F).A fF).af (L0 F).Img s →
      (∀ a, (L0 F).Img a → ¬ StackBelow (frameDrop ((L0 F).A fF).af + (L0 F).K M) (spv s) a) →
      (∀ a, (L0 F).Img a → s.mem a = (L0 F).imgMem a) →
      BodyEntry ((L0 F).A fF).af s w₀ → ArgsIn fF.sig args s → ClifEntry fF args cs →
      StackArgsAvoid (L0 F).Img fF.sig args s →
      Rel.holds ⟨(L0 F).F, (L0 F).syms, ((L0 F).A fF).af.slotBase,
        (RAFrame.compute ((L0 F).A fF).vcp ((L0 F).A fF).rf).intBase⟩ fF cs.frame.slots cs.mem w₀ →
      ((L0 F).NeedSlots → (L0 F).PlaceAt cs.mem (spv w₀)) →
      (L0 F).std.TrapsD M fF cs →
      Clif.runLoop (L0 F).base (L0 F).P (M + 1) cs = .trapped tc →
      (L0 F).TrapIn M fF s tc := by
  have hL := L_ok F hF
  have hfF : fF ∈ (L0 F).P.funcs := by rw [funcs_eq]; simp
  refine ⟨hL, trapsOk F, baseTrapsOk F, (L0 F).budget_K hL, hfF, by rw [funcs_eq]; simp,
    cs0_entry, run_traps F, cs0_trapsD F, cs0_not_trapsExplicit F,
    fun M ra s w₀ args cs tc hent hres hFe hgfree himg hbe hargs hcs hsav hrel hpl htr hrun => ?_⟩
  exact backend_correct_program_trap (L0 F) hL (trapsOk F) (baseTrapsOk F) hfF M hent hres hFe
    hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

end E2E.LinkTrapCallWitness

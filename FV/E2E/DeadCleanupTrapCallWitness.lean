import FV.E2E.WorldTrapCall
import FV.Backend.Proof.LowerDecide
import FV.E2E.DeadCleanupCover
import FV.Backend.SpillAlloc

/-!
# Non-vacuity of `backend_correct_final_cleanup_trapcall` (S9a, #33)

A concrete CLIF function whose callee traps (a Rust panic: `Clif.Rust.env`'s panics trap with
`user1`):

```
function %pc(i64) -> i64 system_v {
    fn0 = %panic(i64) -> i64 system_v
block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
```

compiled by the shipped pipeline (`lowerFunction`, dead cleanup `prune`, `prepare`, the spill
allocation, `lowerRFunc`, `emitFunc`, layout). `checks_true` (a closed receipt, `native_decide`,
the convention of `FV/E2E/DeadCleanupUnwindWitness.lean`) decides the decidable premises.

* `final_applies`: `backend_correct_final_cleanup_trapcall` applies to it with the environment
  `env` whose extern `%panic` traps, the trapping callees' contract `XTrapsOk` and the normal
  return contracts (vacuous: no extern returns) discharged; open, as in the old witnesses: the
  machine's callee contract `hC`, the linker's symbol addresses `hsym`, the run's entry
  premises.
* `cs0_trapsC`, `cs0_not_trapsExplicit`, `cs0_traps`: the entered state `cs0` (argument 5): its
  run traps with `user1` inside the callee; **`TrapsExplicitC` holds and `TrapsExplicit` does
  not** — the run is covered by the new theorem and was excluded by the old one.
* `cs0_unwinds`: on it the proof device `trapEnv` ends with an exception (the callee trap).
-/

namespace E2E.DeadCleanupTrapCallWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `(i64) -> i64 system_v`. -/
def sigI : Clif.Signature :=
  { params := [{ ty := .i64 }], returns := [{ ty := .i64 }], callConv := some .systemV }

/-- The call statement `v1 = call fn0(v0)`. -/
def callStmt : Clif.Stmt := { results := [1], inst := .call 0 [0] }

/-- The source function: a call of the extern `%panic`, then `return v1`. -/
def source : Clif.Function :=
  { name := "pc", sig := sigI, externs := [(0, { name := "panic", sig := sigI })],
    blocks := [{ id := 0, params := [(0, .i64)], body := [callStmt], term := .ret [1] }] }

/-- The compiler's outputs (the defaults are never used: `checks_true`). -/
def vc : VCode := (lowerFunction source).toOption.getD default
def vcp : VCode := (Backend.prepare (prune vc)).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default

/-- **The closed receipt**: every decidable premise of the pipeline and of the new theorem on
the compiled function. -/
def checks : Bool :=
  Backend.verifiable source && lowerScopeB source && !hasTls source &&
  (lowerFunction source).toBool && lowerCheckU source vc &&
  (Backend.prepare (prune vc)).toBool && prepCheck (prune vc) vcp &&
  (checkAlloc vcp rf).toBool && (lowerRFunc vcp rf).toBool && (emitFunc 0 af).toBool &&
  fa.layout.toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The compiler path is inhabited by a function with a trapping callee (closed receipt, not
used by any compiler correctness theorem). -/
theorem checks_true : checks = true := by native_decide

theorem ok_getD {ε α : Type} [Inhabited α] {e : Except ε α} (h : e.toBool = true) :
    e = .ok (e.toOption.getD default) := by
  cases e <;> simp_all [Except.toBool, Except.toOption]

theorem ok_unit {ε : Type} {e : Except ε Unit} (h : e.toBool = true) : e = .ok () := by
  cases e <;> simp_all [Except.toBool]

/-- The facts of the receipt. -/
theorem facts :
    Backend.verifiable source = true ∧ lowerScopeB source = true ∧ hasTls source = false ∧
    CompiledCleanup source 0 vc vcp rf af fa fb ∧ lowerCheckU source vc = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hv, hs, ht, hl, hlU, hp, hpc, hca, hal, hem, hla⟩ := h
  exact ⟨hv, hs, ht, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca, ok_getD hal,
    ok_getD hem, ok_getD hla⟩, hlU⟩

/-! ## A trapping callee -/

/-- The environment: `%panic` traps with `user1` (as `Clif.Rust.env`'s panics). -/
def env : Clif.Env :=
  { extern := fun n => if n = "panic" then some (fun _ _ => .trapped (.user 1)) else none }

/-- The external semantics: `X0` without normally returning callees. -/
def Xn (X0 : ExtSem) : ExtSem := { X0 with call := fun _ _ _ => none }

theorem env_extern {n : String} {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    (h : env.extern n = some g) : ∀ vals cm, g vals cm = .trapped (.user 1) := by
  intro vals cm
  simp only [env] at h
  split at h
  · cases h; rfl
  · cases h

theorem xCallsOk_env (exts : List Clif.ExtFunc) (MR : MemRelT) (X : ExtSem) :
    XCallsOk env exts MR X := by
  intro _ _ g _ cm _ _ _ _ vals _ _ hg _ _ _ hr
  rw [env_extern hg] at hr
  cases hr

theorem xCallsIndOk_env (sigs : List Clif.Signature) (MR : MemRelT) (X : ExtSem) :
    XCallsIndOk env sigs MR X := by
  intro _ _ _ g _ cm _ _ _ vals _ _ hg _ _ _ _ _ hr
  rw [env_extern hg] at hr
  cases hr

/-- No callee of `Xn X0` returns normally: the trapping callees' contract holds. -/
theorem xTrapsOk_Xn (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (MR : MemRelT)
    (X0 : ExtSem) : XTrapsOk env exts sigs MR (Xn X0) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩

theorem source_noTry : ∀ B ∈ source.blocks, B.term.isTry = false := by
  intro B hB
  simp only [source, List.mem_singleton] at hB
  subst hB
  rfl

/-- **`backend_correct_final_cleanup_trapcall` applies to the compiled function with a trapping
callee**, leaving open only the machine's callee contract (`hC`), the linker's symbol addresses
(`hsym`) and the run's entry premises. -/
theorem final_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K (Xn X0) H
      vcp.CallSite)
    (hsym : ∀ n b, syms n = some b → (Xn X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn source.sig args s) (hcs : ClifEntry source args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitC env { funcs := [] } cs) {fuel : Nat} {c : Clif.TrapCode}
    (hrun : Clif.runLoop env { funcs := [] } fuel cs = .trapped c) :
    ∃ n, TrapAt fb base c (runX (ArmStepX (Xn X0) H fa) n s) ∨
      (CallTrapAt vcp (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
          K (fun _ => False) s fa base (Xn X0) (fun _ _ => False)
          (TrapCallSem env (source.externs.map (·.2)) (indSigs source) (fun sl cm w =>
            Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
              syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source sl cm w) (Xn X0) c)
          (runX (ArmStepX (Xn X0) H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s (Xn X0) H K (fun _ => False) (fun _ _ => False)
          (runX (ArmStepX (Xn X0) H fa) i s)) := by
  obtain ⟨hv, hs, ht, hc, hlU⟩ := facts
  exact backend_correct_final_cleanup_trapcall (InSubset.of_verifiable hv (fun _ => rfl)) hc.toA
    hlU rfl source_noTry (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _) hC
    (fun h => absurd h (by rw [ht]; decide)) (fun _ => xCallsOk_env _ _ _)
    (fun _ => xCallsIndOk_env _ _ _) (fun _ => xTrapsOk_Xn _ _ _ _) hsym rfl hent hres hbe hargs
    hcs hrel htr hrun

/-- **`backend_correct_world_cleanup_trapcall` applies to the compiled function with a
trapping callee** (the activation inside a linked program: `RelW`, `ActEntry`), leaving open
the linker's symbol addresses (`hsym`) and the run's entry premises. -/
theorem world_applies {X0 : ExtSem} {syms : String → Option Nat} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsym : ∀ n b, syms n = some b → (Xn X0).sym n 0 = BitVec.ofNat 64 b)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry source args cs)
    (hrel : RelW ⟨F, syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F source.sig args w₀)
    (htr : TrapsExplicitC env { funcs := [] } cs) {fuel : Nat} {tc : Clif.TrapCode}
    (hrun : Clif.runLoop env { funcs := [] } fuel cs = .trapped tc) :
    ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G (Xn X0) H base ra s w₀ →
      ∃ n, TrapAt fb base tc (runX (ArmStepX (Xn X0) H fa) n s) ∨
        (CallTrapAt vcp F K G s fa base (Xn X0) (GotV vcp)
            (TrapCallSem env (source.externs.map (·.2)) (indSigs source)
              (RelW ⟨F, syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c) (Xn X0) tc)
            (runX (ArmStepX (Xn X0) H fa) n s) ∧
          ∀ i < n, actGoodX vcp rf af fa fb base s (Xn X0) H K G (GotV vcp)
            (runX (ArmStepX (Xn X0) H fa) i s)) := by
  obtain ⟨hv, hs, -, hc, hlU⟩ := facts
  exact backend_correct_world_cleanup_trapcall (InSubset.of_verifiable hv (fun _ => rfl)) hc hlU
    rfl source_noTry (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _)
    (xCallsOk_env _ _ _) (xCallsIndOk_env _ _ _) (xTrapsOk_Xn _ _ _ _) hsym rfl hcs hrel hargs
    htr hrun

/-! ## A run the new theorem covers and the old one excludes -/

/-- The entered state on argument 5. -/
def regs0 : Clif.Regs := Clif.Regs.set Clif.Regs.empty 0 ⟨.i64, 5⟩

def cs0 : Clif.State := ⟨⟨source, regs0, [], [callStmt], .ret [1]⟩, [], Clif.Mem.empty⟩

theorem cs0_entry : ClifEntry source [⟨.i64, 5⟩] cs0 :=
  ⟨rfl, rfl, rfl, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Its step traps with `user1`, inside the callee `%panic`. -/
theorem cs0_step : Clif.step env { funcs := [] } cs0 = .trapped (.user 1) := by rfl

theorem cs0_traps : Clif.runLoop env { funcs := [] } 1 cs0 = .trapped (.user 1) := by
  rw [Clif.runLoop_succ, cs0_step]

theorem cs0_reach {s : Clif.State} (h : Reach env { funcs := [] } cs0 s) : s = cs0 := by
  cases h with
  | refl => rfl
  | step h1 _ => rw [cs0_step] at h1; cases h1

/-- **`TrapsExplicitC` holds** for the run of `cs0` (its trap is a callee's). -/
theorem cs0_trapsC : TrapsExplicitC env { funcs := [] } cs0 := by
  refine ⟨fun s c st rest hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_, fun s _ _ _ _ hr _ hb => ?_,
    fun s st rest _ _ _ hr hb hi => ?_, fun s _ _ _ hr hb => ?_⟩
  · obtain rfl := cs0_reach hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    exact .inr (.inl ⟨0, [0], rfl⟩)
  · obtain rfl := cs0_reach hr; cases hb
  · obtain rfl := cs0_reach hr; cases hb
  · obtain rfl := cs0_reach hr
    simp only [cs0, List.cons.injEq] at hb
    obtain ⟨rfl, -⟩ := hb
    cases hi
  · obtain rfl := cs0_reach hr; cases hb

/-- **`TrapsExplicit` does not hold**: the old theorem excludes this run. -/
theorem cs0_not_trapsExplicit : ¬ TrapsExplicit env { funcs := [] } cs0 := by
  intro h
  have := h.stmt cs0 _ callStmt [] (.refl _) cs0_step rfl
  simp [callStmt, explicitTrapInst] at this

/-- On `cs0` the proof device's run with unwinding ends with an exception. -/
theorem cs0_unwinds : ∃ e m, Clif.runLoopX (trapEnv env (.user 1)) { funcs := [] } 1 cs0.toX =
    .unwound e m :=
  ⟨_, _, rfl⟩

end E2E.DeadCleanupTrapCallWitness

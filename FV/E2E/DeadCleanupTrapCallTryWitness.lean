import FV.E2E.DeadCleanupTrapCallTry
import FV.E2E.DeadCleanupTrapCallWitness

/-!
# Non-vacuity of `backend_correct_final_cleanup_trapcallT` (S9b, #375)

A concrete CLIF function with a `try_call` whose callee traps (a Rust panic: `Clif.Rust.env`'s
panics trap with `user1`):

```
function %tp(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %panic(i64) -> i64 system_v
block0(v0: i64):
    try_call fn0(v0), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v1: i64):
    return v1
block2(v2: i64):
    return v2
}
```

compiled by the shipped pipeline (`lowerFunction`, dead cleanup `prune`, `prepare`, the spill
allocation, `lowerRFunc`, `emitFunc`, layout). `checks_true` (a closed receipt, `native_decide`,
the convention of `FV/E2E/DeadCleanupUnwindWitness.lean`) decides the decidable premises.

* `final_applies`: `backend_correct_final_cleanup_trapcallT` applies to it with the environment
  `DeadCleanupTrapCallWitness.env` whose extern `%panic` traps, the trapping callees' contract
  `XTrapsOk` and the normal return contracts (vacuous: no extern returns) discharged; open, as in
  the S9a witness: the machine's callee contract `hC`, the linker's symbol addresses `hsym`, the
  run's entry premises.
* `source_hasTry`: the function has a `try_call` terminator, so S9a's
  `backend_correct_final_cleanup_trapcall` (premise `∀ B ∈ f.blocks, B.term.isTry = false`) does
  not apply to it.
* `cs0_trapsCT`, `cs0_traps`: the entered state `cs0` (argument 5): its run traps with `user1`
  inside the `try_call`'s callee, and **`TrapsExplicitCT` holds** — the run is covered by the new
  theorem.
-/

namespace E2E.DeadCleanupTrapCallTryWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
open DeadCleanupTrapCallWitness (sigI env Xn xCallsOk_env xCallsIndOk_env xTrapsOk_Xn ok_getD
  ok_unit)

/-- The exception table: `sig0, block1(ret0), [ tag0: block2(exn0) ]`. -/
def et : Clif.ExnTable :=
  { sig := 0, normal := { block := 1, args := [.ret 0] },
    items := [.tag 0 { block := 2, args := [.exn 0] }] }

/-- The source function: a `try_call` of the extern `%panic`, a `tag0` handler. -/
def source : Clif.Function :=
  { name := "tp", sig := sigI, externs := [(0, { name := "panic", sig := sigI })],
    sigDecls := [(0, sigI)],
    blocks := [
      { id := 0, params := [(0, .i64)], term := .tryCall 0 [0] et },
      { id := 1, params := [(1, .i64)], term := .ret [1] },
      { id := 2, params := [(2, .i64)], term := .ret [2] }] }

/-- The compiler's outputs (the defaults are never used: `checks_true`). -/
def vc : VCode := (lowerFunction source).toOption.getD default
def vcp : VCode := (Backend.prepare (cleanupStage source vc)).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default

/-- **The closed receipt**: every decidable premise of the pipeline and of the new theorem on
the compiled function. -/
def checks : Bool :=
  Backend.verifiable source && lowerScopeB source && !hasTls source &&
  (lowerFunction source).toBool && lowerCheckU source vc &&
  (Backend.prepare (cleanupStage source vc)).toBool && prepCheck (cleanupStage source vc) vcp &&
  (checkAlloc vcp rf).toBool && (lowerRFunc vcp rf).toBool && (emitFunc 0 af).toBool &&
  fa.layout.toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The compiler path is inhabited by a function with a `try_call` of a trapping callee (closed
receipt, not used by any compiler correctness theorem). -/
theorem checks_true : checks = true := by native_decide

/-- The facts of the receipt. -/
theorem facts :
    Backend.verifiable source = true ∧ lowerScopeB source = true ∧ hasTls source = false ∧
    CompiledCleanup source 0 vc vcp rf af fa fb ∧ lowerCheckU source vc = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hv, hs, ht, hl, hlU, hp, hpc, hca, hal, hem, hla⟩ := h
  exact ⟨hv, hs, ht, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca, ok_getD hal,
    ok_getD hem, ok_getD hla⟩, hlU⟩

/-- **S9a does not apply**: the function has a `try_call` terminator. -/
theorem source_hasTry : ¬ ∀ B ∈ source.blocks, B.term.isTry = false := by
  intro h
  have := h _ (List.mem_cons_self ..)
  simp [Clif.Terminator.isTry] at this

/-- **`backend_correct_final_cleanup_trapcallT` applies to the compiled function with a
`try_call` of a trapping callee**, leaving open only the machine's callee contract (`hC`), the
linker's symbol addresses (`hsym`) and the run's entry premises. -/
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
    (htr : TrapsExplicitCT env { funcs := [] } cs) {fuel : Nat} {c : Clif.TrapCode}
    (hrun : Clif.runLoop env { funcs := [] } fuel cs = .trapped c) :
    ∃ n, TrapAt fb base c (runX (ArmStepX (Xn X0) H fa) n s) ∨
      (CallTrapAtT vcp (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
          K (fun _ => False) s fa base (Xn X0) (fun _ _ => False)
          (TrapCallSem env (source.externs.map (·.2)) (indSigs source) (fun sl cm w =>
            Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
              syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source sl cm w) (Xn X0) c)
          (runX (ArmStepX (Xn X0) H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s (Xn X0) H K (fun _ => False) (fun _ _ => False)
          (runX (ArmStepX (Xn X0) H fa) i s)) := by
  obtain ⟨hv, hs, ht, hc, hlU⟩ := facts
  exact backend_correct_final_cleanup_trapcallT (InSubset.of_verifiable hv (fun _ => rfl)) hc.toA
    hlU rfl (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _) hC
    (fun h => absurd h (by rw [ht]; decide)) (fun _ => xCallsOk_env _ _ _)
    (fun _ => xCallsIndOk_env _ _ _) (fun _ => xTrapsOk_Xn _ _ _ _) hsym rfl hent hres hbe hargs
    hcs hrel htr hrun

/-! ## A run the new theorem covers -/

/-- The entered state on argument 5. -/
def regs0 : Clif.Regs := Clif.Regs.set Clif.Regs.empty 0 ⟨.i64, 5⟩

def cs0 : Clif.State := ⟨⟨source, regs0, [], [], .tryCall 0 [0] et⟩, [], Clif.Mem.empty⟩

theorem cs0_entry : ClifEntry source [⟨.i64, 5⟩] cs0 :=
  ⟨rfl, rfl, rfl, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Its step traps with `user1`, inside the `try_call`'s callee `%panic`. -/
theorem cs0_step : Clif.step env { funcs := [] } cs0 = .trapped (.user 1) := by rfl

theorem cs0_traps : Clif.runLoop env { funcs := [] } 1 cs0 = .trapped (.user 1) := by
  rw [Clif.runLoop_succ, cs0_step]

theorem cs0_reach {s : Clif.State} (h : Reach env { funcs := [] } cs0 s) : s = cs0 := by
  cases h with
  | refl => rfl
  | step h1 _ => rw [cs0_step] at h1; cases h1

/-- **`TrapsExplicitCT` holds** for the run of `cs0` (its trap is the `try_call` callee's). -/
theorem cs0_trapsCT : TrapsExplicitCT env { funcs := [] } cs0 := by
  refine ⟨fun s _ st rest hr _ hb => ?_, fun s st rest _ _ _ hr hb => ?_,
    fun s _ _ _ hr _ ht => ?_⟩
  · obtain rfl := cs0_reach hr; cases hb
  · obtain rfl := cs0_reach hr; cases hb
  · obtain rfl := cs0_reach hr; cases ht

end E2E.DeadCleanupTrapCallTryWitness

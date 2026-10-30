import FV.E2E.DeadCleanupUnwindFinal
import FV.Backend.Proof.LowerDecide
import FV.E2E.DeadCleanupCover
import FV.Backend.SpillAlloc

/-!
# Non-vacuity of `backend_correct_final_cleanup_unwind` (S10e, #232)

A concrete CLIF function with a `try_call` (`corpus/clif-regress/try_call.clif`'s shape):

```
function %tc(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %add1(i64) -> i64 system_v
block0(v0: i64):
    try_call fn0(v0), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v1: i64):
    return v1
block2(v2: i64):
    return v2
}
```

compiled by the shipped pipeline (`lowerFunction`, dead cleanup `prune`, `prepare`, the spill
allocation, `lowerRFunc`, `emitFunc`, layout), with the unwind tables `T` the unwinder reads built
from the emitted call-site table (`callSites`, one entry: the function has a landing pad) and frame
rows (`unwindRows`). `checks_true` (a closed receipt, `native_decide`, the convention of
`FV/E2E/DeadCleanupWitness.lean`) decides every decidable premise of the new theorem:
`lowerCheckU`, the `CompiledCleanup` pieces, `callSites = .ok (some …)`, `unwindRows`,
`padsNonzeroB`, `lastCallsOk`, `savedCheck`, plus `verifiable` (`InSubset`), `lowerScopeB`
(`FormsCovered`) and `hasTls = false`.

`final_applies` applies `backend_correct_final_cleanup_unwind` to it **with callees that raise**:
every extern unwinds with a Rust panic (`IselSimUWitness.env`), the callees' exceptional semantics
raises object 77 (`IselSimUWitness.XR`), and the machine's raising callees `Uw` raise 77 from the
call state (the unwinder restores it unchanged); the external semantics `Xr X0` has no normally
returning callee (`X0` otherwise arbitrary). The premises discharged here: the unwinding
validator, every table and check premise, the raising callees' contracts (`CalleeUnwOkG`,
`XRaiseOk`, `XRaiseIndOk`), the normal-return callee contracts `XCallsOk`/`XCallsIndOk`
(vacuous: no extern returns), `FormsCovered`, `hTls`, `hslot`. Left open, as in the old
witness: the machine's callee contracts `hC`/`hCT` (the hooks `H`), the linker's symbol
addresses `hsym`, and the run's entry premises.
-/

namespace E2E.DeadCleanupUnwindWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables

/-- `(i64) -> i64 system_v`. -/
def sigI : Clif.Signature :=
  { params := [{ ty := .i64 }], returns := [{ ty := .i64 }], callConv := some .systemV }

/-- The exception table: `sig0, block1(ret0), [ tag0: block2(exn0) ]`. -/
def et : Clif.ExnTable :=
  { sig := 0, normal := { block := 1, args := [.ret 0] },
    items := [.tag 0 { block := 2, args := [.exn 0] }] }

/-- The source function: a `try_call` of the extern `add1`, a `tag0` handler with the
exception payload `exn0`. -/
def source : Clif.Function :=
  { name := "tc", sig := sigI, externs := [(0, { name := "add1", sig := sigI })],
    sigDecls := [(0, sigI)],
    blocks := [
      { id := 0, params := [(0, .i64)], term := .tryCall 0 [0] et },
      { id := 1, params := [(1, .i64)], term := .ret [1] },
      { id := 2, params := [(2, .i64)], term := .ret [2] }] }

/-- The compiler's outputs (the defaults are never used: `checks_true`). -/
def vc : VCode := (lowerFunction source).toOption.getD default
def vcp : VCode := (Backend.prepare (prune vc)).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default
def lsda : Option (List CallSite) := (callSites af fa).toOption.getD none
def rows : List (Nat × Cfi) := (unwindRows af fa).toOption.getD []

/-- The tables the unwinder reads: the emitted CIE, the FDE rows and the LSDA. -/
def T : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rows, lsda.map (List.map (·.entry))⟩

/-- **The closed receipt**: every decidable premise of the pipeline and of the unwinding theorem
on the compiled function. -/
def checks : Bool :=
  Backend.verifiable source && lowerScopeB source && !hasTls source &&
  (lowerFunction source).toBool && lowerCheckU source vc &&
  (Backend.prepare (prune vc)).toBool && prepCheck (prune vc) vcp &&
  (checkAlloc vcp rf).toBool && (lowerRFunc vcp rf).toBool && (emitFunc 0 af).toBool &&
  fa.layout.toBool && savedCheck vcp rf && padsNonzeroB af fa && lastCallsOk af fa &&
  (callSites af fa).toBool && lsda.isSome && (unwindRows af fa).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The compiler path is inhabited by a function with a landing pad (`lsda.isSome`), using the
fixed-witness convention of `DeadCleanupWitness.checks_true`. This closed receipt is not used by
any compiler correctness theorem. -/
theorem checks_true : checks = true := by native_decide

theorem ok_getD {ε α : Type} [Inhabited α] {e : Except ε α} (h : e.toBool = true) :
    e = .ok (e.toOption.getD default) := by
  cases e <;> simp_all [Except.toBool, Except.toOption]

theorem ok_unit {ε : Type} {e : Except ε Unit} (h : e.toBool = true) : e = .ok () := by
  cases e <;> simp_all [Except.toBool]

/-- The facts of the receipt. -/
theorem facts :
    Backend.verifiable source = true ∧ lowerScopeB source = true ∧ hasTls source = false ∧
    CompiledCleanup source 0 vc vcp rf af fa fb ∧ lowerCheckU source vc = true ∧
    savedCheck vcp rf = true ∧ padsNonzeroB af fa = true ∧ lastCallsOk af fa = true ∧
    callSites af fa = .ok lsda ∧ lsda.isSome = true ∧ unwindRows af fa = .ok rows := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hv, hs, ht, hl, hlU, hp, hpc, hca, hal, hem, hla, hsv, hpad, hlast, hcs, hsome,
    hrows⟩ := h
  exact ⟨hv, hs, ht, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca, ok_getD hal,
    ok_getD hem, ok_getD hla⟩, hlU, hsv, hpad, hlast, ok_getD hcs, hsome, ok_getD hrows⟩

/-! ## Raising callees -/

/-- The external semantics: `X0` without normally returning callees. -/
def Xr (X0 : ExtSem) : ExtSem := { X0 with call := fun _ _ _ => none }

/-- The machine's raising callees: raise object 77, the unwinder restoring the call state. -/
def Uw : Unw.UnwHooks := ⟨fun _ s => some (77, s)⟩

/-- **The raising callees' contract holds** for `IselSimUWitness.XR` and `Uw`, at every
activation. -/
theorem calleeUnwOkG_raise (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (X0 : ExtSem) (S : CallInfo → Prop)
    (gv : Nat → String → Prop) :
    CalleeUnwOkG F K G s0 Pc (Xr X0) IselSimUWitness.XR Uw S gv where
  os := by
    intro info i _ _ s _ _ _ c wh ops regs i' w _ _ _ _ hsw _ herr _ obj w' h
    simp only [IselSimUWitness.XR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, rfl, hsw, ⟨rfl, fun _ _ => rfl, rfl⟩, herr, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  noRaise := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h
  excl := fun _ _ _ h => absurd rfl h

/-- No extern of `IselSimUWitness.env` returns normally: the normal-return contracts hold. -/
theorem xCallsOk_env (exts : List Clif.ExtFunc) (MR : MemRelT) (X : ExtSem) :
    XCallsOk IselSimUWitness.env.toEnv exts MR X := by
  intro _ _ g _ cm _ _ _ _ vals _ _ hg _ _ _ hr
  obtain ⟨g0, hg0, hgg⟩ := toEnv_extern hg
  simp only [IselSimUWitness.env, Option.some.injEq] at hg0
  subst hg0
  have := toOutcome_returned ((hgg vals cm).symm.trans hr)
  cases this

theorem xCallsIndOk_env (sigs : List Clif.Signature) (MR : MemRelT) (X : ExtSem) :
    XCallsIndOk IselSimUWitness.env.toEnv sigs MR X := by
  intro _ _ _ g _ cm _ _ _ vals _ _ hg _ _ _ _ _ hr
  obtain ⟨g0, hg0, hgg⟩ := toEnv_extern hg
  simp only [IselSimUWitness.env, Option.some.injEq] at hg0
  subst hg0
  have := toOutcome_returned ((hgg vals cm).symm.trans hr)
  cases this

/-- **`backend_correct_final_cleanup_unwind` applies to the compiled `try_call` function with
raising callees**, leaving open only what the old witness leaves open: the machine's callee
contracts (`hC`, `hCT`), the linker's symbol addresses (`hsym`) and the run's entry premises. -/
theorem final_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K (Xr X0) H
      vcp.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) (Xr X0) H
      vcp.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn source.sig args s) (hcs : ClifEntry source args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU (Xr X0) H Uw T fa) s
      (Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX) := by
  obtain ⟨hv, hs, ht, hc, hlU, hsv, hpad, hlast, hcs', -, hrows⟩ := facts
  exact backend_correct_final_cleanup_unwind (InSubset.of_verifiable hv (fun _ => rfl)) hc hlU
    (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide))
    (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _ _)
    (fun _ => xCallsOk_env _ _ _) (fun _ => xCallsIndOk_env _ _ _)
    (fun _ => IselSimUWitness.xRaiseOk _ _ _) (fun _ => IselSimUWitness.xRaiseIndOk _ _ _)
    hsym rfl hcs' rfl hrows rfl rfl hpad hlast hsv hent hres hbe hargs hcs hrel htr fuel

end E2E.DeadCleanupUnwindWitness

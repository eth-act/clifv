import FV.E2E.ConstPhiE2E
import FV.E2E.OptUnwindWitness
import FV.Opt.Proof.ConstPhiWitness
import FV.E2E.VerifiableT

/-!
# Non-vacuity of the end-to-end theorems over a pass, at constant-phi removal (#990)

Each theorem of `FV/E2E/PassX.lean` applies with `T := Opt.ConstPhi.run` to a function the pass
really changes, compiled by the shipped pipeline (closed receipts by `native_decide`, the
convention of `FV/E2E/OptUnwindWitness.lean`). Left open, as there: the machine's callee
contracts (`hC`, `hCT` where the function has a `try_call`), the linker's symbol addresses
(`hsym`) and the run's entry premises.

* `pass_entry_returns`: `pass_entry` on `Opt.ConstPhi.Witness.fwd` (`block1(v1)` receives only
  `v0`; the pass removes `v1`, `fwd_run`): the source run on `5` returns `[5]`, and so does the
  transformed program's run;
* `pass_cleanup_applies`, `pass_applies`: `backend_correct_pass_cleanup`, `backend_correct_pass`
  on `fwd` (no extern, no indirect call: those contracts are discharged);
* `pass_finalTCF_applies`: `backend_correct_pass_finalTCF` on `fwdF`, `fwd` at `f64` (outside
  subset E, inside the typed scope);
* `pass_cleanup_unwind_applies`, `pass_unwind_applies`: the unwinding theorems on `tcp`, whose
  `try_call` argument is a constant phi, every extern raising (`IselSimUWitness.env`, the raising
  callees' contracts discharged);
* `legal_pass_applies`, `legal_pass_cleanup_applies`, `legal_pass_unwind_applies`: the
  legalisation theorems on `Clif.Rust.LegalXWitness.src` (an `i128` function with a raising
  `try_call`) and its legalisation `gL`, `hCT` open.
-/

namespace E2E.ConstPhiE2EWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables
open E2E.DeadCleanupUnwindWitness (Xr Uw calleeUnwOkG_raise ok_getD ok_unit xCallsOk_env
  xCallsIndOk_env sigI et)
open Opt.ConstPhi.Witness (fwd fwd' fwd_run)

abbrev cp : Clif.Function → Clif.Function := Opt.ConstPhi.run

theorem passProg_nil : passProg cp { funcs := [] } = { funcs := [] } := rfl

/-! ## `pass_entry` on a run -/

/-- The entry state of `fwd` on the argument `5`. -/
def cs0 : Clif.State :=
  ⟨{ func := fwd, regs := (Clif.Regs.empty.setMany [0] [⟨.i64, 5⟩]).getD Clif.Regs.empty,
     slots := [], body := [], term := .jump ⟨1, [0]⟩ }, [], Clif.Mem.empty⟩

theorem entry0 : ClifEntry fwd [⟨.i64, 5⟩] cs0 :=
  ⟨rfl, rfl, rfl, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem src_returns : ∃ M, Clif.runLoop Clif.Rust.env { funcs := [] } 10 cs0 =
    .returned [⟨.i64, 5⟩] M := ⟨Clif.Mem.empty, rfl⟩

/-- **`pass_entry` applies on a returning run**: the transformed program's run from the
corresponding entry of `run fwd` (`fwd'`, without the parameter) returns `[5]` too. -/
theorem pass_entry_returns : ∃ k M, Clif.runLoop Clif.Rust.env { funcs := [] } k
    (passEntry cp fwd cs0) = .returned [⟨.i64, 5⟩] M := by
  obtain ⟨-, -, -, n', hn⟩ := pass_entry (T := cp) Opt.ConstPhi.run_simX
    (p := { funcs := [] }) RustSyms.envKeepsSymbols_env entry0 10
  obtain ⟨M, hM⟩ := src_returns
  exact ⟨n', M, hn.1 _ _ hM⟩

/-! ## `backend_correct_pass{,_cleanup}` on `fwd` -/

def vc : VCode := (lowerFunction fwd').toOption.getD default
def vcp : VCode := (Backend.prepare (cleanupStage fwd' vc)).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default

def vcpL : VCode := (Backend.prepare vc).toOption.getD default
def rfL : RFunc := spillAlloc vcpL
def afL : AFunc := (lowerRFunc vcpL rfL).toOption.getD default
def faL : FnAsm := (emitFunc 0 afL).toOption.getD default
def fbL : FnBin := faL.layout.toOption.getD default

/-- **The closed receipt** of both pipelines on `run fwd`. -/
def checks : Bool :=
  Backend.verifiable fwd && lowerScopeB fwd' && !hasTls fwd' && (indSigs fwd').isEmpty &&
  (lowerFunction fwd').toBool && lowerCheck fwd' vc &&
  (Backend.prepare (cleanupStage fwd' vc)).toBool && prepCheck (cleanupStage fwd' vc) vcp &&
  (checkAlloc vcp rf).toBool && (lowerRFunc vcp rf).toBool && (emitFunc 0 af).toBool &&
  fa.layout.toBool &&
  (Backend.prepare vc).toBool && prepCheck vc vcpL &&
  (checkAlloc vcpL rfL).toBool && (lowerRFunc vcpL rfL).toBool && (emitFunc 0 afL).toBool &&
  faL.layout.toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt (the convention of `DeadCleanupUnwindWitness.checks_true`); not used by any
compiler correctness theorem. -/
theorem checks_true : checks = true := by native_decide

theorem facts :
    Backend.verifiable fwd = true ∧ lowerScopeB fwd' = true ∧ hasTls fwd' = false ∧
    indSigs fwd' = [] ∧ CompiledCleanup fwd' 0 vc vcp rf af fa fb ∧
    Compiled fwd' 0 vc vcpL rfL afL faL fbL := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, and_assoc] at h
  obtain ⟨hv, hs, ht, hi, hl, hlc, hp, hpc, hca, hal, hem, hla, hpL, hpcL, hcaL, halL, hemL,
    hlaL⟩ := h
  exact ⟨hv, hs, ht, hi, ⟨ok_getD hl, hlc, ok_getD hp, hpc, ok_unit hca, ok_getD hal,
    ok_getD hem, ok_getD hla⟩, ⟨ok_getD hl, hlc, ok_getD hpL, hpcL, ok_unit hcaL, ok_getD halL,
    ok_getD hemL, ok_getD hlaL⟩⟩

theorem noTry : ¬ ∃ B ∈ (cp fwd).blocks, B.term.isTry = true := by
  rw [show cp fwd = fwd' from fwd_run]
  rintro ⟨B, hB, h⟩
  simp only [fwd', fwd, List.mem_cons, List.mem_nil_iff, or_false] at hB
  rcases hB with rfl | rfl <;> exact absurd h (by decide)

/-- **`backend_correct_pass_cleanup` applies to the compiled constant-phi removal of `fwd`**: the
pass's facts (`run_simX`, `run_shape`), the subset, the compiled code, `FormsCovered`, the
`try_call`, TLS, extern and indirect-call contracts (vacuous) and `hslot` are discharged. -/
theorem pass_cleanup_applies {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H
      vcp.CallSite)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn fwd.sig args s) (hcs : ClifEntry fwd args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ fwd cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (passProg cp { funcs := [] }) (passEntry cp fwd cs)) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env { funcs := [] } fuel cs) := by
  obtain ⟨hv, hs, ht, hi, hcc, -⟩ := facts
  have hrun : cp fwd = fwd' := fwd_run
  exact backend_correct_pass_cleanup (T := cp) Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape
    (p := { funcs := [] }) (InSubset.of_verifiable hv (fun _ => rfl)) (hrun ▸ hcc)
    (formsCovered_cleanup_complete (lowerScope_of hs) hcc.lower hcc.prepare _) hC
    (fun h => absurd h noTry) (fun h => absurd h (by rw [hrun, ht]; decide))
    (fun _ ext hin => by simp [fwd] at hin)
    (fun _ => by rw [hrun, hi]; exact xCallsIndOk_nil _ _ _) hsym rfl hE hent hres hbe hargs
    hcs hrel htr fuel

/-- **`backend_correct_pass` applies** to `fwd`'s constant-phi removal compiled without the dead
cleanup; open as `pass_cleanup_applies`. -/
theorem pass_applies {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpL rfL).intBase (RAFrame.compute vcpL rfL).size afL s) K X H
      vcpL.CallSite)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fbL base ra s) (hres : StackAvail K afL s) (hbe : BodyEntry afL s w₀)
    (hargs : ArgsIn fwd.sig args s) (hcs : ClifEntry fwd args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpL rfL).intBase
      (RAFrame.compute vcpL rfL).size afL s, syms, afL.slotBase,
      (RAFrame.compute vcpL rfL).intBase⟩ fwd cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (passProg cp { funcs := [] }) (passEntry cp fwd cs)) (fuel : Nat) :
    ArmRefines fbL base ra (ArmStepX X H faL) s (Clif.runLoop env { funcs := [] } fuel cs) := by
  obtain ⟨hv, hs, ht, hi, -, hc⟩ := facts
  have hrun : cp fwd = fwd' := fwd_run
  exact backend_correct_pass (T := cp) Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape
    (p := { funcs := [] }) (InSubset.of_verifiable hv (fun _ => rfl)) (hrun ▸ hc)
    (formsCovered_completeB hs hc.lower hc.prepare _) hC
    (fun h => absurd h noTry) (fun h => absurd h (by rw [hrun, ht]; decide))
    (fun _ ext hin => by simp [fwd] at hin)
    (fun _ => by rw [hrun, hi]; exact xCallsIndOk_nil _ _ _) hsym rfl hE hent hres hbe hargs
    hcs hrel htr fuel

/-! ## `backend_correct_pass_finalTCF` on `fwd` at `f64` -/

/-- `fwd` at `f64`: `block0(v0: f64): jump block1(v0)`; `block1(v1: f64): return v1`. -/
def fwdF : Clif.Function where
  name := "fwdF"
  sig := { params := [{ ty := .f64 }], returns := [{ ty := .f64 }] }
  blocks := [
    { id := 0, params := [(0, .f64)], term := .jump ⟨1, [0]⟩ },
    { id := 1, params := [(1, .f64)], term := .ret [1] }]

/-- Its constant-phi removal: `block1` returns `v0`. -/
def fwdF' : Clif.Function :=
  { fwdF with blocks := [
    { id := 0, params := [(0, .f64)], term := .jump ⟨1, []⟩ },
    { id := 1, params := [], term := .ret [0] }] }

theorem fwdF_run : cp fwdF = fwdF' := by native_decide -- witness: native_decide

def vcF : VCode := (lowerFunction fwdF').toOption.getD default
def vcpF : VCode := (Backend.prepare vcF).toOption.getD default
def rfF : RFunc := spillAlloc vcpF
def afF : AFunc := (lowerRFunc vcpF rfF).toOption.getD default
def faF : FnAsm := (emitFunc 0 afF).toOption.getD default
def fbF : FnBin := faF.layout.toOption.getD default

/-- **The closed receipt** of the typed pipeline on `run fwdF` (outside subset E). -/
def checksF : Bool :=
  !Compile.functionE fwdF' && verifiableTCF fwdF' && !hasTls fwdF' && (indSigs fwdF').isEmpty &&
  (lowerFunction fwdF').toBool && lowerCheckTCF fwdF' vcF &&
  (Backend.prepare vcF).toBool && prepCheck vcF vcpF &&
  (checkAlloc vcpF rfF).toBool && (lowerRFunc vcpF rfF).toBool && (emitFunc 0 afF).toBool &&
  faF.layout.toBool && formsCoveredB ⟨faF.k, afF.slotBase⟩ vcpF

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt; not used by any compiler correctness theorem. -/
theorem checksF_true : checksF = true := by native_decide

theorem factsF :
    verifiableTCF fwdF' = true ∧ hasTls fwdF' = false ∧ indSigs fwdF' = [] ∧
    CompiledTCF fwdF' 0 vcF vcpF rfF afF faF fbF ∧
    FormsCovered ⟨faF.k, afF.slotBase⟩ vcpF := by
  have h := checksF_true
  simp only [checksF, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, and_assoc] at h
  obtain ⟨-, hv, ht, hi, hl, hlc, hp, hpc, hca, hal, hem, hla, hcov⟩ := h
  exact ⟨hv, ht, hi, ⟨ok_getD hl, hlc, ok_getD hp, hpc, ok_unit hca, ok_getD hal, ok_getD hem,
    ok_getD hla⟩, (formsCoveredB_iff _ _).mp hcov⟩

theorem noTryF : ¬ ∃ B ∈ (cp fwdF).blocks, B.term.isTry = true := by
  rw [fwdF_run]
  rintro ⟨B, hB, h⟩
  simp only [fwdF', fwdF, List.mem_cons, List.mem_nil_iff, or_false] at hB
  rcases hB with rfl | rfl <;> exact absurd h (by decide)

/-- **`backend_correct_pass_finalTCF` applies to the compiled constant-phi removal of `fwdF`**
(an `f64` function outside subset E); open as `pass_cleanup_applies`. -/
theorem pass_finalTCF_applies {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpF rfF).intBase (RAFrame.compute vcpF rfF).size afF s) K X H
      vcpF.CallSite)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fbF base ra s) (hres : StackAvail K afF s) (hbe : BodyEntry afF s w₀)
    (hargs : ArgsIn fwdF.sig args s) (hcs : ClifEntry fwdF args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpF rfF).intBase
      (RAFrame.compute vcpF rfF).size afF s, syms, afF.slotBase,
      (RAFrame.compute vcpF rfF).intBase⟩ fwdF cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (passProg cp { funcs := [] }) (passEntry cp fwdF cs)) (fuel : Nat) :
    ArmRefinesT fbF base ra (ArmStepX X H faF) s (Clif.runLoop env { funcs := [] } fuel cs) := by
  obtain ⟨hv, ht, hi, hc, hcov⟩ := factsF
  exact backend_correct_pass_finalTCF (T := cp) Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape
    (p := { funcs := [] }) (fwdF_run ▸ InSubsetTCF.of_verifiableTCF hv (fun _ => rfl))
    (fwdF_run ▸ hc) hcov hC (fun h => absurd h noTryF)
    (fun h => absurd h (by rw [fwdF_run, ht]; decide))
    (fun _ ext hin => by simp [fwdF] at hin)
    (fun _ => by rw [fwdF_run, hi]; exact xCallsIndOk_nil _ _ _) hsym rfl hE hent hres hbe hargs
    hcs hrel htr fuel

/-! ## The unwinding theorems on a `try_call` whose argument is a constant phi -/

/-- `block0(v0)` jumps to `block3(v0)`, whose `try_call add1(v1)` passes its parameter `v1`
(always `v0`): the pass removes `v1`. -/
def tcp : Clif.Function :=
  { name := "tcp", sig := sigI, externs := [(0, { name := "add1", sig := sigI })],
    sigDecls := [(0, sigI)],
    blocks := [
      { id := 0, params := [(0, .i64)], term := .jump ⟨3, [0]⟩ },
      { id := 3, params := [(1, .i64)], term := .tryCall 0 [1] et },
      { id := 1, params := [(2, .i64)], term := .ret [2] },
      { id := 2, params := [(3, .i64)], term := .ret [3] }] }

/-- Its constant-phi removal. -/
def tcp' : Clif.Function :=
  { tcp with blocks := [
      { id := 0, params := [(0, .i64)], term := .jump ⟨3, []⟩ },
      { id := 3, params := [], term := .tryCall 0 [0] et },
      { id := 1, params := [(2, .i64)], term := .ret [2] },
      { id := 2, params := [(3, .i64)], term := .ret [3] }] }

theorem tcp_run : cp tcp = tcp' := by native_decide -- witness: native_decide

def vcU : VCode := (lowerFunction tcp').toOption.getD default
def vcpU : VCode := (Backend.prepare (cleanupStage tcp' vcU)).toOption.getD default
def rfU : RFunc := spillAlloc vcpU
def afU : AFunc := (lowerRFunc vcpU rfU).toOption.getD default
def faU : FnAsm := (emitFunc 0 afU).toOption.getD default
def fbU : FnBin := faU.layout.toOption.getD default
def lsdaU : Option (List CallSite) := (callSites afU faU).toOption.getD none
def rowsU : List (Nat × Cfi) := (unwindRows afU faU).toOption.getD []
def TU : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rowsU, lsdaU.map (List.map (·.entry))⟩

def vcpUL : VCode := (Backend.prepare vcU).toOption.getD default
def rfUL : RFunc := spillAlloc vcpUL
def afUL : AFunc := (lowerRFunc vcpUL rfUL).toOption.getD default
def faUL : FnAsm := (emitFunc 0 afUL).toOption.getD default
def fbUL : FnBin := faUL.layout.toOption.getD default
def lsdaUL : Option (List CallSite) := (callSites afUL faUL).toOption.getD none
def rowsUL : List (Nat × Cfi) := (unwindRows afUL faUL).toOption.getD []
def TUL : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rowsUL, lsdaUL.map (List.map (·.entry))⟩

/-- **The closed receipt** of both pipelines with the unwinding checks on `run tcp` (it has a
landing pad: `lsdaU.isSome`). -/
def checksU : Bool :=
  Backend.verifiable tcp && lowerScopeB tcp' && !hasTls tcp' && (indSigs tcp').isEmpty &&
  (lowerFunction tcp').toBool && lowerCheckU tcp' vcU && unwCheck tcp' vcU &&
  (Backend.prepare (cleanupStage tcp' vcU)).toBool && prepCheck (cleanupStage tcp' vcU) vcpU &&
  (checkAlloc vcpU rfU).toBool && (lowerRFunc vcpU rfU).toBool && (emitFunc 0 afU).toBool &&
  faU.layout.toBool && savedCheck vcpU rfU && padsNonzeroB afU faU &&
  (callSites afU faU).toBool && lsdaU.isSome && (unwindRows afU faU).toBool &&
  (Backend.prepare vcU).toBool && prepCheck vcU vcpUL &&
  (checkAlloc vcpUL rfUL).toBool && (lowerRFunc vcpUL rfUL).toBool && (emitFunc 0 afUL).toBool &&
  faUL.layout.toBool && savedCheck vcpUL rfUL && padsNonzeroB afUL faUL &&
  (callSites afUL faUL).toBool && (unwindRows afUL faUL).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt; not used by any compiler correctness theorem. -/
theorem checksU_true : checksU = true := by native_decide

theorem factsU :
    Backend.verifiable tcp = true ∧ lowerScopeB tcp' = true ∧ hasTls tcp' = false ∧
    indSigs tcp' = [] ∧ CompiledCleanup tcp' 0 vcU vcpU rfU afU faU fbU ∧
    lowerCheckU tcp' vcU = true ∧ savedCheck vcpU rfU = true ∧ padsNonzeroB afU faU = true ∧
    callSites afU faU = .ok lsdaU ∧ unwindRows afU faU = .ok rowsU ∧
    unwCheck tcp' vcU = true ∧ Compiled tcp' 0 vcU vcpUL rfUL afUL faUL fbUL ∧
    savedCheck vcpUL rfUL = true ∧ padsNonzeroB afUL faUL = true ∧
    callSites afUL faUL = .ok lsdaUL ∧ unwindRows afUL faUL = .ok rowsUL := by
  have h := checksU_true
  simp only [checksU, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, and_assoc] at h
  obtain ⟨hv, hs, ht, hi, hl, hlU, hunw, hp, hpc, hca, hal, hem, hla, hsv, hpad, hcs, -, hrows,
    hpL, hpcL, hcaL, halL, hemL, hlaL, hsvL, hpadL, hcsL, hrowsL⟩ := h
  exact ⟨hv, hs, ht, hi, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, hlU, hsv, hpad, ok_getD hcs, ok_getD hrows, hunw,
    ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hpL, hpcL, ok_unit hcaL, ok_getD halL,
      ok_getD hemL, ok_getD hlaL⟩, hsvL, hpadL, ok_getD hcsL, ok_getD hrowsL⟩

/-- **`backend_correct_pass_cleanup_unwind_any` applies to the compiled constant-phi removal of
`tcp`**, every extern raising: the pass's facts (`run_simU`, `run_shape`), the unwinding
validator, every table and check premise, the raising callees' contracts, the normal-return
contracts, `FormsCovered`, `hTls`, `hslot` are discharged; open: `hC`, `hCT`, `hsym` and the
run's entry premises. -/
theorem pass_cleanup_unwind_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpU rfU).intBase (RAFrame.compute vcpU rfU).size afU s) K
      (Xr X0) H vcpU.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcpU rfU).intBase (RAFrame.compute vcpU rfU).size afU s)
      (Xr X0) H vcpU.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fbU base ra s) (hres : StackAvail K afU s) (hbe : BodyEntry afU s w₀)
    (hargs : ArgsIn tcp.sig args s) (hcs : ClifEntry tcp args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpU rfU).intBase
      (RAFrame.compute vcpU rfU).size afU s, syms, afU.slotBase,
      (RAFrame.compute vcpU rfU).intBase⟩ tcp cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX IselSimUWitness.env (passProg cp { funcs := [] }) (passEntry cp tcp cs))
    (fuel : Nat) :
    ArmRefinesU fbU base ra (Unw.ArmStepU (Xr X0) H Uw TU faU) s
      (Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX) := by
  obtain ⟨hv, hs, ht, hi, hcc, hlU, hsv, hpad, hsites, hrows, -⟩ := factsU
  have hrun : cp tcp = tcp' := tcp_run
  exact backend_correct_pass_cleanup_unwind_any (T := cp) Opt.ConstPhi.run_simU
    Opt.ConstPhi.run_shape (p := { funcs := [] }) (InSubset.of_verifiable hv (fun _ => rfl))
    (hrun ▸ hcc) (hrun ▸ hlU)
    (formsCovered_cleanup_complete (lowerScope_of hs) hcc.lower hcc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [hrun, ht]; decide))
    (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _ _)
    (fun _ => xCallsOk_env _ _ _) (fun _ => xCallsIndOk_env _ _ _)
    (fun _ => IselSimUWitness.xRaiseOk _ _ _) (fun _ => IselSimUWitness.xRaiseIndOk _ _ _)
    hsym rfl OptUnwindWitness.keeps_iselEnv hsites rfl hrows rfl rfl hpad hsv hent hres hbe hargs
    hcs hrel htr fuel

/-- **`backend_correct_pass_unwind_any` applies** to `tcp`'s constant-phi removal compiled
without the dead cleanup; open as `pass_cleanup_unwind_applies`. -/
theorem pass_unwind_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpUL rfUL).intBase (RAFrame.compute vcpUL rfUL).size afUL s) K
      (Xr X0) H vcpUL.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcpUL rfUL).intBase (RAFrame.compute vcpUL rfUL).size afUL s)
      (Xr X0) H vcpUL.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fbUL base ra s) (hres : StackAvail K afUL s) (hbe : BodyEntry afUL s w₀)
    (hargs : ArgsIn tcp.sig args s) (hcs : ClifEntry tcp args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpUL rfUL).intBase
      (RAFrame.compute vcpUL rfUL).size afUL s, syms, afUL.slotBase,
      (RAFrame.compute vcpUL rfUL).intBase⟩ tcp cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX IselSimUWitness.env (passProg cp { funcs := [] }) (passEntry cp tcp cs))
    (fuel : Nat) :
    ArmRefinesU fbUL base ra (Unw.ArmStepU (Xr X0) H Uw TUL faUL) s
      (Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX) := by
  obtain ⟨hv, hs, ht, hi, -, -, -, -, -, -, hunw, hc, hsv, hpad, hsites, hrows⟩ := factsU
  have hrun : cp tcp = tcp' := tcp_run
  exact backend_correct_pass_unwind_any (T := cp) Opt.ConstPhi.run_simU Opt.ConstPhi.run_shape
    (p := { funcs := [] }) (InSubset.of_verifiable hv (fun _ => rfl)) (hrun ▸ hc) (hrun ▸ hunw)
    (formsCovered_completeB hs hc.lower hc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [hrun, ht]; decide))
    (fun _ => xCallsOk_env _ _ _) (fun _ => xCallsIndOk_env _ _ _)
    (fun _ => IselSimUWitness.xRaiseOk _ _ _) (fun _ => IselSimUWitness.xRaiseIndOk _ _ _)
    (fun _ => IselSimUWitness.xRaiseExcl _ _ _ _)
    hsym rfl OptUnwindWitness.keeps_iselEnv (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _ _)
    hsites rfl hpad hrows rfl rfl hsv hent hres hbe hargs hcs hrel htr fuel

/-! ## Legalisation, then the pass -/

section Legal

open Clif.Rust.LegalXWitness (src gL certL raises)

def vcG : VCode := (lowerFunction (cp gL)).toOption.getD default
def vcpG : VCode := (Backend.prepare (cleanupStage (cp gL) vcG)).toOption.getD default
def rfG : RFunc := spillAlloc vcpG
def afG : AFunc := (lowerRFunc vcpG rfG).toOption.getD default
def faG : FnAsm := (emitFunc 0 afG).toOption.getD default
def fbG : FnBin := faG.layout.toOption.getD default
def lsdaG : Option (List CallSite) := (callSites afG faG).toOption.getD none
def rowsG : List (Nat × Cfi) := (unwindRows afG faG).toOption.getD []
def TG : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rowsG, lsdaG.map (List.map (·.entry))⟩

def vcpGL : VCode := (Backend.prepare vcG).toOption.getD default
def rfGL : RFunc := spillAlloc vcpGL
def afGL : AFunc := (lowerRFunc vcpGL rfGL).toOption.getD default
def faGL : FnAsm := (emitFunc 0 afGL).toOption.getD default
def fbGL : FnBin := faGL.layout.toOption.getD default

/-- **The closed receipt** of both pipelines on the constant-phi removal of the legalisation
`gL`. -/
def checksG : Bool :=
  Backend.verifiable gL && lowerScopeB (cp gL) && !hasTls (cp gL) && (indSigs (cp gL)).isEmpty &&
  (lowerFunction (cp gL)).toBool && lowerCheckU (cp gL) vcG &&
  (Backend.prepare (cleanupStage (cp gL) vcG)).toBool &&
  prepCheck (cleanupStage (cp gL) vcG) vcpG &&
  (checkAlloc vcpG rfG).toBool && (lowerRFunc vcpG rfG).toBool && (emitFunc 0 afG).toBool &&
  faG.layout.toBool && savedCheck vcpG rfG && padsNonzeroB afG faG &&
  (callSites afG faG).toBool && lsdaG.isSome && (unwindRows afG faG).toBool &&
  (Backend.prepare vcG).toBool && prepCheck vcG vcpGL &&
  (checkAlloc vcpGL rfGL).toBool && (lowerRFunc vcpGL rfGL).toBool && (emitFunc 0 afGL).toBool &&
  faGL.layout.toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt; not used by any compiler correctness theorem. -/
theorem checksG_true : checksG = true := by native_decide

theorem factsG :
    Backend.verifiable gL = true ∧ lowerScopeB (cp gL) = true ∧ hasTls (cp gL) = false ∧
    indSigs (cp gL) = [] ∧ CompiledCleanup (cp gL) 0 vcG vcpG rfG afG faG fbG ∧
    lowerCheckU (cp gL) vcG = true ∧ savedCheck vcpG rfG = true ∧
    padsNonzeroB afG faG = true ∧ callSites afG faG = .ok lsdaG ∧
    unwindRows afG faG = .ok rowsG ∧ Compiled (cp gL) 0 vcG vcpGL rfGL afGL faGL fbGL := by
  have h := checksG_true
  simp only [checksG, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, and_assoc] at h
  obtain ⟨hv, hs, ht, hi, hl, hlU, hp, hpc, hca, hal, hem, hla, hsv, hpad, hcs, -, hrows,
    hpL, hpcL, hcaL, halL, hemL, hlaL⟩ := h
  exact ⟨hv, hs, ht, hi, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, hlU, hsv, hpad, ok_getD hcs, ok_getD hrows,
    ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hpL, hpcL, ok_unit hcaL, ok_getD halL,
      ok_getD hemL, ok_getD hlaL⟩⟩

theorem srcNoInd : ¬ ∃ sig, Opt.Legal.IndSite src sig := by
  rintro ⟨sig, ⟨B, hB, st, hst, callee, args, -⟩ | ⟨B, hB, callee, args, et, ht, -⟩⟩
  · simp only [src, List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with rfl | rfl | rfl <;> simp at hst
  · simp only [src, List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with rfl | rfl | rfl <;> cases ht

/-- **`backend_correct_legal_pass_wide_cleanup` applies to the compiled constant-phi removal of
the legalisation `gL` of the `i128` function `src`**, under the trusted Rust environment: the
validator (`checkW_of_check`), the program conditions, the pass's facts, the compiled code,
`FormsCovered`, `hTls`, the indirect-call contract (vacuous) and `hslot` are discharged; open:
`hC`, `hCT` (the `try_call`'s callee), the extern contract `hX` (`%throw`), `hsym` and the run's
entry premises. -/
theorem legal_pass_cleanup_applies {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpG rfG).intBase (RAFrame.compute vcpG rfG).size afG s) K X H
      vcpG.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcpG rfG).intBase (RAFrame.compute vcpG rfG).size afG s) X H
      vcpG.TrySite)
    (hX : ∀ s, XCallsOk Clif.Rust.env (gL.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcpG rfG).intBase (RAFrame.compute vcpG rfG).size afG s,
        syms, afG.slotBase, (RAFrame.compute vcpG rfG).intBase⟩ gL sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fbG base ra s) (hres : StackAvail K afG s) (hbe : BodyEntry afG s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups src.sig.params).getD []) args args')
    (hargs : ArgsIn gL.sig args' s) (hcs : ClifEntry src args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpG rfG).intBase
      (RAFrame.compute vcpG rfG).size afG s, syms, afG.slotBase,
      (RAFrame.compute vcpG rfG).intBase⟩ gL cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg cp { funcs := [] }) (passEntry cp gL cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups src.sig.returns).getD []) fbG base ra (ArmStepX X H faG) s
      (Clif.runLoop Clif.Rust.env { funcs := [] } fuel cs) := by
  have hc : Opt.Legal.check src gL certL = true := Clif.Rust.LegalXWitness.validators.1
  obtain ⟨hv, hs, ht, hi, hcc, -⟩ := factsG
  exact backend_correct_legal_pass_wide_cleanup (T := cp) (f := src) (g := gL) (cert := certL)
    (Opt.Legal.checkW_of_check hc) Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape
    (p := { funcs := [] }) (p' := { funcs := [] })
    (InSubset.of_verifiable hv (fun _ => rfl)) hcc
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _)
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _) (fun h => absurd h srcNoInd)
    (formsCovered_cleanup_complete (lowerScope_of hs) hcc.lower hcc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide)) hX (fun _ => hi ▸ xCallsIndOk_nil _ _ _)
    hsym rfl hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_pass_wide` applies** to the constant-phi removal of `gL` compiled
without the dead cleanup; open as `legal_pass_cleanup_applies`. -/
theorem legal_pass_applies {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpGL rfGL).intBase (RAFrame.compute vcpGL rfGL).size afGL s) K X H
      vcpGL.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcpGL rfGL).intBase (RAFrame.compute vcpGL rfGL).size afGL s) X H
      vcpGL.TrySite)
    (hX : ∀ s, XCallsOk Clif.Rust.env (gL.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcpGL rfGL).intBase
        (RAFrame.compute vcpGL rfGL).size afGL s, syms, afGL.slotBase,
        (RAFrame.compute vcpGL rfGL).intBase⟩ gL sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fbGL base ra s) (hres : StackAvail K afGL s) (hbe : BodyEntry afGL s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups src.sig.params).getD []) args args')
    (hargs : ArgsIn gL.sig args' s) (hcs : ClifEntry src args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpGL rfGL).intBase
      (RAFrame.compute vcpGL rfGL).size afGL s, syms, afGL.slotBase,
      (RAFrame.compute vcpGL rfGL).intBase⟩ gL cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg cp { funcs := [] }) (passEntry cp gL cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups src.sig.returns).getD []) fbGL base ra
      (ArmStepX X H faGL) s (Clif.runLoop Clif.Rust.env { funcs := [] } fuel cs) := by
  have hc : Opt.Legal.check src gL certL = true := Clif.Rust.LegalXWitness.validators.1
  obtain ⟨hv, hs, ht, hi, -, -, -, -, -, -, hcc⟩ := factsG
  exact backend_correct_legal_pass_wide (T := cp) (f := src) (g := gL) (cert := certL)
    (Opt.Legal.checkW_of_check hc) Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape
    (p := { funcs := [] }) (p' := { funcs := [] })
    (InSubset.of_verifiable hv (fun _ => rfl)) hcc
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _)
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _) (fun h => absurd h srcNoInd)
    (formsCovered_completeB hs hcc.lower hcc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide)) hX (fun _ => hi ▸ xCallsIndOk_nil _ _ _)
    hsym rfl hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_pass_unwind_any` applies to the compiled constant-phi removal of the
legalisation `gL`** with its raising `%throw`: open as in
`LegalUnwindWitness.legal_unwind_applies`. -/
theorem legal_pass_unwind_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpG rfG).intBase (RAFrame.compute vcpG rfG).size afG s) K
      (Xr X0) H vcpG.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcpG rfG).intBase (RAFrame.compute vcpG rfG).size afG s)
      (Xr X0) H vcpG.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fbG base ra s) (hres : StackAvail K afG s) (hbe : BodyEntry afG s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups src.sig.params).getD []) args args')
    (hargs : ArgsIn gL.sig args' s) (hcs : ClifEntry src args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpG rfG).intBase
      (RAFrame.compute vcpG rfG).size afG s, syms, afG.slotBase,
      (RAFrame.compute vcpG rfG).intBase⟩ gL cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX LegalUnwindWitness.xe { funcs := [] } cs)
    (htr : TrapsExplicitX LegalUnwindWitness.xe (passProg cp { funcs := [] }) (passEntry cp gL cs'))
    (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups src.sig.returns).getD []) fbG base ra
      (Unw.ArmStepU (Xr X0) H Uw TG faG) s
      (Clif.runLoopX LegalUnwindWitness.xe { funcs := [] } fuel cs.toX) := by
  have hc : Opt.Legal.check src gL certL = true := Clif.Rust.LegalXWitness.validators.1
  have hx : Opt.Legal.exnOk src gL certL = true := Clif.Rust.LegalXWitness.validators.2
  obtain ⟨hv, hs, ht, hi, hcc, hlU, hsv, hpad, hsites, hrows, -⟩ := factsG
  exact backend_correct_legal_pass_unwind_any (T := cp) (f := src) (g := gL) (cert := certL)
    hc hx Opt.ConstPhi.run_simU Opt.ConstPhi.run_shape (p' := { funcs := [] })
    (InSubset.of_verifiable hv (fun _ => rfl)) hcc hlU raises 77
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _)
    (fun _ _ _ => Clif.Rust.LegalXWitness.func?_nil _)
    (fun ⟨B, hB, st, hst, _⟩ => by
      simp only [src, List.mem_cons, List.mem_nil_iff, or_false] at hB
      rcases hB with rfl | rfl | rfl <;> simp at hst)
    (formsCovered_cleanup_complete (lowerScope_of hs) hcc.lower hcc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide))
    (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _ _)
    (fun _ => LegalUnwindWitness.xCallsOk_xe _ _) (fun _ => hi ▸ xCallsIndOk_nil _ _ _)
    (fun _ => LegalUnwindWitness.xRaiseOk_xe _ _) (fun _ => hi ▸ fun _ h => nomatch h)
    hsym rfl hsites rfl hrows rfl rfl hpad hsv hent hres hbe hexp hargs hcs hcs' hsl hmem
    hrel htrS htr fuel

end Legal

end E2E.ConstPhiE2EWitness

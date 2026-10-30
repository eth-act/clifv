import FV.E2E.OptUnwind
import FV.E2E.LegalOptUnwind
import FV.Backend.Proof.FormsCoverComplete
import FV.E2E.LegalUnwindWitness

/-!
# Non-vacuity of `optExe_entryX` and `backend_correct_opt_exe_cleanup_unwind` (S10f, #233)

The witness function, whose `try_call` callee raises:

```
function %w(i64) system_v {
    sig0 = (i64) system_v
    fn0 = %throw(i64) system_v
block0(v0: i64):
    v1 = iconst.i64 0
    v2 = iadd v0, v1
    try_call fn0(v2), sig0, block1, [ tag0: block2(exn0) ]
block1:
    return
block2(v3: i64):
    return
}
```

The mid-end of the executable compiler with the proven rule sets (`Opt.exeConfig`) rewrites
`v0 + 0` to `v0` and removes the dead statements: its output reads `try_call fn0(v0)`
(`optimized`). The environment is the trusted Rust environment with unwinding
`Clif.Rust.xenvWith raises 77` with `raises := (· == "throw")`: `%throw` raises Rust's
exception (object 77), the `tag0` handler catches it.

* `caught`: the source run with unwinding raises at the `try_call` and is caught (it returns:
  `%throw` never returns normally);
* `refines`: `optExe_entryX` applies with every premise discharged (`xenvWith_keepsSymbolsX`):
  the optimised program's run with unwinding from the corresponding entry returns too;
* `opt_unwind_applies`: `backend_correct_opt_exe_cleanup_unwind` applies to the shipped
  compiler's output on the optimised function (closed receipt `checks_true`, `native_decide`,
  the convention of `FV/E2E/DeadCleanupUnwindWitness.lean`) with raising callees, leaving open
  what `LegalUnwindWitness.legal_unwind_applies` leaves open: the machine's callee contracts
  (`hC`/`hCT`), the linker's symbol addresses (`hsym`) and the run's entry premises;
  `opt_unwind_applies_legacy`: `backend_correct_opt_exe_unwind` on the pipeline without the dead
  cleanup, every extern raising (`IselSimUWitness.env`, as `WorldUnwindWitness.world_applies_legacy`);
* `LegalOptUnwindWitness.legal_opt_unwind_applies`: `backend_correct_legal_opt_unwind` on the
  compiled optimisation of `LegalXWitness.gL` (the legalisation of `%w(i128)`), the same premises
  open.
-/

namespace E2E.OptUnwindWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables
open E2E.DeadCleanupUnwindWitness (Xr Uw calleeUnwOkG_raise ok_getD ok_unit xCallsOk_env
  xCallsIndOk_env)

def i64p : Clif.AbiParam := { ty := .i64 }
def sigT : Clif.Signature := { params := [i64p], returns := [], callConv := some .systemV }

def et : Clif.ExnTable :=
  { sig := 0, normal := { block := 1, args := [] },
    items := [.tag 0 { block := 2, args := [.exn 0] }] }

/-- The entry block: `v2 = v0 + 0`, `try_call %throw(v2)`. -/
def b0 : Clif.Block :=
  { id := 0, params := [(0, .i64)],
    body := [{ results := [1], inst := .iconst .i64 0 },
             { results := [2], inst := .binary .iadd .i64 0 1 }],
    term := .tryCall 0 [2] et }

/-- The source function. -/
def src : Clif.Function :=
  { name := "w", sig := sigT, externs := [(0, { name := "throw", sig := sigT })],
    sigDecls := [(0, sigT)],
    blocks := [b0,
      { id := 1, params := [], term := .ret [] },
      { id := 2, params := [(3, .i64)], term := .ret [] }] }

/-- The optimised function. -/
abbrev gO : Clif.Function := Opt.optimizeExe src Opt.exeConfig

/-- **The mid-end transforms the function**: the statements are gone and the `try_call` reads
`v0`. -/
theorem optimized : gO.blocks = [
    { id := 0, params := [(0, .i64)], term := .tryCall 0 [0] et },
    { id := 1, params := [], term := .ret [] },
    { id := 2, params := [(3, .i64)], term := .ret [] }] := by
  native_decide

def raises (n : String) : Bool := n == "throw"

/-- The trusted Rust environment with unwinding, `%throw` raising object 77. -/
abbrev xe : Clif.XEnv := Clif.Rust.xenvWith raises 77

/-- The entry state on the argument `5`. -/
def cs0 : Clif.State :=
  ⟨{ func := src, regs := (Clif.Regs.empty.setMany [0] [⟨.i64, 5⟩]).getD Clif.Regs.empty,
     slots := [], body := b0.body, term := b0.term }, [], Clif.Mem.empty⟩

theorem entry : ClifEntry src [⟨.i64, 5⟩] cs0 :=
  ⟨rfl, rfl, rfl, ⟨b0, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- **The source run with unwinding raises and catches**: `%throw` raises, the `tag0` handler
catches, the run returns. -/
theorem caught :
    (Clif.runLoopX xe { funcs := [] } 10 cs0.toX).returnedVals? = some [] := by
  decide +kernel

/-- **`optExe_entryX` applies** to the raising-and-catching run with every premise discharged:
the optimised program's run with unwinding returns too. -/
theorem refines : ∃ k M, Clif.runLoopX xe { funcs := [] } k
    (optEntryX Opt.exeConfig src cs0).toX = .returned [] M := by
  obtain ⟨-, -, -, n', hn⟩ := optExe_entryX Opt.exeConfig rfl rfl (p := { funcs := [] })
    (xenvWith_keepsSymbolsX raises 77) entry 10
  obtain ⟨M, hM⟩ : ∃ M, Clif.runLoopX xe { funcs := [] } 10 cs0.toX = .returned [] M := by
    have := caught
    revert this
    cases Clif.runLoopX xe { funcs := [] } 10 cs0.toX <;> simp [Clif.XOutcome.returnedVals?]
  have h := hn.1 [] M hM
  exact ⟨n', M, h⟩

/-! ## `backend_correct_opt_exe_cleanup_unwind` on the compiled optimised function -/

/-- The compiler's outputs on the optimised function (the defaults are never used:
`checks_true`). -/
def vc : VCode := (lowerFunction gO).toOption.getD default
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
on the compiled optimised function (it has a landing pad: `lsda.isSome`, no indirect call). -/
def checks : Bool :=
  Backend.verifiable src && lowerScopeB gO && !hasTls gO && (indSigs gO).isEmpty &&
  (lowerFunction gO).toBool && lowerCheckU gO vc &&
  (Backend.prepare (prune vc)).toBool && prepCheck (prune vc) vcp &&
  (checkAlloc vcp rf).toBool && (lowerRFunc vcp rf).toBool && (emitFunc 0 af).toBool &&
  fa.layout.toBool && savedCheck vcp rf && padsNonzeroB af fa && lastCallsOk af fa &&
  (callSites af fa).toBool && lsda.isSome && (unwindRows af fa).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt (fixed-witness convention of `DeadCleanupUnwindWitness.checks_true`); not used
by any compiler correctness theorem. -/
theorem checks_true : checks = true := by native_decide

theorem facts :
    Backend.verifiable src = true ∧ lowerScopeB gO = true ∧ hasTls gO = false ∧
    indSigs gO = [] ∧
    CompiledCleanup gO 0 vc vcp rf af fa fb ∧ lowerCheckU gO vc = true ∧
    savedCheck vcp rf = true ∧ padsNonzeroB af fa = true ∧ lastCallsOk af fa = true ∧
    callSites af fa = .ok lsda ∧ lsda.isSome = true ∧ unwindRows af fa = .ok rows := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, and_assoc] at h
  obtain ⟨hv, hs, ht, hi, hl, hlU, hp, hpc, hca, hal, hem, hla, hsv, hpad, hlast, hcs, hsome,
    hrows⟩ := h
  exact ⟨hv, hs, ht, hi, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, hlU, hsv, hpad, hlast, ok_getD hcs, hsome,
    ok_getD hrows⟩

theorem mem_externs {ext : Clif.ExtFunc} (h : ext ∈ src.externs.map (·.2)) :
    ext.name = "throw" := by
  simp only [src, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h
  subst h; rfl

theorem xe_throw : xe.extern "throw" = some fun _ m => .unwound (Clif.Rust.panicExn 77) m := by
  simp [xe, Clif.Rust.xenvWith, raises, Clif.Rust.isDivHelper]

/-- `%throw` never returns normally: the normal-return contract holds (vacuously). -/
theorem xCallsOk_xe (MR : MemRelT) (X : ExtSem) :
    XCallsOk xe.toEnv (src.externs.map (·.2)) MR X := by
  intro ext hext g _ cm _ _ _ _ vals _ _ hg _ _ _ hr
  rw [mem_externs hext, Clif.Rust.xenvWith_toEnv_raise raises 77 (by decide) (by decide)] at hg
  cases hg
  cases hr

/-- **`%throw` raises Rust's exception object 77** (`IselSimUWitness.XR`) from every world. -/
theorem xRaiseOk_xe (MR : MemRelT) (X : ExtSem) :
    XRaiseOk xe (src.externs.map (·.2)) MR X IselSimUWitness.XR := by
  intro ext hext g sl cm w d uses args vals e m hg _ _ hmr hu
  rw [mem_externs hext, xe_throw, Option.some.injEq] at hg
  subst hg
  simp only [Clif.XOutcome.unwound.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact ⟨77, w, rfl, ⟨rfl, rfl, rfl⟩, hmr⟩

/-- **`backend_correct_opt_exe_cleanup_unwind` applies to the compiled optimisation of `src`,
a function with a `try_call` whose callee raises**: the mid-end's conditions (proven rule sets,
`xenvWith_keepsSymbolsX`), the unwinding validator, every table and check premise, the raising
callees' contracts (`CalleeUnwOkG`, `XRaiseOk`, `XRaiseIndOk`), the normal-return contracts
(vacuous: `%throw` never returns), `FormsCovered`, `hTls`, `hslot` are discharged; left open as
in `LegalUnwindWitness.legal_unwind_applies`: the machine's callee contracts (`hC`, `hCT`), the
linker's symbol addresses (`hsym`) and the run's entry premises. -/
theorem opt_unwind_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K (Xr X0) H
      vcp.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) (Xr X0) H
      vcp.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn src.sig args s) (hcs : ClifEntry src args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ src cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX xe { funcs := [] } (optEntryX Opt.exeConfig src cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU (Xr X0) H Uw T fa) s
      (Clif.runLoopX xe { funcs := [] } fuel cs.toX) := by
  obtain ⟨hv, hs, ht, hi, hcc, hlU, hsv, hpad, hlast, hsites, -, hrows⟩ := facts
  have htr' : TrapsExplicitX xe (Opt.optimizeProgramExe { funcs := [] } Opt.exeConfig)
      (optEntryX Opt.exeConfig src cs) := htr
  exact backend_correct_opt_exe_cleanup_unwind Opt.exeConfig rfl rfl (p := { funcs := [] })
    (InSubset.of_verifiable hv (fun _ => rfl)) hcc hlU
    (formsCovered_cleanup_complete (lowerScope_of hs) hcc.lower hcc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide))
    (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _ _)
    (fun _ => xCallsOk_xe _ _) (fun _ => hi ▸ xCallsIndOk_nil _ _ _)
    (fun _ => xRaiseOk_xe _ _) (fun _ => hi ▸ fun _ h => nomatch h)
    hsym rfl (xenvWith_keepsSymbolsX raises 77) hsites rfl hrows rfl rfl hpad hlast hsv
    hent hres hbe hargs hcs hrel htr' fuel

/-! ## `backend_correct_opt_exe_unwind`: the pipeline without the dead cleanup -/

def vcpL : VCode := (Backend.prepare vc).toOption.getD default
def rfL : RFunc := spillAlloc vcpL
def afL : AFunc := (lowerRFunc vcpL rfL).toOption.getD default
def faL : FnAsm := (emitFunc 0 afL).toOption.getD default
def fbL : FnBin := faL.layout.toOption.getD default
def lsdaL : Option (List CallSite) := (callSites afL faL).toOption.getD none
def rowsL : List (Nat × Cfi) := (unwindRows afL faL).toOption.getD []

/-- Its tables. -/
def TL : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rowsL, lsdaL.map (List.map (·.entry))⟩

/-- **The closed receipt of the pipeline without the dead cleanup.** -/
def checksL : Bool :=
  unwCheck gO vc && (lowerFunction gO).toBool && lowerCheck gO vc &&
  (Backend.prepare vc).toBool && prepCheck vc vcpL &&
  (checkAlloc vcpL rfL).toBool && (lowerRFunc vcpL rfL).toBool && (emitFunc 0 afL).toBool &&
  faL.layout.toBool && savedCheck vcpL rfL && padsNonzeroB afL faL && lastCallsOk afL faL &&
  (callSites afL faL).toBool && lsdaL.isSome && (unwindRows afL faL).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt (the convention of `DeadCleanupUnwindWitness.checks_true`); not used by any
compiler correctness theorem. -/
theorem checksL_true : checksL = true := by native_decide

theorem factsL :
    unwCheck gO vc = true ∧ Compiled gO 0 vc vcpL rfL afL faL fbL ∧ savedCheck vcpL rfL = true ∧
    padsNonzeroB afL faL = true ∧ lastCallsOk afL faL = true ∧
    callSites afL faL = .ok lsdaL ∧ unwindRows afL faL = .ok rowsL := by
  have h := checksL_true
  simp only [checksL, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hu, hl, hlc, hp, hpc, hca, hal, hem, hla, hsv, hpad, hlast, hcs, -, hrows⟩ := h
  exact ⟨hu, ⟨ok_getD hl, hlc, ok_getD hp, hpc, ok_unit hca, ok_getD hal, ok_getD hem,
    ok_getD hla⟩, hsv, hpad, hlast, ok_getD hcs, ok_getD hrows⟩

/-- Every extern of `IselSimUWitness.env` unwinds keeping the memory. -/
theorem keeps_iselEnv : Opt.EnvKeepsSymbolsX IselSimUWitness.env := by
  intro name g hg vals m
  simp only [IselSimUWitness.env, Option.some.injEq] at hg
  subst hg
  exact ⟨fun rv m' h => (by cases h), fun e m' h => (by cases h; rfl)⟩

/-- **`backend_correct_opt_exe_unwind` applies to the optimised function compiled without the
dead cleanup**, every extern raising (`IselSimUWitness.env`); open as `opt_unwind_applies`. -/
theorem opt_unwind_applies_legacy {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcpL rfL).intBase (RAFrame.compute vcpL rfL).size afL s) K
      (Xr X0) H vcpL.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcpL rfL).intBase (RAFrame.compute vcpL rfL).size afL s)
      (Xr X0) H vcpL.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fbL base ra s) (hres : StackAvail K afL s) (hbe : BodyEntry afL s w₀)
    (hargs : ArgsIn src.sig args s) (hcs : ClifEntry src args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcpL rfL).intBase (RAFrame.compute vcpL rfL).size
      afL s, syms, afL.slotBase, (RAFrame.compute vcpL rfL).intBase⟩ src cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } (optEntryX Opt.exeConfig src cs))
    (fuel : Nat) :
    ArmRefinesU fbL base ra (Unw.ArmStepU (Xr X0) H Uw TL faL) s
      (Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX) := by
  obtain ⟨hv, hs, ht, -⟩ := facts
  obtain ⟨hunw, hc, hsv, hpad, hlast, hsites, hrows⟩ := factsL
  have htr' : TrapsExplicitX IselSimUWitness.env
      (Opt.optimizeProgramExe { funcs := [] } Opt.exeConfig) (optEntryX Opt.exeConfig src cs) := htr
  exact backend_correct_opt_exe_unwind Opt.exeConfig rfl rfl (p := { funcs := [] })
    (InSubset.of_verifiable hv (fun _ => rfl)) hc hunw
    (formsCovered_completeB hs hc.lower hc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide))
    (fun _ => xCallsOk_env _ _ _) (fun _ => xCallsIndOk_env _ _ _)
    (fun _ => IselSimUWitness.xRaiseOk _ _ _) (fun _ => IselSimUWitness.xRaiseIndOk _ _ _)
    (fun _ => IselSimUWitness.xRaiseExcl _ _ _ _)
    hsym rfl keeps_iselEnv (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _ _)
    hsites rfl hpad hlast hrows rfl rfl hsv hent hres hbe hargs hcs hrel htr' fuel

end E2E.OptUnwindWitness

/-! ## `backend_correct_legal_opt_unwind` on the compiled optimised legalisation -/

namespace E2E.LegalOptUnwindWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables
open Clif.Rust.LegalXWitness (src gL certL raises)
open E2E.DeadCleanupUnwindWitness (Xr Uw calleeUnwOkG_raise ok_getD ok_unit)

/-- The optimised legalisation of `%w(i128)`. -/
abbrev gLO : Clif.Function := Opt.optimizeExe gL Opt.exeConfig

def vc : VCode := (lowerFunction gLO).toOption.getD default
def vcp : VCode := (Backend.prepare (prune vc)).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default
def lsda : Option (List CallSite) := (callSites af fa).toOption.getD none
def rows : List (Nat × Cfi) := (unwindRows af fa).toOption.getD []

def T : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rows, lsda.map (List.map (·.entry))⟩

/-- **The closed receipt** on the compiled optimised legalisation. -/
def checks : Bool :=
  Backend.verifiable gL && lowerScopeB gLO && !hasTls gLO && (indSigs gLO).isEmpty &&
  (lowerFunction gLO).toBool && lowerCheckU gLO vc &&
  (Backend.prepare (prune vc)).toBool && prepCheck (prune vc) vcp &&
  (checkAlloc vcp rf).toBool && (lowerRFunc vcp rf).toBool && (emitFunc 0 af).toBool &&
  fa.layout.toBool && savedCheck vcp rf && padsNonzeroB af fa && lastCallsOk af fa &&
  (callSites af fa).toBool && lsda.isSome && (unwindRows af fa).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Closed receipt (the convention of `DeadCleanupUnwindWitness.checks_true`); not used by any
compiler correctness theorem. -/
theorem checks_true : checks = true := by native_decide

theorem facts :
    Backend.verifiable gL = true ∧ lowerScopeB gLO = true ∧ hasTls gLO = false ∧
    indSigs gLO = [] ∧
    CompiledCleanup gLO 0 vc vcp rf af fa fb ∧ lowerCheckU gLO vc = true ∧
    savedCheck vcp rf = true ∧ padsNonzeroB af fa = true ∧ lastCallsOk af fa = true ∧
    callSites af fa = .ok lsda ∧ lsda.isSome = true ∧ unwindRows af fa = .ok rows := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, and_assoc] at h
  obtain ⟨hv, hs, ht, hi, hl, hlU, hp, hpc, hca, hal, hem, hla, hsv, hpad, hlast, hcs, hsome,
    hrows⟩ := h
  exact ⟨hv, hs, ht, hi, ⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, hlU, hsv, hpad, hlast, ok_getD hcs, hsome,
    ok_getD hrows⟩

/-- **`backend_correct_legal_opt_unwind` applies to the compiled optimisation of the
legalisation of the `i128` function `src` with a `try_call` whose callee raises**; open as in
`LegalUnwindWitness.legal_unwind_applies`. -/
theorem legal_opt_unwind_applies {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K (Xr X0) H
      vcp.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) (Xr X0) H
      vcp.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups src.sig.params).getD []) args args')
    (hargs : ArgsIn gL.sig args' s) (hcs : ClifEntry src args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ gL cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX LegalUnwindWitness.xe { funcs := [] } cs)
    (htr : TrapsExplicitX LegalUnwindWitness.xe { funcs := [] } (optEntryX Opt.exeConfig gL cs'))
    (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups src.sig.returns).getD []) fb base ra
      (Unw.ArmStepU (Xr X0) H Uw T fa) s
      (Clif.runLoopX LegalUnwindWitness.xe { funcs := [] } fuel cs.toX) := by
  have hc : Opt.Legal.check src gL certL = true := Clif.Rust.LegalXWitness.validators.1
  have hx : Opt.Legal.exnOk src gL certL = true := Clif.Rust.LegalXWitness.validators.2
  obtain ⟨hv, hs, ht, hi, hcc, hlU, hsv, hpad, hlast, hsites, -, hrows⟩ := facts
  have htr' : TrapsExplicitX LegalUnwindWitness.xe
      (Opt.optimizeProgramExe { funcs := [] } Opt.exeConfig) (optEntryX Opt.exeConfig gL cs') := htr
  exact backend_correct_legal_opt_unwind (f := src) (g := gL) (cert := certL) hc hx
    Opt.exeConfig rfl rfl (p' := { funcs := [] })
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
    hsym rfl hsites rfl hrows rfl rfl hpad hlast hsv hent hres hbe hexp hargs hcs hcs' hsl hmem
    hrel htrS htr' fuel

end E2E.LegalOptUnwindWitness

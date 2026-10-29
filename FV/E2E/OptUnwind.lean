import FV.E2E.OptX
import FV.E2E.LegalOptX
import FV.E2E.DeadCleanupUnwindFinal
import FV.E2E.FinalUnwind
import FV.Opt.Proof.PipelineU
import FV.Opt.Proof.LegalRustX

/-!
# The end-to-end theorem with unwinding over the mid-end (S10f, #233)

`E2E.backend_correct_opt_exe_cleanup` (`FV/E2E/OptX.lean`) concludes `ArmRefines` of
`Clif.runLoop`: a callee that unwinds is outside its claim. With the mid-end's simulation
covering the handler edges of `try_call` (`Opt.optimizeExe_simU`,
`FV/Opt/Proof/PipelineU.lean`) the runs with unwinding of the optimised program refine those of
the source program (`optExe_entryX`: returns, traps and exceptions leaving the run are the
same), and the shipped compiler's per-function theorem with unwinding at the optimised function
(`backend_correct_final_cleanup_unwind`) closes the chain:

**`backend_correct_opt_exe_cleanup_unwind`**: the Arm code compiled from `Opt.optimizeExe f cfg`
(proven rule sets, `--opt-proven-only`), run on the machine with unwinding, refines the run
with unwinding of the *source* program from `f`'s entry (`ArmRefinesU`): a return is an Arm
return with the same values and memory, a trap a trap with the same code, and an exception
leaving `f` an Arm return to the caller with the exception object in x0 and the same memory.
Premises: `backend_correct_opt_exe_cleanup`'s (with the environment with unwinding, whose
externs keep the link-time symbols when they return and when they unwind,
`Opt.EnvKeepsSymbolsX`) and `backend_correct_final_cleanup_unwind`'s unwinding premises at the
optimised function. `backend_correct_opt_exe_unwind`: the same for the backend without the
dead-instruction cleanup (`Compiled`, `backend_correct_final_unwind`). The trusted Rust
environment with unwinding keeps the symbols (`xenvWith_keepsSymbolsX`).
`backend_correct_opt_exe_cleanup_unwind_any`, `backend_correct_opt_exe_unwind_any`: the same
without the check `lastCallsOk` (#622; the two above are their corollaries).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables

/-- The entry states of `f` and of its optimisation are related with unwinding. -/
theorem clifEntry_optU (cfg : Opt.Config)
    (hS : Opt.SimplifyPassSimU cfg.simplifyFn cfg.skeletonFn) {f : Clif.Function}
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    Opt.SRU cs.mem.symbols cs.toX (optEntryX cfg f cs).toX := by
  have hsim := Opt.optimizeExe_simU cfg hS f
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : optEntryX cfg f cs =
      ⟨⟨Opt.optimizeExe f cfg, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [optEntryX, hb']
  have hcx : cs.toX = ⟨cs, []⟩ := by simp [Clif.State.toX, hcs.callers]
  rw [hcx, hoe]
  refine ⟨rfl, rfl, Opt.GRU.of hR ?_, ?_⟩
  · show R cs.frame ⟨Opt.optimizeExe f cfg, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩
    have hfr : cs.frame = ⟨f, cs.frame.regs, cs.frame.slots, b.body, b.term⟩ := by
      have h1 := hcs.func
      cases hfr0 : cs.frame with
      | mk fu re sl bo te =>
        rw [hfr0] at h1 hbody hterm
        simp only at h1 hbody hterm
        rw [h1, hbody, hterm]
    rw [hfr]
    exact hrel args cs.frame.regs cs.frame.slots (hty.symm) hregs hcs.slotIds
  · show Opt.CallersRelU _ _ cs.callers [] [] []
    rw [hcs.callers]; exact .nil _

/-- **The source run with unwinding from `f`'s entry, refined by the optimised program's run
with unwinding** from the corresponding entry (`optExe_entry` with unwinding: returns, traps
and exceptions leaving the run are matched); the facts the backend theorem needs of that
entry. -/
theorem optExe_entryX (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) {p : Clif.Program} {f : Clif.Function} {env : Clif.XEnv}
    (hE : Opt.EnvKeepsSymbolsX env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) (fuel : Nat) :
    ClifEntry (Opt.optimizeExe f cfg) args (optEntryX cfg f cs) ∧
      (optEntryX cfg f cs).frame.slots = cs.frame.slots ∧ (optEntryX cfg f cs).mem = cs.mem ∧
      ∃ n', Opt.XOutcomeRefines (Clif.runLoopX env p fuel cs.toX)
        (Clif.runLoopX env (Opt.optimizeProgramExe p cfg) n' (optEntryX cfg f cs).toX) := by
  have hS := Opt.simplifyPassSimU_proven hr ha
  obtain ⟨hcs', hsl, hmem, -⟩ :=
    optExe_entry cfg hr ha (p := p) (env := env.toEnv) hE.toEnv hcs fuel
  exact ⟨hcs', hsl, hmem,
    Opt.optimizeProgramExe_refinesU cfg hS hE p fuel _ _ (clifEntry_optU cfg hS hcs)⟩

theorem armRefinesU_of_outcome {fb : FnBin} {base ra : BitVec 64}
    {step : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {o o' : Clif.XOutcome}
    (h : Opt.XOutcomeRefines o o') (hA : ArmRefinesU fb base ra step s o') :
    ArmRefinesU fb base ra step s o := by
  obtain ⟨hret, htrap, hunw⟩ := h
  cases hrn : o with
  | returned vals m => rw [hret vals m hrn] at hA; exact hA
  | trapped c => rw [htrap c hrn] at hA; exact hA
  | unwound e m => rw [hunw e m hrn] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **`backend_correct_opt_exe_cleanup_unwind` without the check on the calls of the last block**
(#622; `backend_correct_final_cleanup_unwind_any`). Non-vacuity: `OptUnwindWitness` (its premises
are among `backend_correct_opt_exe_cleanup_unwind`'s). -/
theorem backend_correct_opt_exe_cleanup_unwind_any (cfg : Opt.Config)
    (hr : cfg.rules = .cranelift) (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : CompiledCleanup (Opt.optimizeExe f cfg) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (Opt.optimizeExe f cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe f cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbolsX env)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env (Opt.optimizeProgramExe p cfg) (optEntryX cfg f cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) := by
  have hF := optimizeExe_shape cfg f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := optExe_entryX cfg hr ha hE hcs fuel (p := p)
  exact armRefinesU_of_outcome hn (backend_correct_final_cleanup_unwind_any
    (inSubset_optExe cfg hsub) hc hlU hcov hC hCT hTls hU
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXR s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXRi s')
    hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_opt_exe_unwind` without the check on the calls of the last block** (#622;
`backend_correct_final_unwind_any`). Non-vacuity: `OptUnwindWitness` (its premises are among
`backend_correct_opt_exe_unwind`'s). -/
theorem backend_correct_opt_exe_unwind_any (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : Compiled (Opt.optimizeExe f cfg) k vc vcp rf af fa fb)
    (hunw : unwCheck (Opt.optimizeExe f cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe f cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : ∀ s, XRaiseExcl env (f.externs.map (·.2)) (indSigs (Opt.optimizeExe f cfg))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbolsX env)
    (hUnw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env (Opt.optimizeProgramExe p cfg) (optEntryX cfg f cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) := by
  have hF := optimizeExe_shape cfg f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := optExe_entryX cfg hr ha hE hcs fuel (p := p)
  exact armRefinesU_of_outcome hn (backend_correct_final_unwind_any (inSubset_optExe cfg hsub)
    hc hunw hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXR s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXRi s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXE s')
    hsym hslot hUnw hsites hlsda hpad hrows hcie hfde hsaved hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **End-to-end theorem with unwinding over the mid-end of the executable compiler**
(`--opt-proven-only`, `lean-backend`'s default backend). For an in-subset function `f` of `p`
whose optimisation `Opt.optimizeExe f cfg` (proven rule sets) the shipped compiler compiles
through the dead cleanup (`CompiledCleanup`) with a lowering that passes the unwinding
validator (`lowerCheckU`), the Arm run with unwinding of the compiled optimised function refines
the CLIF run with unwinding of the *source* program `p` from `f`'s entry state: returns and
traps as in `backend_correct_opt_exe_cleanup`, and an exception leaving `f` (`unwound e m`) is an
Arm return to the caller with the exception object in x0 and the same memory. Premises:
`backend_correct_opt_exe_cleanup`'s (externs keep the link-time symbols when they return and
when they unwind, `hE`), and `backend_correct_final_cleanup_unwind`'s unwinding premises at the
optimised function (the raising callees' contracts `hU`, `hXR`, `hXRi`, the emitted call-site
table and frame rows, the checks `padsNonzeroB`, `lastCallsOk`, `savedCheck`); the optimised
program's run with unwinding traps only explicitly (`htr`). Statement kept for its callers;
`backend_correct_opt_exe_cleanup_unwind_any` drops `lastCallsOk`. -/
theorem backend_correct_opt_exe_cleanup_unwind (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : CompiledCleanup (Opt.optimizeExe f cfg) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (Opt.optimizeExe f cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe f cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbolsX env)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true) (_hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env (Opt.optimizeProgramExe p cfg) (optEntryX cfg f cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_opt_exe_cleanup_unwind_any cfg hr ha hsub hc hlU hcov hC hCT hTls hU hX hXI hXR
    hXRi hsym hslot hE hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe hargs hcs hrel htr fuel

/-- **`backend_correct_opt_exe_cleanup_unwind` for the backend without the dead-instruction
cleanup** (`Compiled`, `backend_correct_final_unwind`; statement kept for its callers,
`backend_correct_opt_exe_unwind_any` drops `lastCallsOk`). -/
theorem backend_correct_opt_exe_unwind (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : Compiled (Opt.optimizeExe f cfg) k vc vcp rf af fa fb)
    (hunw : unwCheck (Opt.optimizeExe f cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe f cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : ∀ s, XRaiseExcl env (f.externs.map (·.2)) (indSigs (Opt.optimizeExe f cfg))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbolsX env)
    (hUnw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (_hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env (Opt.optimizeProgramExe p cfg) (optEntryX cfg f cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_opt_exe_unwind_any cfg hr ha hsub hc hunw hcov hC hCT hTls hX hXI hXR hXRi hXE
    hsym hslot hE hUnw hsites hlsda hpad hrows hcie hfde hsaved hent hres hbe hargs hcs hrel htr fuel

/-! ## The trusted Rust environment with unwinding keeps the symbols -/

theorem toX_returned {o : Clif.Outcome} {v : List Clif.Val} {m : Clif.Mem}
    (h : o.toX = .returned v m) : o = .returned v m := by
  cases o <;> simp_all [Clif.Outcome.toX]

/-- **The trusted Rust environment with unwinding keeps the link-time symbols** when an extern
returns (`RustSyms.envKeepsSymbols_env`) and when it unwinds (the memory is the caller's). -/
theorem xenvWith_keepsSymbolsX (raises : String → Bool) (obj : BitVec 64) :
    Opt.EnvKeepsSymbolsX (Clif.Rust.xenvWith raises obj) := by
  have hk := RustSyms.envKeepsSymbols_env
  intro name g hg vals m
  simp only [Clif.Rust.xenvWith] at hg
  by_cases hd : Clif.Rust.isDivHelper name = true
  · rw [ite_eq_left hd] at hg
    cases hg
    have he : Clif.Rust.env.extern name = some fun vals m => Clif.Rust.divOutcome name vals m := by
      simp only [Clif.Rust.env]; rw [ite_eq_left hd]
    exact ⟨fun rv m' h => hk name _ he vals m rv m' (toX_returned h),
      fun e m' h => absurd h (Clif.Outcome.toX_ne_unwound _ e m')⟩
  · rw [ite_eq_right hd] at hg
    by_cases hr : raises name = true
    · rw [ite_eq_left hr] at hg
      cases hg
      exact ⟨fun rv m' h => (by cases h), fun e m' h => (by cases h; rfl)⟩
    · rw [ite_eq_right hr] at hg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hg
      exact ⟨fun rv m' h => hk name g0 hg0 vals m rv m' (toX_returned h),
        fun e m' h => absurd h (Clif.Outcome.toX_ne_unwound _ e m')⟩

end E2E

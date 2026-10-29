import FV.E2E.LegalUnwind
import FV.E2E.OptUnwind

/-!
# The end-to-end theorem with unwinding for `i128` functions legalised then optimised (S10f, #233)

`lean-backend --opt` compiles an `i128` function `f` as `Opt.optimizeExe g cfg`, where `g` is its
legalisation. **`backend_correct_legal_opt_unwind_env`** composes the three refinements with
unwinding: the run of `f` (in `p`) is refined by the run of `g` (in `p'`) with ABI-split
arguments and results (`Opt.Legal.X.check_refinesX`, `Opt.Legal.exnOk` accepting the handler
edges), which is refined by the run of the optimised `g` in the optimised program
(`optExe_entryX`), which the Arm code compiled from it refines on the machine with unwinding
(`backend_correct_final_cleanup_unwind`). The conclusion is `ArmRefinesLegalU` (as
`backend_correct_legal_unwind`'s). `backend_correct_legal_opt_unwind`: under the trusted Rust
environment with unwinding `Clif.Rust.xenvWith raises obj` (its contracts proven). The `_any`
variants drop the check `lastCallsOk` (#622); the theorems without the suffix are their
corollaries.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables

/-- **End-to-end theorem with unwinding for a legalised then optimised function, any
environment with the contracts of `check_refinesX` and `optExe_entryX`**, without the check on
the calls of the last block (#622). Non-vacuity: `OptUnwindWitness` (through
`backend_correct_legal_opt_unwind`, whose premises include its own). -/
theorem backend_correct_legal_opt_unwind_env_any {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    (cfg : Opt.Config) (hr : cfg.rules = .cranelift) (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (Opt.optimizeExe g cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hE : Opt.Legal.X.EnvOkX env ⟨f, g, cert⟩ p p') (hEs : Opt.EnvKeepsSymbolsX env)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX env p cs)
    (htr : TrapsExplicitX env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hF := optimizeExe_shape cfg g
  -- the optimised legalisation's Arm code refines every run with unwinding of `g`
  have hB : ∀ n, ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s
      (Clif.runLoopX env p' n cs'.toX) := by
    intro n
    obtain ⟨hcs'', hsl', hmem', n', hn⟩ := optExe_entryX cfg hr ha hEs hcs' n (p := p')
    exact armRefinesU_of_outcome hn (backend_correct_final_cleanup_unwind_any
      (inSubset_optExe cfg hsub)
      hc hlU hcov hC hCT hTls hU
      (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
      (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s')
      (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXR s')
      (fun s' => by rw [rel_holds_slots hF.slots]; exact hXRi s')
      hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe
      (by rw [hF.sig]; exact hargs) hcs''
      (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n')
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  have hT := noMemTrapX_of_trapsExplicitX htrS hcs.callers
  have hI := noIndInternalX_of_trapsExplicitX htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2, hr3⟩ := Opt.Legal.X.check_refinesX (C := C) hchk hexn hE hb hb' hcs.func h2 h3
    h4 h5 hcs'.func h2' h3' h5' hsl hexp hM hT hI fuel
  have hst : cs.toX = ⟨⟨cs.frame, [], cs.mem⟩, []⟩ := by
    simp only [Clif.State.toX, hcs.callers, List.map_nil]
    rw [← hcs.callers]
  have hst' : cs'.toX = ⟨⟨cs'.frame, [], cs.mem⟩, []⟩ := by
    simp only [Clif.State.toX, hcs'.callers, List.map_nil]
    rw [← hmem, ← hcs'.callers]
  rw [← hst] at hr1 hr2 hr3
  rw [← hst'] at hr1 hr2 hr3
  cases hrun : Clif.runLoopX env p fuel cs.toX with
  | returned vals m1 =>
    obtain ⟨vals', hv, k, hk⟩ := hr1 vals m1 hrun
    have := hB k
    rw [hk] at this
    exact ⟨vals', hv, this⟩
  | trapped c =>
    obtain ⟨k, hk⟩ := hr2 c hrun
    have := hB k
    rw [hk] at this
    exact this
  | unwound e m1 =>
    obtain ⟨k, hk⟩ := hr3 e m1 hrun
    have := hB k
    rw [hk] at this
    exact this
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **The end-to-end theorem with unwinding for `i128` functions legalised then optimised**
(`--opt-proven-only`): for a function `f` whose legalisation `g` the validators accept
(`Opt.Legal.check`, `Opt.Legal.exnOk`) and whose optimised legalisation `Opt.optimizeExe g cfg`
the shipped compiler compiles (`CompiledCleanup`, `lowerCheckU`), the Arm code, entered with the
ABI-split arguments and run on the machine with unwinding, refines the run with unwinding of the
original `f` under the trusted Rust environment with unwinding `Clif.Rust.xenvWith raises obj`
(contracts proven: `Clif.Rust.xenvWith_envOkX`, `xenvWith_keepsSymbolsX`), without the check on
the calls of the last block (#622). Non-vacuity: `OptUnwindWitness` (through
`backend_correct_legal_opt_unwind`). -/
theorem backend_correct_legal_opt_unwind_any {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    (cfg : Opt.Config) (hr : cfg.rules = .cranelift) (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (Opt.optimizeExe g cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {K : Nat} (raises : String → Bool)
    (obj : BitVec 64)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk (Clif.Rust.xenvWith raises obj).toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk (Clif.Rust.xenvWith raises obj).toEnv (indSigs (Opt.optimizeExe g cfg))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.Rust.xenvWith raises obj) (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk (Clif.Rust.xenvWith raises obj) (indSigs (Opt.optimizeExe g cfg))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX (Clif.Rust.xenvWith raises obj) p cs)
    (htr : TrapsExplicitX (Clif.Rust.xenvWith raises obj) (Opt.optimizeProgramExe p' cfg)
      (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U T fa) s (Clif.runLoopX (Clif.Rust.xenvWith raises obj) p fuel cs.toX) :=
  backend_correct_legal_opt_unwind_env_any hchk hexn cfg hr ha hsub hc hlU
    (Clif.Rust.xenvWith_envOkX raises obj (C := ⟨f, g, cert⟩) (Opt.Legal.indOldB_of_check hchk)
      hext hext' hind)
    (xenvWith_keepsSymbolsX raises obj) hcov hC hCT hTls hU hX hXI hXR hXRi hsym hslot hsites hlsda
    hrows hcie hfde hpad hsaved hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **End-to-end theorem with unwinding for a legalised then optimised function, any
environment with the contracts of `check_refinesX` and `optExe_entryX`** (statement kept for its
callers; `backend_correct_legal_opt_unwind_env_any` drops `lastCallsOk`). -/
theorem backend_correct_legal_opt_unwind_env {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    (cfg : Opt.Config) (hr : cfg.rules = .cranelift) (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (Opt.optimizeExe g cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hE : Opt.Legal.X.EnvOkX env ⟨f, g, cert⟩ p p') (hEs : Opt.EnvKeepsSymbolsX env)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true) (_hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX env p cs)
    (htr : TrapsExplicitX env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_legal_opt_unwind_env_any hchk hexn cfg hr ha hsub hc hlU hE hEs hcov hC hCT hTls
    hU hX hXI hXR hXRi hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe hexp hargs
    hcs hcs' hsl hmem hrel htrS htr fuel

/-- **The end-to-end theorem with unwinding for `i128` functions legalised then optimised**
(`--opt-proven-only`; statement kept for its callers, `backend_correct_legal_opt_unwind_any`
drops `lastCallsOk`). -/
theorem backend_correct_legal_opt_unwind {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    (cfg : Opt.Config) (hr : cfg.rules = .cranelift) (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (Opt.optimizeExe g cfg) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {K : Nat} (raises : String → Bool)
    (obj : BitVec 64)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk (Clif.Rust.xenvWith raises obj).toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk (Clif.Rust.xenvWith raises obj).toEnv (indSigs (Opt.optimizeExe g cfg))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.Rust.xenvWith raises obj) (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk (Clif.Rust.xenvWith raises obj) (indSigs (Opt.optimizeExe g cfg))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true) (_hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX (Clif.Rust.xenvWith raises obj) p cs)
    (htr : TrapsExplicitX (Clif.Rust.xenvWith raises obj) (Opt.optimizeProgramExe p' cfg)
      (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U T fa) s (Clif.runLoopX (Clif.Rust.xenvWith raises obj) p fuel cs.toX) :=
  backend_correct_legal_opt_unwind_any hchk hexn cfg hr ha hsub hc hlU raises obj hext hext' hind
    hcov hC hCT hTls hU hX hXI hXR hXRi hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent
    hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

end E2E

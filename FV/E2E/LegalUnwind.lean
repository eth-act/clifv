import FV.E2E.DeadCleanupUnwindFinal
import FV.E2E.Legal
import FV.Opt.Proof.LegalRustX

/-!
# The end-to-end theorem with unwinding for `i128` functions (S10e, #232)

An `i128` function `f` is compiled as its legalisation `g` (`Opt.Legalize128`), accepted by
`Opt.Legal.check` and by the handler-edge check `Opt.Legal.exnOk`.
**`backend_correct_legal_unwind`** composes the refinement theorem with unwinding
`Opt.Legal.X.check_refinesX` (`FV/Opt/Proof/LegalSimX.lean`) with the shipped compiler's
per-function theorem with unwinding `backend_correct_final_cleanup_unwind` at `g`: the Arm code
compiled from `g`, entered with the ABI-split arguments and run on the machine with unwinding,
refines the run with unwinding of the ORIGINAL function `f` (`ArmRefinesLegalU`): a return of
`f` is an Arm return of the results split by the ABI groups with the same memory, a trap the
same trap, and an exception leaving `f` (`unwound e m`) an Arm return to the caller with the
exception object in x0 (`ExnRel`) and the same memory.

Discharged premises: the source run's `NoMemTrapX`/`NoIndInternalX` (from its
`TrapsExplicitX`) and `MemBounded` (from the backend relation). The environment's contracts
(`Opt.Legal.X.EnvOkX`) are premises of `backend_correct_legal_unwind_env`; for the trusted Rust
environment with unwinding `Clif.Rust.xenvWith` (`FV/Opt/Proof/LegalRustX.lean`) they are
proven (`backend_correct_legal_unwind`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables

/-- What the Arm run with unwinding does for an outcome with unwinding of the original
function `f` whose results are expanded by the ABI groups `rg`: a return with values `vals` is
an Arm return with the expanded values; traps and exceptions as `ArmRefinesU`. -/
def ArmRefinesLegalU (rg : List (List Opt.Legalize128.SlotEl)) (fb : FnBin) (base ra : BitVec 64)
    (astep : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) : Clif.XOutcome → Prop
  | .returned vals cm => ∃ vals', Opt.Legal.ExpRel rg vals vals' ∧
      ArmRefinesU fb base ra astep s (.returned vals' cm)
  | o => ArmRefinesU fb base ra astep s o

theorem sreachX_reachX {env : Clif.XEnv} {p : Clif.Program} {xs xs' : Clif.XState}
    (h : Opt.Legal.X.SReachX env p xs xs') : ReachX env p xs xs' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih

/-- A run with unwinding whose traps are all explicit has no load/store trap. -/
theorem noMemTrapX_of_trapsExplicitX {env : Clif.XEnv} {p : Clif.Program} {cs : Clif.State}
    (h : TrapsExplicitX env p cs) (hcl : cs.callers = []) :
    Opt.Legal.X.NoMemTrapX env p ⟨cs.frame, [], cs.mem⟩ := by
  have hcs : (⟨⟨cs.frame, [], cs.mem⟩, []⟩ : Clif.XState) = cs.toX := by
    simp [Clif.State.toX, hcl]; rw [← hcl]
  intro xs hr c st rest hst hb
  rw [hcs] at hr
  have he := h.stmt xs c st rest (sreachX_reachX hr) hst hb
  refine ⟨fun op t fl a o hi => ?_, fun op t fl x a o hi => ?_⟩ <;>
    (rw [hi] at he; cases he)

/-- A run with unwinding whose indirect calls reach no function of the program satisfies
`NoIndInternalX`. -/
theorem noIndInternalX_of_trapsExplicitX {env : Clif.XEnv} {p : Clif.Program} {cs : Clif.State}
    (h : TrapsExplicitX env p cs) (hcl : cs.callers = []) :
    Opt.Legal.X.NoIndInternalX env p cs.frame.func ⟨cs.frame, [], cs.mem⟩ := by
  have hcs : (⟨⟨cs.frame, [], cs.mem⟩, []⟩ : Clif.XState) = cs.toX := by
    simp [Clif.State.toX, hcl]; rw [← hcl]
  intro xs hr
  rw [hcs] at hr
  exact ⟨fun st rest sig callee args cv hb hi hB hc =>
    h.indirect xs st rest sig callee args (sreachX_reachX hr) hb hi hB cv hc,
    fun callee args et cv hb ht hB hc =>
    h.tryIndirect xs callee args et (sreachX_reachX hr) hb ht hB cv hc⟩

/-- **End-to-end theorem with unwinding for a legalised function, any environment with the
contracts of `check_refinesX`.** -/
theorem backend_correct_legal_unwind_env {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup g k vc vcp rf af fa fb)
    (hlU : lowerCheckU g vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    -- the environment's contracts (`FV/Opt/Proof/LegalSimX.lean`) and the programs' conditions
    (hE : Opt.Legal.X.EnvOkX env ⟨f, g, cert⟩ p p')
    -- `backend_correct_final_cleanup_unwind`'s premises about `g`
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    -- the run: `f` on `args`, `g` on the ABI-split `args'` (same slots and memory)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX env p cs) (htr : TrapsExplicitX env p' cs') (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
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
  have hB := fun k => backend_correct_final_cleanup_unwind hsub hc hlU hcov hC hCT hTls hU hX hXI
    hXR hXRi hsym hslot hsites hlsda hrows hcie hfde hpad hlast hsaved hent hres hbe hargs hcs'
    hrel htr k
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

/-- **The end-to-end theorem with unwinding for `i128` functions**: for a function `f` whose
legalisation `g` the validators accept (`Opt.Legal.check`, `Opt.Legal.exnOk`) and which the
shipped compiler compiles inside `InSubset` (`CompiledCleanup`, `lowerCheckU`), the Arm code of
`g`, entered with the ABI-split arguments and run on the machine with unwinding, refines the run
with unwinding of the original `f` under the trusted Rust environment with unwinding
`Clif.Rust.xenvWith raises` (an extern `raises` classifies raises Rust's exception; for
`panic=unwind`, `raises = isPanic`: `Clif.Rust.xenv`; its contracts proven,
`Clif.Rust.xenvWith_envOkX`): returns are returns of the expanded results with the same memory,
traps are traps with the same code, and an exception leaving `f` is an Arm return to the
caller with the exception object in x0 and the same memory. -/
theorem backend_correct_legal_unwind {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup g k vc vcp rf af fa fb)
    (hlU : lowerCheckU g vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {K : Nat} (raises : String → Bool) (obj : BitVec 64)
    -- calls of `f` and `g` go to the environment
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    -- an indirect call of `f` resolves to the same extern in both programs
    (hind : (∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    -- `backend_correct_final_cleanup_unwind`'s premises about `g`
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk (Clif.Rust.xenvWith raises obj).toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk (Clif.Rust.xenvWith raises obj).toEnv (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.Rust.xenvWith raises obj) (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk (Clif.Rust.xenvWith raises obj) (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    -- the run: `f` on `args`, `g` on the ABI-split `args'` (same slots and memory)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX (Clif.Rust.xenvWith raises obj) p cs) (htr : TrapsExplicitX (Clif.Rust.xenvWith raises obj) p' cs') (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U T fa) s (Clif.runLoopX (Clif.Rust.xenvWith raises obj) p fuel cs.toX) :=
  backend_correct_legal_unwind_env hchk hexn hsub hc hlU
    (Clif.Rust.xenvWith_envOkX raises obj (C := ⟨f, g, cert⟩) (Opt.Legal.indOldB_of_check hchk)
      hext hext' hind) hcov hC hCT hTls hU hX hXI hXR
    hXRi hsym hslot hsites hlsda hrows hcie hfde hpad hlast hsaved hent hres hbe hexp hargs hcs hcs'
    hsl hmem hrel htrS htr fuel

end E2E

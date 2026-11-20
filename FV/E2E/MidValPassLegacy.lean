import FV.E2E.MidValPass
import FV.E2E.RetypeLegal
import FV.E2E.DeadCleanupPairTC

/-! # The legacy, unwinding and typed theorems through the mid-end validator (#1119)

`FV/E2E/MidValPass.lean` for the other paths `lean-backend` names a theorem on (a file with a
`try_call`: the legacy path with dead cleanup; the unwinding theorems; the typed scope). Each
theorem has the artifact hypothesis of the theorem `lean-backend` names for the compiled `g` (or its
`i128` legalisation `g'`, or `T g`/`T g'` for constant-phi removal at `T := Opt.ConstPhi.run`), the
decided premise `Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true`, the program `q` of
validated functions (`Opt.MidVal.ValidatedC p.funcs q.funcs`), and that theorem's conclusion about
the run of the program `p` with cg_clif's source function `f` from `f`'s entry state:

* legacy, dead cleanup: `backend_correct_midval_final_cleanup`, `backend_correct_midval_pass_cleanup`,
  `backend_correct_midval_legal_wide_cleanup`, `backend_correct_midval_legal_pass_wide_cleanup`;
* unwinding: `backend_correct_midval_final_cleanup_unwind_any`,
  `backend_correct_midval_pass_cleanup_unwind_any`, `backend_correct_midval_legal_unwind_any`,
  `backend_correct_midval_legal_pass_unwind_any`;
* typed (no legalisation or constant-phi change of `g`; `lean-backend` names no composed typed
  theorem when those changed a function, so neither is composed here):
  `backend_correct_midval_final_cleanupT`, `backend_correct_midval_world_cleanupTC`,
  `backend_correct_midval_world_cleanupTCF`.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables
set_option autoImplicit false

theorem armRefinesLegalU_of_outcome {rg : List (List Opt.Legalize128.SlotEl)} {fb : FnBin}
    {base ra : BitVec 64} {step : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    {o o' : Clif.XOutcome} (h : Opt.XOutcomeRefines o o')
    (hA : ArmRefinesLegalU rg fb base ra step s o') : ArmRefinesLegalU rg fb base ra step s o := by
  obtain ⟨hret, htrap, hunw⟩ := h
  cases hrn : o with
  | returned vals m => rw [hret vals m hrn] at hA; exact hA
  | trapped c => rw [htrap c hrn] at hA; exact hA
  | unwound e m => rw [hunw e m hrn] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

/-! ## Legacy path, dead cleanup -/

/-- **`backend_correct_final_cleanup` through the mid-end validator**: `g` compiled
(`CompiledCleanup`); the Arm run of the compiled `g` refines the CLIF run of the *source* program
`p` from `f`'s entry. -/
theorem backend_correct_midval_final_cleanup {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset q g)
    (hc : CompiledCleanup g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env q (midEntry g cs)) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entry hchk hv hE hcs fuel
  exact armRefines_of_outcome hn (backend_correct_final_cleanup hsub hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_pass_cleanup` through the mid-end validator** (`lean-backend` names it at
`T := Opt.ConstPhi.run`): `T g` compiled. -/
theorem backend_correct_midval_pass_cleanup {T : Clif.Function → Clif.Function}
    (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset q g)
    (hc : CompiledCleanup (T g) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (T g)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (passProg T q) (passEntry T g (midEntry g cs))) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entry hchk hv hE hcs fuel
  exact armRefines_of_outcome hn (backend_correct_pass_cleanup hT hS hsub hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hE hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_legal_wide_cleanup` through the mid-end validator** (under
`Clif.Rust.env`): `g` legalised to `g'` (`Opt.Legal.checkW g g' certL`), `g'` compiled. -/
theorem backend_correct_midval_legal_wide_cleanup {f g g' : Clif.Function}
    {cert : Opt.MidVal.Cert} {certL : Opt.Legalize128.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q p' : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    (hchkL : Opt.Legal.checkW g g' certL = true)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g')
    (hc : CompiledCleanup g' k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, g.extern? fn = some e → q.func? e.name = none)
    (hext' : ∀ fn e, g'.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite g sig) →
      p'.funcs.map (·.name) = q.funcs.map (·.name) ∧ q.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g'.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g' = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g'.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs g') (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g'.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g' args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env q (midEntry g cs)) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs1, hsl1, hmem1, n', hn⟩ := midval_entry hchk hv RustSyms.envKeepsSymbols_env hcs fuel
  have key := backend_correct_legal_wide_cleanup hchkL hsub hc hext hext' hind hcov hC hCT hTls hX
    hXI hsym hslot hent hres hbe (by rw [hF.sig]; exact hexp) hargs hcs1 hcs'
    (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hrel htrS htr n'
  rw [hF.sig] at key
  exact armRefinesLegal_of_outcome hn key

/-- **`backend_correct_legal_pass_wide_cleanup` through the mid-end validator** (under
`Clif.Rust.env`; `lean-backend` names it at `T := Opt.ConstPhi.run`): `g` legalised to `g'`,
`T g'` compiled. -/
theorem backend_correct_midval_legal_pass_wide_cleanup {T : Clif.Function → Clif.Function}
    (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {f g g' : Clif.Function} {cert : Opt.MidVal.Cert} {certL : Opt.Legalize128.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q p' : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    (hchkL : Opt.Legal.checkW g g' certL = true)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g')
    (hc : CompiledCleanup (T g') k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, g.extern? fn = some e → q.func? e.name = none)
    (hext' : ∀ fn e, g'.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite g sig) →
      p'.funcs.map (·.name) = q.funcs.map (·.name) ∧ q.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g').blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g') = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g'.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs (T g')) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g'.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g' args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env q (midEntry g cs))
    (htr : TrapsExplicit Clif.Rust.env (passProg T p') (passEntry T g' cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs1, hsl1, hmem1, n', hn⟩ := midval_entry hchk hv RustSyms.envKeepsSymbols_env hcs fuel
  have key := backend_correct_legal_pass_wide_cleanup hchkL hT hS hsub hc hext hext' hind hcov hC
    hCT hTls hX hXI hsym hslot hent hres hbe (by rw [hF.sig]; exact hexp) hargs hcs1 hcs'
    (hsl.trans hsl1.symm) (hmem.trans hmem1.symm) hrel htrS htr n'
  rw [hF.sig] at key
  exact armRefinesLegal_of_outcome hn key

/-! ## Unwinding -/

/-- **`backend_correct_final_cleanup_unwind_any` through the mid-end validator**: the Arm code
compiled from `g` through the dead cleanup, run on the machine with unwinding, refines the run with
unwinding of the *source* program `p` from `f`'s entry (`ArmRefinesU`). -/
theorem backend_correct_midval_final_cleanup_unwind_any {f g : Clif.Function}
    {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset q g)
    (hc : CompiledCleanup g k vc vcp rf af fa fb)
    (hlU : lowerCheckU g vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {Tb : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hUw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbolsX env)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : Tb.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : Tb.cie = cieInsns)
    (hfde : Tb.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env q (midEntry g cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U Tb fa) s (Clif.runLoopX env p fuel cs.toX) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entryX hchk hv hE hcs fuel
  exact armRefinesU_of_outcome hn (backend_correct_final_cleanup_unwind_any
    hsub hc hlU hcov hC hCT hTls hUw
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXR s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXRi s')
    hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_pass_cleanup_unwind_any` through the mid-end validator** (`lean-backend`
names it at `T := Opt.ConstPhi.run`): `T g` compiled. -/
theorem backend_correct_midval_pass_cleanup_unwind_any {T : Clif.Function → Clif.Function}
    (hU : ∀ f, Opt.FunSimU f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset q g)
    (hc : CompiledCleanup (T g) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (T g) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {Tb : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hUw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (T g)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (T g)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbolsX env)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : Tb.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : Tb.cie = cieInsns)
    (hfde : Tb.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env (passProg T q) (passEntry T g (midEntry g cs))) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U Tb fa) s (Clif.runLoopX env p fuel cs.toX) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entryX hchk hv hE hcs fuel
  exact armRefinesU_of_outcome hn (backend_correct_pass_cleanup_unwind_any hU hS hsub hc hlU hcov
    hC hCT hTls hUw
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXR s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXRi s')
    hsym hslot hE hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_legal_unwind_any` through the mid-end validator** (the trusted Rust
environment with unwinding `Clif.Rust.xenvWith raises obj`): `g` legalised to `g'` (`Opt.Legal.check`
and `Opt.Legal.exnOk` accept), `g'` compiled. -/
theorem backend_correct_midval_legal_unwind_any {f g g' : Clif.Function}
    {cert : Opt.MidVal.Cert} {certL : Opt.Legalize128.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q p' : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    (hchkL : Opt.Legal.check g g' certL = true) (hexn : Opt.Legal.exnOk g g' certL = true)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g') (hc : CompiledCleanup g' k vc vcp rf af fa fb)
    (hlU : lowerCheckU g' vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {K : Nat} (raises : String → Bool) (obj : BitVec 64)
    (hext : ∀ fn e, g.extern? fn = some e → q.func? e.name = none)
    (hext' : ∀ fn e, g'.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ g.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = q.funcs.map (·.name) ∧ q.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g'.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g' = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk (Clif.Rust.xenvWith raises obj).toEnv (g'.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hXI : ∀ s, XCallsIndOk (Clif.Rust.xenvWith raises obj).toEnv (indSigs g') (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.Rust.xenvWith raises obj) (g'.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk (Clif.Rust.xenvWith raises obj) (indSigs g') (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X XR)
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
    (hargs : ArgsIn g'.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g' args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX (Clif.Rust.xenvWith raises obj) q (midEntry g cs))
    (htr : TrapsExplicitX (Clif.Rust.xenvWith raises obj) p' cs') (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U T fa) s (Clif.runLoopX (Clif.Rust.xenvWith raises obj) p fuel cs.toX) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs1, hsl1, hmem1, n', hn⟩ :=
    midval_entryX hchk hv (xenvWith_keepsSymbolsX raises obj) hcs fuel
  have key := backend_correct_legal_unwind_any hchkL hexn hsub hc hlU raises obj hext hext' hind
    hcov hC hCT hTls hU hX hXI hXR hXRi hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent
    hres hbe (by rw [hF.sig]; exact hexp) hargs hcs1 hcs' (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hrel htrS htr n'
  rw [hF.sig] at key
  exact armRefinesLegalU_of_outcome hn key

/-- **`backend_correct_legal_pass_unwind_any` through the mid-end validator** (`lean-backend` names
it at `T := Opt.ConstPhi.run`): `g` legalised to `g'`, `T g'` compiled. -/
theorem backend_correct_midval_legal_pass_unwind_any {T : Clif.Function → Clif.Function}
    (hUs : ∀ f, Opt.FunSimU f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {f g g' : Clif.Function} {cert : Opt.MidVal.Cert} {certL : Opt.Legalize128.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q p' : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    (hchkL : Opt.Legal.check g g' certL = true) (hexn : Opt.Legal.exnOk g g' certL = true)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g') (hc : CompiledCleanup (T g') k vc vcp rf af fa fb)
    (hlU : lowerCheckU (T g') vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {Tb : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {K : Nat} (raises : String → Bool)
    (obj : BitVec 64)
    (hext : ∀ fn e, g.extern? fn = some e → q.func? e.name = none)
    (hext' : ∀ fn e, g'.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ g.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = q.funcs.map (·.name) ∧ q.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g').blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g') = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk (Clif.Rust.xenvWith raises obj).toEnv (g'.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hXI : ∀ s, XCallsIndOk (Clif.Rust.xenvWith raises obj).toEnv (indSigs (T g'))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.Rust.xenvWith raises obj) (g'.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk (Clif.Rust.xenvWith raises obj) (indSigs (T g'))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : Tb.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : Tb.cie = cieInsns)
    (hfde : Tb.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g'.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g' args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX (Clif.Rust.xenvWith raises obj) q (midEntry g cs))
    (htr : TrapsExplicitX (Clif.Rust.xenvWith raises obj) (passProg T p') (passEntry T g' cs'))
    (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U Tb fa) s (Clif.runLoopX (Clif.Rust.xenvWith raises obj) p fuel cs.toX) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs1, hsl1, hmem1, n', hn⟩ :=
    midval_entryX hchk hv (xenvWith_keepsSymbolsX raises obj) hcs fuel
  have key := backend_correct_legal_pass_unwind_any hchkL hexn hUs hS hsub hc hlU raises obj hext
    hext' hind hcov hC hCT hTls hU hX hXI hXR hXRi hsym hslot hsites hlsda hrows hcie hfde hpad
    hsaved hent hres hbe (by rw [hF.sig]; exact hexp) hargs hcs1 hcs' (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hrel htrS htr n'
  rw [hF.sig] at key
  exact armRefinesLegalU_of_outcome hn key

/-! ## The typed scope -/

/-- **`backend_correct_final_cleanupT` through the mid-end validator**: `g` in the typed scope
compiled (`CompiledCleanupT`); returned values by class (`ArmRefinesT`). -/
theorem backend_correct_midval_final_cleanupT {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT q g) (hc : CompiledCleanupT g k vc vcp rf af fa fb) (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env q (midEntry g cs)) (fuel : Nat) :
    ArmRefinesT fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entry hchk hv hE hcs fuel
  exact armRefinesT_of_outcome hn (backend_correct_final_cleanupT hsub hc hT hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_world_cleanupTCF` through the mid-end validator**: `g` in the typed scope
with the proven float operations compiled (`CompiledCleanupTCF`). -/
theorem backend_correct_midval_world_cleanupTCF {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTCF q g)
    (hc : CompiledCleanupTCF g k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs g)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env q (midEntry g cs)) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entry hchk hv hE hcs fuel
  have hW : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c =
      RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c := relW_slots hF.slots c
  have key := backend_correct_world_cleanupTCF (K := K) hsub hc hT hcov
    (by rw [hW, hF.externs]; exact hX) (by rw [hW]; exact hXI) hsym hslot hcs'
    (by rw [hW, hsl, hmem]; exact hrel) (by rw [hF.sig]; exact hargs) htr n'
  rw [hF.sig] at key
  exact ⟨fun vals cm hrun => key.1 vals cm (hn.1 _ _ hrun), fun c' hrun => key.2 c' (hn.2 _ hrun)⟩

/-- **`backend_correct_world_cleanupTC` through the mid-end validator**: `g` in the typed scope
with typed `try_call`s compiled (`CompiledCleanupTC`). -/
theorem backend_correct_midval_world_cleanupTC {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTC q g)
    (hc : CompiledCleanupTC g k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs g)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env q (midEntry g cs)) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) :=
  backend_correct_midval_world_cleanupTCF hchk hv hsub.toTCF hc.toTCF hT hcov hX hXI hsym hslot hE
    hcs hrel hargs htr fuel

end E2E

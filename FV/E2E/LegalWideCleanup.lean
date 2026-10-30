import FV.E2E.Legal
import FV.E2E.DeadCleanupFinal
import FV.Opt.Proof.LegalComplete

/-!
# The widened `i128` theorems for the backend with the dead-instruction cleanup (S4)

`backend_correct_legal_env_wide_cleanup`, `backend_correct_legal_wide_cleanup` and
`backend_correct_legal_direct_wide_cleanup`: `backend_correct_legal_env_wide` /
`backend_correct_legal_wide` / `backend_correct_legal_direct_wide` (`FV/E2E/Legal.lean`,
`FV/E2E/LegalDirect.lean`) with `backend_correct_final_cleanup` for `backend_correct_final`. The
validator `Opt.Legal.checkW` (completeness: `Opt.Legal.Complete.PreW`) accepts indirect calls at
an `i128` call-site signature and `try_call_indirect`; the `check` theorems
(`backend_correct_legal_env_cleanup`, … in `FV/E2E/DeadCleanupLegal.lean`) are these on the
domain of `check`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_legal_env_wide` for the backend with the dead-instruction cleanup.** -/
theorem backend_correct_legal_env_wide_cleanup {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    -- the environment's contracts (`FV/Opt/Proof/LegalExt.lean`)
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env)
    -- calls of `f` and `g` go to the environment
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    -- an indirect call of `f` resolves to the same extern in both programs
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    -- at an indirect call with an `i128` signature, no known signature has `i128`
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    -- `backend_correct_final`'s premises about `g`
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run: `f` on `args`, `g` on the ABI-split `args'` (same slots and memory)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit env p cs) (htr : TrapsExplicit env p' cs') (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop env p fuel cs) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hE : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK, hind, hsigs⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  have hT := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2⟩ := Opt.Legal.checkW_refines (C := C) hchk hE hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hT hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst] at hr1 hr2
  rw [hst'] at hr1 hr2
  have hB := fun k => backend_correct_final_cleanup hsub hc hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs' hrel htr k
  cases hrun : Clif.runLoop env p fuel cs with
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
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **`backend_correct_legal_wide` for the backend with the dead-instruction cleanup**: under
`Clif.Rust.env` (no known signature, `hsigs` discharged). -/
theorem backend_correct_legal_wide_cleanup {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_env_wide_cleanup hchk hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env hext hext' hind (fun _ _ _ h => by cases h)
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_direct_wide` for the backend with the dead-instruction
cleanup.** -/
theorem backend_correct_legal_direct_wide_cleanup {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hpre : Opt.Legal.Complete.PreW f) (hlg : Opt.Legalize128.function128Cert f = .ok (g, cert))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_wide_cleanup (Opt.Legal.Complete.checkW_complete hpre hlg) hsub hc hext
    hext' hind hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel
    htrS htr fuel

end E2E

import FV.E2E.LegalOptX
import FV.E2E.LegalWideCleanup
import FV.Opt.Proof.RetypeSim

/-! # Retyped data movement, legalised, compiled (S12e, #36)

`lean-backend` compiles a function `f` whose memory accesses at the types of a `TyMap σ` only
move data (`Opt.Retype.okB σ f`; S12: 128-bit vectors, `Opt.Retype.vec128`) as the `i128`
legalisation `g` of `Opt.Retype.retype σ f` (the accesses at the same-width types, `i128`).
**`backend_correct_retype_legal_wide`** (`_cleanup`: the backend with the dead-instruction
cleanup) composes the two refinements below the Arm code: the run of `f` is refined by the run
of `retype σ f` from the corresponding entry (`retypeEntry`: the same registers, slots and
memory; `Opt.Retype.retype_simX` lifted by `Opt.runLoop_refinesX`, the externs keeping the
link-time symbols), which `backend_correct_legal_wide` relates to the Arm code of `g`. Premises:
`backend_correct_legal_wide`'s, with the source entry `cs` of `f` and `TrapsExplicit` of the
retyped run from `retypeEntry σ f cs`. `backend_correct_retype_legal_opt_wide{,_cleanup}`: the
same composed with the mid-end (`backend_correct_legal_opt_wide`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Opt.Retype

/-- The entry state of `retype σ f` corresponding to the entry state `cs` of `f`. -/
def retypeEntry (σ : TyMap) (f : Clif.Function) (cs : Clif.State) : Clif.State :=
  match (retype σ f).entry? with
  | some b => ⟨⟨retype σ f, cs.frame.regs, cs.frame.slots, b.body, b.term⟩, [], cs.mem⟩
  | none => cs

theorem clifEntry_retype {σ : TyMap} {f : Clif.Function} (hok : okB σ f = true)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    ClifEntry (retype σ f) args (retypeEntry σ f cs) ∧
      Opt.SRX cs.mem.symbols cs (retypeEntry σ f cs) ∧
      (retypeEntry σ f cs).frame.slots = cs.frame.slots ∧ (retypeEntry σ f cs).mem = cs.mem := by
  have hsim := retype_simX f hok
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : retypeEntry σ f cs =
      ⟨⟨retype σ f, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [retypeEntry, hb']
  rw [hoe]
  refine ⟨⟨rfl, rfl, by rw [hsim.sig]; exact hcs.sig, ⟨b', hb', rfl, rfl, by rw [hpar]; exact hty,
    by rw [hpar]; exact hregs⟩, by rw [hsim.slots]; exact hcs.slotIds⟩, ⟨rfl, rfl,
    Opt.GRX.of hR ?_, ?_⟩, rfl, rfl⟩
  · have hfr : cs.frame = ⟨f, cs.frame.regs, cs.frame.slots, b.body, b.term⟩ := by
      have h1 := hcs.func
      cases hfr0 : cs.frame with
      | mk fu re sl bo te =>
        rw [hfr0] at h1 hbody hterm
        simp only at h1 hbody hterm
        rw [h1, hbody, hterm]
    rw [hfr]
    exact hrel args cs.frame.regs cs.frame.slots (hty.symm) hregs hcs.slotIds
  · rw [hcs.callers]; exact .nil _

/-- **The retyping refines a whole run**: the run of `f` in `p` from its entry `cs` is refined
by the run of `retype σ f` in `p` from `retypeEntry σ f cs` (the externs keeping the link-time
symbols). -/
theorem retype_entry_refines {σ : TyMap} {f : Clif.Function} (hok : okB σ f = true)
    {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env) (p : Clif.Program) {args : List Clif.Val}
    {cs : Clif.State} (hcs : ClifEntry f args cs) (fuel : Nat) :
    ∃ n', Opt.OutcomeRefines (Clif.runLoop env p fuel cs)
      (Clif.runLoop env p n' (retypeEntry σ f cs)) := by
  obtain ⟨-, hSR, -⟩ := clifEntry_retype hok hcs
  have hP : Opt.FunsSimX p.funcs (p.funcs.map id) := Opt.FunsSimX.map Opt.FunSimX.refl
  rw [List.map_id] at hP
  obtain ⟨n', hn, -⟩ := Opt.runLoop_refinesX hE hP fuel cs (retypeEntry σ f cs) hSR
  exact ⟨n', hn⟩

theorem armRefinesLegal_of_outcome {rg : List (List Opt.Legalize128.SlotEl)} {fb : FnBin}
    {base ra : BitVec 64} {step : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    {o o' : Clif.Outcome} (h : Opt.OutcomeRefines o o')
    (hA : ArmRefinesLegal rg fb base ra step s o') : ArmRefinesLegal rg fb base ra step s o := by
  obtain ⟨hret, htrap⟩ := h
  cases hrn : o with
  | returned vals m => rw [hret vals m hrn] at hA; exact hA
  | trapped c => rw [htrap c hrn] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **The end-to-end theorem for retyped data movement, legalised** (S12e): the Arm code of the
`i128` legalisation `g` of `retype σ f`, entered with the ABI-split arguments, refines the run of
the original `f` (under the trusted Rust environment `Clif.Rust.env`). -/
theorem backend_correct_retype_legal_wide {σ : TyMap} {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert} (hok : okB σ f = true)
    (hchk : Opt.Legal.checkW (retype σ f) g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite (retype σ f) sig) →
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
    (htrS : TrapsExplicit Clif.Rust.env p (retypeEntry σ f cs))
    (htr : TrapsExplicit Clif.Rust.env p' cs') (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  obtain ⟨hcsR, -, hslR, hmemR⟩ := clifEntry_retype hok hcs
  obtain ⟨n', hn⟩ := retype_entry_refines hok RustSyms.envKeepsSymbols_env p hcs fuel
  exact armRefinesLegal_of_outcome hn (backend_correct_legal_wide hchk hsub hc hext hext' hind
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcsR hcs'
    (by rw [hslR]; exact hsl) (by rw [hmemR]; exact hmem) hrel htrS htr n')

/-- **`backend_correct_retype_legal_wide` for the backend with the dead-instruction cleanup**
(`CompiledCleanup`, `lean-backend`'s default). -/
theorem backend_correct_retype_legal_wide_cleanup {σ : TyMap} {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert} (hok : okB σ f = true)
    (hchk : Opt.Legal.checkW (retype σ f) g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite (retype σ f) sig) →
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
    (htrS : TrapsExplicit Clif.Rust.env p (retypeEntry σ f cs))
    (htr : TrapsExplicit Clif.Rust.env p' cs') (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  obtain ⟨hcsR, -, hslR, hmemR⟩ := clifEntry_retype hok hcs
  obtain ⟨n', hn⟩ := retype_entry_refines hok RustSyms.envKeepsSymbols_env p hcs fuel
  exact armRefinesLegal_of_outcome hn (backend_correct_legal_wide_cleanup hchk hsub hc hext hext'
    hind hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcsR hcs'
    (by rw [hslR]; exact hsl) (by rw [hmemR]; exact hmem) hrel htrS htr n')

/-- **The end-to-end theorem for retyped data movement, legalised then optimised** (S12e): the Arm
code of `Opt.optimizeExe g cfg` (proven rule sets), `g` the `i128` legalisation of `retype σ f`, entered with the ABI-split arguments, refines the run of
the original `f` (under the trusted Rust environment `Clif.Rust.env`). -/
theorem backend_correct_retype_legal_opt_wide {σ : TyMap} {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert} (hok : okB σ f = true)
    (hchk : Opt.Legal.checkW (retype σ f) g cert = true) (cfg : Opt.Config)
    (hr : cfg.rules = .cranelift) (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite (retype σ f) sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
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
    (htrS : TrapsExplicit Clif.Rust.env p (retypeEntry σ f cs))
    (htr : TrapsExplicit Clif.Rust.env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  obtain ⟨hcsR, -, hslR, hmemR⟩ := clifEntry_retype hok hcs
  obtain ⟨n', hn⟩ := retype_entry_refines hok RustSyms.envKeepsSymbols_env p hcs fuel
  exact armRefinesLegal_of_outcome hn (backend_correct_legal_opt_wide hchk cfg hr ha hsub hc hext hext' hind
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcsR hcs'
    (by rw [hslR]; exact hsl) (by rw [hmemR]; exact hmem) hrel htrS htr n')

/-- **`backend_correct_retype_legal_opt_wide` for the backend with the dead-instruction cleanup**. -/
theorem backend_correct_retype_legal_opt_wide_cleanup {σ : TyMap} {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert} (hok : okB σ f = true)
    (hchk : Opt.Legal.checkW (retype σ f) g cert = true) (cfg : Opt.Config)
    (hr : cfg.rules = .cranelift) (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite (retype σ f) sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
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
    (htrS : TrapsExplicit Clif.Rust.env p (retypeEntry σ f cs))
    (htr : TrapsExplicit Clif.Rust.env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  obtain ⟨hcsR, -, hslR, hmemR⟩ := clifEntry_retype hok hcs
  obtain ⟨n', hn⟩ := retype_entry_refines hok RustSyms.envKeepsSymbols_env p hcs fuel
  exact armRefinesLegal_of_outcome hn (backend_correct_legal_opt_wide_cleanup hchk cfg hr ha hsub hc hext hext'
    hind hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcsR hcs'
    (by rw [hslR]; exact hsl) (by rw [hmemR]; exact hmem) hrel htrS htr n')

end E2E

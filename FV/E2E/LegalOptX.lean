import FV.E2E.OptX
import FV.E2E.Legal

/-! # Legalisation followed by optimisation (S2)

`lean-backend --opt` compiles an `i128` function `f` as `Opt.optimizeExe g cfg`, where `g` is its
legalisation (`Opt.Legalize128`). `backend_correct_legal` (`FV/E2E/Legal.lean`) covers `g`
compiled without the mid-end; `backend_correct_opt_exe` (`FV/E2E/OptX.lean`) covers the mid-end
on a function compiled without legalisation. **`backend_correct_legal_opt_env`** composes the
three refinements: the source run of `f` (in `p`) is refined by the run of `g` (in `p'`) with
ABI-split arguments and results (`Opt.Legal.check_refines`), which is refined by the run of the
optimised `g` in the optimised program `Opt.optimizeProgramExe p' cfg`
(`Opt.optimizeProgramExe`'s simulation, `call_indirect` and `try_call` included), which the Arm
code compiled from it refines (`backend_correct_final`). Premises: `backend_correct_legal_env`'s,
with the backend's about the compiled optimised function, externs keeping the link-time
symbols (`EnvKeepsSymbols`, as for every mid-end theorem), and `TrapsExplicit` of the optimised
program's run from the corresponding entry. `backend_correct_legal_opt` instantiates the
environment with `Clif.Rust.env`; `_cleanup`: the backend with the dead-instruction cleanup.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- The source run of `f` refined by the legalisation's run, refined by the optimised
legalisation's run from the corresponding entry. -/
theorem legal_opt_refines {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) {p p' : Clif.Program} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : Opt.Legal.MemBounded cs.mem) (htrS : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals m, Clif.runLoop env p fuel cs = .returned vals m → ∃ vals',
      Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧ ∃ n',
        Clif.runLoop env (Opt.optimizeProgramExe p' cfg) n' (optEntryX cfg g cs') =
          .returned vals' m) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → ∃ n',
      Clif.runLoop env (Opt.optimizeProgramExe p' cfg) n' (optEntryX cfg g cs') = .trapped c) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hEnv : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK,
    Opt.Legal.indOldB_ind (Opt.Legal.indOldB_of_check hchk) hind,
    Opt.Legal.indOldB_sigs (Opt.Legal.indOldB_of_check hchk)⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hT := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2⟩ := Opt.Legal.check_refines (C := C) hchk hEnv hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hT hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst] at hr1 hr2
  rw [hst'] at hr1 hr2
  refine ⟨fun vals m hrun => ?_, fun c hrun => ?_⟩
  · obtain ⟨vals', hv, k, hk⟩ := hr1 vals m hrun
    obtain ⟨-, -, -, n', hn⟩ := optExe_entry cfg hr ha hE hcs' k (p := p')
    exact ⟨vals', hv, n', hn.1 _ _ hk⟩
  · obtain ⟨k, hk⟩ := hr2 c hrun
    obtain ⟨-, -, -, n', hn⟩ := optExe_entry cfg hr ha hE hcs' k (p := p')
    exact ⟨n', hn.2 _ hk⟩

/-- `ArmRefinesLegal` of the source outcome from the Arm refinement of every optimised run. -/
theorem armRefinesLegal_of {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) {p p' : Clif.Program} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : Opt.Legal.MemBounded cs.mem) (htrS : TrapsExplicit env p cs)
    {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    (hB : ∀ n, ArmRefines fb base ra astep s
      (Clif.runLoop env (Opt.optimizeProgramExe p' cfg) n (optEntryX cfg g cs'))) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra astep s
      (Clif.runLoop env p fuel cs) := by
  obtain ⟨hr1, hr2⟩ := legal_opt_refines hchk cfg hr ha hH hXL hK hE hext hext' hind hexp hcs hcs'
    hsl hmem hM htrS fuel
  cases hrun : Clif.runLoop env p fuel cs with
  | returned vals m1 =>
    obtain ⟨vals', hv, n', hn⟩ := hr1 vals m1 hrun
    have := hB n'
    rw [hn] at this
    exact ⟨vals', hv, this⟩
  | trapped c =>
    obtain ⟨n', hn⟩ := hr2 c hrun
    have := hB n'
    rw [hn] at this
    exact this
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **End-to-end theorem for an `i128` function legalised then optimised** (S2), any
environment with the contracts of `check_refines` keeping the link-time symbols: the Arm code
of `Opt.optimizeExe g cfg` (`g` the accepted legalisation of `f`, the proven rule sets), entered
with the ABI-split arguments, refines the run of the original `f`. -/
theorem backend_correct_legal_opt_env {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
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
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
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
    (htrS : TrapsExplicit env p cs)
    (htr : TrapsExplicit env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop env p fuel cs) := by
  have hF := optimizeExe_shape cfg g
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  refine armRefinesLegal_of hchk cfg hr ha hH hXL hK hE hext hext' hind hexp hcs hcs' hsl hmem hM
    htrS (fun n => ?_) fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := optExe_entry cfg hr ha hE hcs' 0 (p := p')
  exact backend_correct_final (inSubset_optExe cfg hsub) hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs''
    (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n

/-- **`backend_correct_legal_opt_env` for the backend with the dead-instruction cleanup.** -/
theorem backend_correct_legal_opt_env_cleanup {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
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
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
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
    (htrS : TrapsExplicit env p cs)
    (htr : TrapsExplicit env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop env p fuel cs) := by
  have hF := optimizeExe_shape cfg g
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  refine armRefinesLegal_of hchk cfg hr ha hH hXL hK hE hext hext' hind hexp hcs hcs' hsl hmem hM
    htrS (fun n => ?_) fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := optExe_entry cfg hr ha hE hcs' 0 (p := p')
  exact backend_correct_final_cleanup (inSubset_optExe cfg hsub) hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs''
    (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n


/-! ## `Clif.Rust.env` -/

namespace RustSyms
open Clif Clif.Rust

theorem memcopy_symbols {m m' : Mem} {d s n : Nat} (h : memcopy m d s n = .ok m') :
    m'.symbols = m.symbols := by
  revert h
  unfold memcopy
  split
  · intro h; cases h; rfl
  · cases m.valid s n <;> cases m.valid d n <;> cases m.readonlyAt d n <;>
      simp [Res.check, bind, Res.bind] <;> (intro h; subst h; rfl)

theorem memstore_symbols {m m' : Mem} {d c n : Nat} (h : memstore m d c n = .ok m') :
    m'.symbols = m.symbols := by
  revert h
  unfold memstore
  cases m.valid d n <;> cases m.readonlyAt d n <;>
    simp [Res.check, bind, Res.bind] <;> (intro h; subst h; rfl)

theorem memOutcome_symbols {name : String} {vals : List Val} {m m' : Mem} {rv : List Val}
    (h : memOutcome name vals m = .returned rv m') : m'.symbols = m.symbols := by
  unfold memOutcome at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · rename_i vs m2 hres
      cases h
      split at hres
      · cases hc : memcopy m _ _ _ <;> rw [hc] at hres <;> cases hres
        exact memcopy_symbols hc
      · cases hc : memcopy m _ _ _ <;> rw [hc] at hres <;> cases hres
        exact memcopy_symbols hc
      · cases hc : memstore m _ _ _ <;> rw [hc] at hres <;> cases hres
        exact memstore_symbols hc
      · cases hc : memcmp m _ _ _ <;> rw [hc] at hres <;> cases hres
        rfl
      · cases hres
    · cases h
    · cases h

/-- **The trusted Rust externs keep the link-time symbols.** -/
theorem envKeepsSymbols_env : Opt.EnvKeepsSymbols env := by
  intro name h hext vals m rv m' hr
  simp only [env] at hext
  by_cases hd : isDivHelper name = true
  · rw [ite_eq_left hd] at hext
    cases hext
    simp only [divOutcome] at hr
    split at hr <;> cases hr
    rfl
  · rw [ite_eq_right hd] at hext
    by_cases hpn : isPanic name = true
    · rw [ite_eq_left hpn] at hext
      cases hext
      cases hr
    · rw [ite_eq_right hpn] at hext
      by_cases hm : (name == "memcpy" || name == "memmove" || name == "memset" ||
          name == "memcmp") = true
      · rw [ite_eq_left hm] at hext
        cases hext
        exact memOutcome_symbols hr
      · rw [ite_eq_right hm] at hext
        cases hext

end RustSyms

/-- **The end-to-end theorem for `i128` functions legalised then optimised** (S2) under the
trusted Rust environment `Clif.Rust.env` (its contracts `HelperOk`/`ExtLegal`/
`EnvKeepsAllocs`/`EnvKeepsSymbols` proven): the Arm code of `Opt.optimizeExe g cfg`, entered with
the ABI-split arguments, refines the run of the original `f`. -/
theorem backend_correct_legal_opt {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
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
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_opt_env hchk cfg hr ha hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext' hind
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_opt` for the backend with the dead-instruction cleanup.** -/
theorem backend_correct_legal_opt_cleanup {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
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
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_opt_env_cleanup hchk cfg hr ha hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext' hind
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-! ## Indirect calls at `i128` signatures and `try_call_indirect` (S4)

The theorems above with the validator `Opt.Legal.checkW`: an indirect call (`call_indirect`,
`try_call_indirect`) needs the programs premise `hind`, and one at an `i128` call-site signature
needs `hsigs` (no signature the environment knows has `i128`; discharged for `Clif.Rust.env`).
The `check` theorems above are these on the domain of `check`. -/

/-- The source run of `f` refined by the legalisation's run, refined by the optimised
legalisation's run from the corresponding entry. -/
theorem legal_opt_refines_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) {p p' : Clif.Program} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : Opt.Legal.MemBounded cs.mem) (htrS : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals m, Clif.runLoop env p fuel cs = .returned vals m → ∃ vals',
      Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧ ∃ n',
        Clif.runLoop env (Opt.optimizeProgramExe p' cfg) n' (optEntryX cfg g cs') =
          .returned vals' m) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → ∃ n',
      Clif.runLoop env (Opt.optimizeProgramExe p' cfg) n' (optEntryX cfg g cs') = .trapped c) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hEnv : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK, hind, hsigs⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hT := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2⟩ := Opt.Legal.checkW_refines (C := C) hchk hEnv hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hT hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst] at hr1 hr2
  rw [hst'] at hr1 hr2
  refine ⟨fun vals m hrun => ?_, fun c hrun => ?_⟩
  · obtain ⟨vals', hv, k, hk⟩ := hr1 vals m hrun
    obtain ⟨-, -, -, n', hn⟩ := optExe_entry cfg hr ha hE hcs' k (p := p')
    exact ⟨vals', hv, n', hn.1 _ _ hk⟩
  · obtain ⟨k, hk⟩ := hr2 c hrun
    obtain ⟨-, -, -, n', hn⟩ := optExe_entry cfg hr ha hE hcs' k (p := p')
    exact ⟨n', hn.2 _ hk⟩

/-- `ArmRefinesLegal` of the source outcome from the Arm refinement of every optimised run. -/
theorem armRefinesLegal_of_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) {p p' : Clif.Program} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : Opt.Legal.MemBounded cs.mem) (htrS : TrapsExplicit env p cs)
    {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    (hB : ∀ n, ArmRefines fb base ra astep s
      (Clif.runLoop env (Opt.optimizeProgramExe p' cfg) n (optEntryX cfg g cs'))) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra astep s
      (Clif.runLoop env p fuel cs) := by
  obtain ⟨hr1, hr2⟩ := legal_opt_refines_wide hchk cfg hr ha hH hXL hK hE hext hext' hind hsigs hexp hcs hcs'
    hsl hmem hM htrS fuel
  cases hrun : Clif.runLoop env p fuel cs with
  | returned vals m1 =>
    obtain ⟨vals', hv, n', hn⟩ := hr1 vals m1 hrun
    have := hB n'
    rw [hn] at this
    exact ⟨vals', hv, this⟩
  | trapped c =>
    obtain ⟨n', hn⟩ := hr2 c hrun
    have := hB n'
    rw [hn] at this
    exact this
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **End-to-end theorem for an `i128` function legalised then optimised** (S2), any
environment with the contracts of `checkW_refines` keeping the link-time symbols: the Arm code
of `Opt.optimizeExe g cfg` (`g` the accepted legalisation of `f`, the proven rule sets), entered
with the ABI-split arguments, refines the run of the original `f`. -/
theorem backend_correct_legal_opt_env_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
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
    (htrS : TrapsExplicit env p cs)
    (htr : TrapsExplicit env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop env p fuel cs) := by
  have hF := optimizeExe_shape cfg g
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  refine armRefinesLegal_of_wide hchk cfg hr ha hH hXL hK hE hext hext' hind hsigs hexp hcs hcs' hsl hmem hM
    htrS (fun n => ?_) fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := optExe_entry cfg hr ha hE hcs' 0 (p := p')
  exact backend_correct_final (inSubset_optExe cfg hsub) hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs''
    (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n

/-- **`backend_correct_legal_opt_env_wide` for the backend with the dead-instruction cleanup.** -/
theorem backend_correct_legal_opt_env_wide_cleanup {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe g cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe g cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (Opt.optimizeExe g cfg)) (fun sl cm w =>
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
    (htrS : TrapsExplicit env p cs)
    (htr : TrapsExplicit env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop env p fuel cs) := by
  have hF := optimizeExe_shape cfg g
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  refine armRefinesLegal_of_wide hchk cfg hr ha hH hXL hK hE hext hext' hind hsigs hexp hcs hcs' hsl hmem hM
    htrS (fun n => ?_) fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := optExe_entry cfg hr ha hE hcs' 0 (p := p')
  exact backend_correct_final_cleanup (inSubset_optExe cfg hsub) hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs''
    (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n

/-- **The end-to-end theorem for `i128` functions legalised then optimised** (S2) under the
trusted Rust environment `Clif.Rust.env` (its contracts `HelperOk`/`ExtLegal`/
`EnvKeepsAllocs`/`EnvKeepsSymbols` proven): the Arm code of `Opt.optimizeExe g cfg`, entered with
the ABI-split arguments, refines the run of the original `f`. -/
theorem backend_correct_legal_opt_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
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
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_opt_env_wide hchk cfg hr ha hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext' hind
    (fun _ _ _ h => by cases h)
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_opt_wide` for the backend with the dead-instruction cleanup.** -/
theorem backend_correct_legal_opt_wide_cleanup {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup (Opt.optimizeExe g cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
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
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env (Opt.optimizeProgramExe p' cfg) (optEntryX cfg g cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_opt_env_wide_cleanup hchk cfg hr ha hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext' hind
    (fun _ _ _ h => by cases h)
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

end E2E

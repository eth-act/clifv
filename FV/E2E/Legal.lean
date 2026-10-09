import FV.E2E.Final
import FV.Opt.Proof.LegalSim
import FV.Opt.Proof.LegalRust

/-! # The end-to-end theorem for `i128` functions (`Opt.Legalize128` + `Opt.Legal.check`)

A function `f` that mentions `i128` is compiled as its legalisation `g`
(`Opt.Legalize128.function128Cert`, untrusted), accepted by the validator
`Opt.Legal.check f g cert`. `backend_correct_legal` composes the validator's refinement theorem
`Opt.Legal.check_refines` (`FV/Opt/Proof/LegalSim.lean`) with `backend_correct_final` at `g`:
the Arm code compiled from `g`, entered with the ABI-split arguments (an `i128` argument as its
low/high `i64` halves in two registers, after an arbitrary pad register where AAPCS64 aligns
the pair), refines the run of the ORIGINAL function `f`: a return of `f` is an Arm return with
the results split the same way and the same memory; a trap of `f` is a trap of the Arm code with
the same code.

Discharged premises: the environment contracts of `check_refines` for `Clif.Rust.env`
(`FV/Opt/Proof/LegalRust.lean`), `MemBounded` of the entry memory (from `MemRel.valid` of the
backend relation), and `NoMemTrap` of the source run (from the source's `TrapsExplicit`: a
source run whose traps are all explicit has no load/store trap).

Remaining premises, beyond `backend_correct_final`'s about `g` (including its `try_call`
callee contract `hCT` and its indirect-call contract `hXI`, both vacuous without such calls):
calls of `f`/`g` go to the environment (`hext`/`hext'`), and for a `call_indirect` the programs
have the same function names and the source program's externs are a prefix of the target's
(`hind`). The driver's per-activation interpretation uses programs without functions, making
these program conditions immediate, including for self-calls. `TrapsExplicit` of the source
run also excludes indirect calls to a function of the activation's program.
The validator accepts `try_call` (its arguments, returns and normal-return
successor arguments split like a `call`'s and a branch's) and `call_indirect` without `i128`
operands, and `func_addr` (the same symbol name in `g`); it rejects `try_call_indirect`. The backend's
`TrapsExplicit` premise stays on the run of `g` (as for `backend_correct_opt_proven`, it is not
derived from the source's): in particular an `i128` division by zero or `sdiv MIN, -1` traps in
the source at a `div` (explicit), but in `g` inside the `__*ti3` helper call (an extern trap,
outside the backend theorem like every extern trap; natively the helper aborts).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- What the Arm run does for an outcome of the original function `f` whose results are
expanded by the ABI groups `rg` (`Opt.Legalize128.expandGroups` of `f`'s returns): a return
with values `vals` is an Arm return with the expanded values; traps as `ArmRefines`. -/
def ArmRefinesLegal (rg : List (List Opt.Legalize128.SlotEl)) (fb : FnBin) (base ra : BitVec 64)
    (astep : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) : Clif.Outcome → Prop
  | .returned vals cm => ∃ vals', Opt.Legal.ExpRel rg vals vals' ∧
      ArmRefines fb base ra astep s (.returned vals' cm)
  | o => ArmRefines fb base ra astep s o

theorem reach_of_sreach {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    (h : Opt.Legal.SReach env p s s') : Reach env p s s' := by
  induction h with
  | refl s => exact .refl s
  | step hs _ ih => exact .step hs ih

/-- A run whose indirect calls reach no function of the program (`TrapsExplicit.indirect`)
satisfies `Opt.Legal.NoIndInternal`. -/
theorem noIndInternal_of_trapsExplicit {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    (h : TrapsExplicit env p cs) (hcl : cs.callers = []) :
    Opt.Legal.NoIndInternal env p cs.frame.func ⟨cs.frame, [], cs.mem⟩ := by
  have hcs : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcl]
  rw [hcs]
  intro s' hr st rest sig callee args cv hb hi hB hc
  exact h.indirect s' st rest sig callee args (reach_of_sreach hr) hb hi hB cv hc

/-- A run whose traps are all explicit (`div`) has no load/store trap. -/
theorem noMemTrap_of_trapsExplicit {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    (h : TrapsExplicit env p cs) (hcl : cs.callers = []) :
    Opt.Legal.NoMemTrap env p ⟨cs.frame, [], cs.mem⟩ := by
  have hcs : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcl]
  rw [hcs]
  intro s' hr c st rest hst hb
  have he := h.stmt s' c st rest (reach_of_sreach hr) hst hb
  refine ⟨fun op t fl a o hi => ?_, fun op t fl x a o hi => ?_⟩ <;>
    (rw [hi] at he; cases he)

/-- The backend relation bounds the valid ranges of the CLIF memory below `2^64`. -/
theorem memBounded_of_holds {Γ : Rel} {f : Clif.Function} {sl : List (Clif.SlotId × Nat)}
    {cm : Clif.Mem} {w : Arm.ArmState} (h : Γ.holds f sl cm w) : Opt.Legal.MemBounded cm :=
  fun a n hv => (h.1.valid a n hv).1

/-- **End-to-end theorem for a legalised function, any environment with the contracts of
`check_refines`.** -/
theorem backend_correct_legal_env {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    -- the environment's contracts (`FV/Opt/Proof/LegalExt.lean`)
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env)
    -- calls of `f` and `g` go to the environment
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    -- an indirect call of `f` resolves to the same extern in both programs
    (hind : (∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
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
  have hE : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK, hind⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  have hT := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2⟩ := Opt.Legal.check_refines (C := C) hchk hE hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hT hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst] at hr1 hr2
  rw [hst'] at hr1 hr2
  have hB := fun k => backend_correct_final hsub hc hcov hC hCT hTls hX hXI hsym hslot hent hres
    hbe hargs hcs' hrel htr k
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

/-- **The end-to-end theorem for `i128` functions** (`docs/contracts/legalize128.md`): for a
function `f` whose legalisation `g` the validator accepts (`Opt.Legal.check f g cert`) and which
the backend compiles inside `InSubset`, the Arm code of `g`, entered with the ABI-split
arguments, refines the run of the original `f` under the trusted Rust environment
`Clif.Rust.env` (its contracts `HelperOk`/`ExtLegal`/`EnvKeepsAllocs` proven): returns are
returns of the expanded results with the same memory, traps are traps with the same code. -/
theorem backend_correct_legal {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
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
  backend_correct_legal_env hchk hsub hc Clif.Rust.helperOk_env Clif.Rust.extLegal_env
    Clif.Rust.envKeepsAllocs_env hext hext' hind hcov hC hCT hTls hX hXI hsym hslot hent hres hbe
    hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **Specialisation**: for a legalisation without `try_call`/`try_call_indirect` (`hnt`) and
`call_indirect` (`hci`), the former statement of `backend_correct_legal` (before
agent/last-unverified): the `try_call` callee contract, the indirect-call contract and the
programs' extern condition are vacuous. -/
theorem backend_correct_legal_callFree {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hci : ∀ B ∈ g.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ g.blocks, B.term.isTry = false)
    (hc : Compiled g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
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
  backend_correct_legal hchk hsub hc hext hext'
    (fun h => absurd (Opt.Legal.check_callInd hchk h) fun ⟨B, hB, st, hst, sig, callee, args, hi⟩ =>
      hci B hB st hst sig callee args hi)
    hcov hC (fun ⟨B, hB, h⟩ => by rw [hnt B hB] at h; cases h) hTls hX
    (fun _ => by
      rw [indSigs_eq_nil hci fun B hB callee args et e => by
        have := hnt B hB; rw [e] at this; cases this]
      exact xCallsIndOk_nil _ _ _) hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS
    htr fuel

end E2E

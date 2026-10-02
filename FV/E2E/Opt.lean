import FV.E2E.Final
import FV.Opt.Proof.Pipeline

/-! # The end-to-end theorem over the mid-end: `backend_correct_opt`

`E2E.backend_correct_final` holds for the compiled *optimised* function `Opt.optimize f cfg`
against the run of the optimised program `Opt.optimizeProgram p cfg`; composed with the mid-end's
refinement (`Opt.runLoop_refines`, from `Opt.optimize_sim`) at the entry state, the Arm run of the
compiled optimised function refines the CLIF run of the *source* program:
`Arm.run (emit (regalloc (isel (opt p)))) ≈ Clif.run p` (`docs/contracts/midend.md`, step 5).

The optimised function keeps the name, signature, stack slots, globals and externs, so the entry
state (`optEntry`), `Rel.holds` and the slot layout carry over; `InSubset` carries over because the
output stays in E, calls only what the input calls and has no `call_indirect`/`try_call` if
the input has none (`Opt.optimize_facts`). The mid-end's simulation (`lstep`) does not model
`call_indirect`, so this variant keeps the premise that `f` has none (`hci`, with `hnt` for
`try_call`/`try_call_indirect`); then the optimised function has no indirect-call signatures and
the indirect-call contract of `backend_correct_final` is vacuous (`xCallsIndOk_nil`).
`FormsCovered`
stays a per-function decided premise (about the optimised code), as do `TrapsExplicit` (about
the optimised program's run) and `EnvKeepsSymbols` (externs keep the link-time symbols).
The simplify stage enters through `Opt.SimplifyPassSim` (proven for sound rule sets,
`Opt.simplifyPassSim`; the instance without the hypothesis for the proven rule sets is
`E2E.backend_correct_opt_proven`, `FV/E2E/OptProven.lean`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- The entry state of the optimised function corresponding to the entry state `cs` of `f`
(same registers, slots and memory). -/
def optEntry (cfg : Opt.Config) (f : Clif.Function) (cs : Clif.State) : Clif.State :=
  match (Opt.optimize f cfg).entry? with
  | some b => ⟨⟨Opt.optimize f cfg, cs.frame.regs, cs.frame.slots, b.body, b.term⟩, [], cs.mem⟩
  | none => cs

theorem rel_holds_slots {Γ : Rel} {f g : Clif.Function} (h : g.slots = f.slots) :
    Rel.holds Γ g = Rel.holds Γ f := by
  funext sl cm w
  simp only [Rel.holds, SlotRel, h]

/-- The mid-end's premise on `f` (`Opt.NoCallIndirect`): no `call_indirect` statement (`hci`)
and no `try_call`/`try_call_indirect` terminator (`hnt`); `lstep` does not model them. -/
theorem noCI_of (f : Clif.Function)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false) : Opt.NoCallIndirect f := ⟨hci, hnt⟩

/-- A function without indirect calls (`Opt.NoCallIndirect`) has no indirect-call signatures. -/
theorem indSigs_nil_of_noCI {g : Clif.Function} (h : Opt.NoCallIndirect g) : indSigs g = [] :=
  indSigs_eq_nil h.1 fun B hB callee args et e => by
    have := h.2 B hB; rw [e] at this; cases this

theorem inSubset_opt (cfg : Opt.Config) {p : Clif.Program} {f : Clif.Function}
    (hsub : InSubset p f)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false) :
    InSubset (Opt.optimizeProgram p cfg) (Opt.optimize f cfg) := by
  have hF := Opt.optimize_facts cfg f
  have hname : ∀ g : Clif.Function, (Opt.optimize g cfg).name = g.name :=
    fun g => (Opt.optimize_facts cfg g).name
  have hfind : ∀ n, (Opt.optimizeProgram p cfg).func? n = (p.func? n).map (Opt.optimize · cfg) := by
    intro n
    simp only [Clif.Program.func?, Opt.optimizeProgram, List.find?_map]
    rw [show ((fun x : Clif.Function => x.name == n) ∘ fun x => Opt.optimize x cfg) =
      (fun x => x.name == n) from by funext g; simp [hname]]
  have hnci := hF.noCI (noCI_of f hci hnt)
  refine ⟨?_, hF.subsetE hsub.subsetE, ?_, ?_, ?_,
    by rw [indSigs_nil_of_noCI hnci]; simp⟩
  · rw [hfind, hF.name, hsub.func]; rfl
  · intro b hb st hst fn args hc e he
    obtain ⟨b0, hb0, st0, hst0, args0, hc0⟩ :=
      Opt.mem_callees.1 (hF.callees fn (Opt.mem_callees.2 ⟨b, hb, st, hst, args, hc⟩))
    have he0 : f.extern? fn = some e := by
      simpa [Clif.Function.extern?, hF.externs] using he
    rw [hfind, hsub.externCalls b0 hb0 st0 hst0 fn args0 hc0 e he0]; rfl
  · intro b hb fn args et ht
    have := hnci.2 b hb
    rw [ht] at this; cases this
  · constructor
    · rw [hF.sig]; exact hsub.abiSigs.1
    · intro e he
      have : e ∈ f.externs := by rw [← hF.externs]; exact he
      exact hsub.abiSigs.2 e this

theorem clifEntry_opt (cfg : Opt.Config)
    (hS : Opt.SimplifyPassSim cfg.simplifyFn cfg.skeletonFn) {f : Clif.Function}
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    ClifEntry (Opt.optimize f cfg) args (optEntry cfg f cs) ∧
      Opt.SR cs.mem.symbols cs (optEntry cfg f cs) := by
  have hsim := Opt.optimize_sim cfg hS f
  have hF := Opt.optimize_facts cfg f
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : optEntry cfg f cs =
      ⟨⟨Opt.optimize f cfg, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [optEntry, hb']
  rw [hoe]
  refine ⟨⟨rfl, rfl, by rw [hF.sig]; exact hcs.sig, ⟨b', hb', rfl, rfl, by rw [hpar]; exact hty,
    by rw [hpar]; exact hregs⟩, by rw [hF.slots]; exact hcs.slotIds⟩, rfl, rfl, ⟨R, hR, ?_⟩, ?_⟩
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

/-- An in-subset function without `call_indirect` and `try_call`/`try_call_indirect` has no tail
call (not in E), and calls only externs that are not functions of `p`: the source run from `f`
stays in `f`. -/
theorem ciFree_of_subset {p : Clif.Program} {f : Clif.Function} (hsub : InSubset p f)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false) : Opt.CIFree p (· = f) where
  noCI := by
    rintro g rfl
    exact noCI_of g hci hnt
  call := by
    rintro g rfl b hb st hst fn args hi e he h hh
    rw [hsub.externCalls b hb st hst fn args hi e he] at hh
    cases hh
  tail := by
    rintro g rfl b hb fn args ht e he h hh
    have hE := hsub.subsetE
    simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hE
    have h := (hE.2 b hb).2
    rw [ht] at h
    simp [Compile.termE] at h

theorem inv_of_entry {f : Clif.Function} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) : Opt.RunInv (· = f) cs := by
  obtain ⟨b, hb, hbody, hterm, -⟩ := hcs.entry
  refine ⟨⟨hcs.func, b, ?_, by rw [hbody]; exact List.suffix_refl _, by rw [hterm]⟩, ?_⟩
  · rw [hcs.func]; exact List.mem_of_mem_head? hb
  · rw [hcs.callers]; intro _ h; cases h

/-- **End-to-end theorem over the mid-end.** For an in-subset function `f` of `p`, the Arm run
of the compiled *optimised* function (`Opt.optimize f cfg`, compiled by the backend: `hc`)
refines the CLIF run of the *source* program `p` from `f`'s entry state: whenever
`Clif.runLoop env p fuel cs` returns or traps, the Arm code returns the same values (and memory)
or stops at a trap site with the same code. Premises as `backend_correct_final` (about the
compiled optimised code; `Rel.holds`/`XCallsOk` stated for `f`, which has the optimised
function's slots; the indirect-call contract is vacuous), plus: `f` has no `call_indirect` (`hci`)
and no `try_call`/`try_call_indirect` (`hnt`: the mid-end simulation covers such functions),
the simplify stage refines (`hS`), externs keep the link-time symbols (`hE`), and the optimised program's run from the corresponding entry state traps only explicitly
(`htr`). -/
theorem backend_correct_opt (cfg : Opt.Config)
    (hS : Opt.SimplifyPassSim cfg.simplifyFn cfg.skeletonFn)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false)
    (hc : Compiled (Opt.optimize f cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : hasTls (Opt.optimize f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (Opt.optimizeProgram p cfg) (optEntry cfg f cs)) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := Opt.optimize_facts cfg f
  obtain ⟨hcs', hSR⟩ := clifEntry_opt cfg hS hcs
  have hP : Opt.FunsSim p.funcs (Opt.optimizeProgram p cfg).funcs :=
    Opt.FunsSim.map (T := (Opt.optimize · cfg)) (Opt.optimize_sim cfg hS)
  obtain ⟨n', hn⟩ := Opt.runLoop_refines hE hP (ciFree_of_subset hsub hci hnt) fuel cs (optEntry cfg f cs)
    hSR (inv_of_entry hcs)
  have hslots : (optEntry cfg f cs).frame.slots = cs.frame.slots ∧
      (optEntry cfg f cs).mem = cs.mem := by
    obtain ⟨b, hb, -⟩ := hcs.entry
    obtain ⟨R, -, hent'⟩ := (Opt.optimize_sim cfg hS f).sim cs.mem.symbols
    obtain ⟨b', hb', -⟩ := hent' b hb
    simp [optEntry, hb']
  have hnci := hF.noCI (noCI_of f hci hnt)
  have hA := backend_correct_final (inSubset_opt cfg hsub hci hnt) hc hcov hC
    (fun ⟨B, hB, h⟩ => by rw [hnci.2 B hB] at h; cases h) hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun _ => by rw [indSigs_nil_of_noCI hnci]; exact xCallsIndOk_nil _ _ _) hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hslots.1, hslots.2]; exact hrel) htr n'
  obtain ⟨hret, htrap⟩ := hn
  cases hr : Clif.runLoop env p fuel cs with
  | returned vals m => rw [hret vals m hr] at hA; exact hA
  | trapped c => rw [htrap c hr] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

end E2E

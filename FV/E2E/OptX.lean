module

public import FV.E2E.Opt
public import FV.E2E.DeadCleanupFinal
public import FV.Opt.Proof.PipelineX

@[expose] public section

/-! # The end-to-end theorem over the mid-end, indirect calls and `try_call` included (S1)

`E2E.backend_correct_opt_proven` (`FV/E2E/OptProven.lean`) excludes functions with
`call_indirect` (`hci`) and `try_call`/`try_call_indirect` (`hnt`): the mid-end's simulation
did not model them. The simulations of `FV/Opt/Proof/SemSimX.lean` do (`Opt.IsSimX`), and the
mid-end of the executable compiler `Opt.optimizeExe` (`optimize` with the fresh-value guard and
the shape guard, `FV/Opt/OptimizeX.lean`) refines every program (`Opt.optimizeProgramExe_refines`).

**`backend_correct_opt_exe`**: the Arm run of the compiled `Opt.optimizeExe f cfg` refines the
CLIF run of the *source* program from `f`'s entry, for every configuration with the proven rule
sets — no premise on `f`'s calls. The premises about the compiled optimised code are those of
`backend_correct_final` (now including the indirect-call contract `XCallsIndOk` of the optimised
function's indirect calls and the `try_call` callee contract `CalleeTryOk`, both vacuous without
them), externs keep the link-time symbols (`EnvKeepsSymbols`), and the optimised program's run
traps only explicitly (`TrapsExplicit`). `backend_correct_opt_exe_cleanup`: the same for the
backend with the dead-instruction cleanup (`CompiledCleanup`, `lean-backend`'s default).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The shape of `optimizeExe`'s output -/

/-- What `optimizeExe` keeps of its input besides the simulation. -/
structure ShapeFacts (f g : Clif.Function) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  externs : g.externs = f.externs
  sigDecls : g.sigDecls = f.sigDecls
  subsetE : Compile.functionE f = true → Compile.functionE g = true
  callees : ∀ fn ∈ Opt.callees g, fn ∈ Opt.callees f
  tryCallees : ∀ fn ∈ Opt.tryCallees g, fn ∈ Opt.tryCallees f
  indSigIds : ∀ i ∈ Opt.indSigIds g, i ∈ Opt.indSigIds f
  retCall : Opt.retCallFreeB g = true → Opt.retCallFreeB f = true
  indCall : Opt.indCallFreeB g = true → Opt.indCallFreeB f = true
  blocksNil : f.blocks = [] → g.blocks = []

theorem ShapeFacts.refl (f : Clif.Function) : ShapeFacts f f :=
  ⟨rfl, rfl, rfl, rfl, rfl, id, fun _ h => h, fun _ h => h, fun _ h => h, id, id, id⟩

theorem keepsShapeB_spec {f g : Clif.Function} (h : Opt.keepsShapeB f g = true) :
    (∀ fn ∈ Opt.tryCallees g, fn ∈ Opt.tryCallees f) ∧ (∀ i ∈ Opt.indSigIds g, i ∈ Opt.indSigIds f) ∧
      (Opt.retCallFreeB g = true → Opt.retCallFreeB f = true) ∧
      (Opt.indCallFreeB g = true → Opt.indCallFreeB f = true) ∧ (f.blocks = [] → g.blocks = []) := by
  simp only [Opt.keepsShapeB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun hg => ?_, fun hg => ?_, fun hf => ?_⟩
  rotate_left 2
  · rcases h5 with h5 | h5
    · rw [hf] at h5; cases h5
    · exact List.isEmpty_iff.1 h5
  · rcases h3 with h3 | h3
    · exact h3
    · rw [hg] at h3; cases h3
  · rcases h4 with h4 | h4
    · exact h4
    · rw [hg] at h4; cases h4

theorem optimizeX_facts (cfg : Opt.Config) (f : Clif.Function) :
    Opt.BackendFacts f (Opt.optimizeX f cfg) := by
  unfold Opt.optimizeX
  split
  · exact Opt.optimize_facts cfg f
  · exact ⟨rfl, rfl, rfl, rfl, rfl, id, fun _ h => h, id⟩

theorem optimizeExe_shape (cfg : Opt.Config) (f : Clif.Function) :
    ShapeFacts f (Opt.optimizeExe f cfg) := by
  have hsd := Opt.optimizeExe_sigDecls cfg f
  unfold Opt.optimizeExe at hsd ⊢
  dsimp only at hsd ⊢
  split
  · rename_i hk
    simp only [hk, ↓reduceIte] at hsd
    have hF := optimizeX_facts cfg f
    obtain ⟨h1, h2, h3, h4, h5⟩ := keepsShapeB_spec hk
    exact ⟨hF.name, hF.sig, hF.slots, hF.externs, hsd, hF.subsetE, hF.callees, h1, h2, h3, h4, h5⟩
  · exact ShapeFacts.refl f

/-- The indirect-call signatures are the declarations of the indirect calls' signature ids. -/
theorem mem_indSigs {f : Clif.Function} {s : Clif.Signature} :
    s ∈ indSigs f ↔ ∃ i ∈ Opt.indSigIds f, f.sigDecls.lookup i = some s := by
  simp only [indSigs, Opt.indSigIds, List.mem_flatMap, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, h⟩
    rcases h with ⟨st, hst, h⟩ | h
    · split at h
      · rename_i sig _ _ hi
        exact ⟨sig, ⟨b, hb, .inl ⟨st, hst, by simp [hi]⟩⟩, h⟩
      · cases h
    · split at h
      · rename_i et _
        exact ⟨et.sig, ⟨b, hb, .inr (by simp [*])⟩, by simpa using h⟩
      · cases h
  · rintro ⟨i, ⟨b, hb, h⟩, hl⟩
    refine ⟨b, hb, ?_⟩
    rcases h with ⟨st, hst, h⟩ | h
    · refine .inl ⟨st, hst, ?_⟩
      split at h
      · rename_i sig _ _ hi
        simp only [Option.some.injEq] at h; subst h
        simp [hi, hl]
      · cases h
    · refine .inr ?_
      split at h
      · rename_i et _
        simp only [List.mem_singleton] at h; subst h
        simp [*]
      · cases h

theorem ShapeFacts.indSigs {f g : Clif.Function} (h : ShapeFacts f g) {s : Clif.Signature}
    (hs : s ∈ indSigs g) : s ∈ indSigs f := by
  obtain ⟨i, hi, hl⟩ := mem_indSigs.1 hs
  exact mem_indSigs.2 ⟨i, h.indSigIds i hi, by rw [← h.sigDecls]; exact hl⟩

theorem mem_tryCallees {f : Clif.Function} {fn : Clif.FnRef} :
    fn ∈ Opt.tryCallees f ↔ ∃ b ∈ f.blocks, ∃ args et, b.term = .tryCall fn args et := by
  simp only [Opt.tryCallees, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, h⟩
    split at h
    · rename_i fn' args et ht
      simp only [Option.some.injEq] at h; subst h
      exact ⟨b, hb, args, et, ht⟩
    · cases h
  · rintro ⟨b, hb, args, et, ht⟩
    exact ⟨b, hb, by simp [ht]⟩

theorem optimizeProgramExe_func? (cfg : Opt.Config) (p : Clif.Program) (n : String) :
    (Opt.optimizeProgramExe p cfg).func? n = (p.func? n).map (Opt.optimizeExe · cfg) := by
  have hname : ∀ g : Clif.Function, (Opt.optimizeExe g cfg).name = g.name :=
    fun g => (optimizeExe_shape cfg g).name
  simp only [Clif.Program.func?, Opt.optimizeProgramExe, List.find?_map]
  rw [show ((fun x : Clif.Function => x.name == n) ∘ fun x => Opt.optimizeExe x cfg) =
    (fun x => x.name == n) from by funext g; simp [hname]]

/-- The optimised function is in the backend's subset when the source function is. -/
theorem inSubset_optExe (cfg : Opt.Config) {p : Clif.Program} {f : Clif.Function}
    (hsub : InSubset p f) : InSubset (Opt.optimizeProgramExe p cfg) (Opt.optimizeExe f cfg) := by
  have hF := optimizeExe_shape cfg f
  refine ⟨hF.subsetE hsub.subsetE, ?_, ?_, ?_, fun s hs => hsub.indSigs s (hF.indSigs hs)⟩
  · intro b hb st hst fn args hc e he
    obtain ⟨b0, hb0, st0, hst0, args0, hc0⟩ :=
      Opt.mem_callees.1 (hF.callees fn (Opt.mem_callees.2 ⟨b, hb, st, hst, args, hc⟩))
    have he0 : f.extern? fn = some e := by
      simpa [Clif.Function.extern?, hF.externs] using he
    rw [optimizeProgramExe_func?, hsub.externCalls b0 hb0 st0 hst0 fn args0 hc0 e he0]; rfl
  · intro b hb fn args et ht e he
    obtain ⟨b0, hb0, args0, et0, ht0⟩ :=
      mem_tryCallees.1 (hF.tryCallees fn (mem_tryCallees.2 ⟨b, hb, args, et, ht⟩))
    have he0 : f.extern? fn = some e := by
      simpa [Clif.Function.extern?, hF.externs] using he
    rw [optimizeProgramExe_func?, hsub.tryExterns b0 hb0 fn args0 et0 ht0 e he0]; rfl
  · constructor
    · rw [hF.sig]; exact hsub.abiSigs.1
    · intro e he
      have : e ∈ f.externs := by rw [← hF.externs]; exact he
      exact hsub.abiSigs.2 e this

/-! ## Entries -/

/-- The entry state of the optimised function corresponding to the entry state `cs` of `f`. -/
def optEntryX (cfg : Opt.Config) (f : Clif.Function) (cs : Clif.State) : Clif.State :=
  match (Opt.optimizeExe f cfg).entry? with
  | some b => ⟨⟨Opt.optimizeExe f cfg, cs.frame.regs, cs.frame.slots, b.body, b.term⟩, [], cs.mem⟩
  | none => cs

theorem clifEntry_optX (cfg : Opt.Config)
    (hS : Opt.SimplifyPassSimX cfg.simplifyFn cfg.skeletonFn) {f : Clif.Function}
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    ClifEntry (Opt.optimizeExe f cfg) args (optEntryX cfg f cs) ∧
      Opt.SRX cs.mem.symbols cs (optEntryX cfg f cs) := by
  have hsim := Opt.optimizeExe_simX cfg hS f
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : optEntryX cfg f cs =
      ⟨⟨Opt.optimizeExe f cfg, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [optEntryX, hb']
  rw [hoe]
  refine ⟨⟨rfl, rfl, by rw [hsim.sig]; exact hcs.sig, ⟨b', hb', rfl, rfl, by rw [hpar]; exact hty,
    by rw [hpar]; exact hregs⟩, by rw [hsim.slots]; exact hcs.slotIds⟩, rfl, rfl,
    Opt.GRX.of hR ?_, ?_⟩
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

/-! ## The theorem -/

/-- The source run from `f`'s entry, refined by the optimised program's run from the
corresponding entry (`optEntryX`); the facts the backend theorem needs of that entry. -/
theorem optExe_entry (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) {p : Clif.Program} {f : Clif.Function} {env : Clif.Env}
    (hE : Opt.EnvKeepsSymbols env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) (fuel : Nat) :
    ClifEntry (Opt.optimizeExe f cfg) args (optEntryX cfg f cs) ∧
      (optEntryX cfg f cs).frame.slots = cs.frame.slots ∧ (optEntryX cfg f cs).mem = cs.mem ∧
      ∃ n', Opt.OutcomeRefines (Clif.runLoop env p fuel cs)
        (Clif.runLoop env (Opt.optimizeProgramExe p cfg) n' (optEntryX cfg f cs)) := by
  have hS := Opt.simplifyPassSimX_proven hr ha
  obtain ⟨hcs', hSR⟩ := clifEntry_optX cfg hS hcs
  have hP : Opt.FunsSimX p.funcs (Opt.optimizeProgramExe p cfg).funcs :=
    Opt.FunsSimX.map (T := (Opt.optimizeExe · cfg)) (Opt.optimizeExe_simX cfg hS)
  obtain ⟨n', hn, -⟩ := Opt.runLoop_refinesX hE hP fuel cs (optEntryX cfg f cs) hSR
  obtain ⟨b, hb, -⟩ := hcs.entry
  obtain ⟨R, -, hent'⟩ := (Opt.optimizeExe_simX cfg hS f).sim cs.mem.symbols
  obtain ⟨b', hb', -⟩ := hent' b hb
  exact ⟨hcs', by simp [optEntryX, hb'], by simp [optEntryX, hb'], n', hn⟩

theorem armRefines_of_outcome {fb : FnBin} {base ra : BitVec 64} {step : Arm.ArmState → Arm.ArmState}
    {s : Arm.ArmState} {o o' : Clif.Outcome} (h : Opt.OutcomeRefines o o')
    (hA : ArmRefines fb base ra step s o') : ArmRefines fb base ra step s o := by
  obtain ⟨hret, htrap⟩ := h
  cases hrn : o with
  | returned vals m => rw [hret vals m hrn] at hA; exact hA
  | trapped c => rw [htrap c hrn] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **End-to-end theorem over the mid-end of the executable compiler, proven rule sets,
`call_indirect` and `try_call`/`try_call_indirect` included** (S1). For an in-subset function
`f` of `p`, the Arm run of the compiled *optimised* function `Opt.optimizeExe f cfg` refines the
CLIF run of the *source* program `p` from `f`'s entry state: whenever `Clif.runLoop env p fuel
cs` returns or traps, the Arm code returns the same values (and memory) or stops at a trap site
with the same code. `backend_correct_opt_proven` without its premises `hci`/`hnt`; premises as
`backend_correct_final`'s about the compiled optimised code (its `try_call` callee contract
`hCT`, its indirect-call contract `hXI`, both vacuous without such calls), externs keep the
link-time symbols (`hE`), and the optimised program's run traps only explicitly (`htr`). -/
theorem backend_correct_opt_exe (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : Compiled (Opt.optimizeExe f cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe f cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (Opt.optimizeProgramExe p cfg) (optEntryX cfg f cs)) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := optimizeExe_shape cfg f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := optExe_entry cfg hr ha hE hcs fuel (p := p)
  exact armRefines_of_outcome hn (backend_correct_final (inSubset_optExe cfg hsub) hc hcov hC hCT
    hTls (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_opt_exe` for the backend with the dead-instruction cleanup**
(`CompiledCleanup`, `lean-backend`'s default). -/
theorem backend_correct_opt_exe_cleanup (cfg : Opt.Config) (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven)
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : CompiledCleanup (Opt.optimizeExe f cfg) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (Opt.optimizeExe f cfg).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (Opt.optimizeExe f cfg) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (Opt.optimizeExe f cfg)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (Opt.optimizeProgramExe p cfg) (optEntryX cfg f cs)) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := optimizeExe_shape cfg f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := optExe_entry cfg hr ha hE hcs fuel (p := p)
  exact armRefines_of_outcome hn (backend_correct_final_cleanup (inSubset_optExe cfg hsub) hc hcov
    hC hCT hTls (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

end E2E

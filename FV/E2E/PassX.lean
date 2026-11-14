import FV.E2E.OptUnwind
import FV.E2E.LegalOptUnwind
import FV.E2E.FinalTCF

/-! # The end-to-end theorems over a CLIF-to-CLIF pass (#990)

`FV/E2E/OptX.lean`, `OptUnwind.lean`, `LegalOptX.lean` and `LegalOptUnwind.lean` compose the
per-function theorems of the backend with the mid-end of the executable compiler
(`Opt.optimizeExe · cfg`). Their proofs read only three facts about the mid-end: its output
simulates its input (`Opt.FunSimX`; with the handler edges, `Opt.FunSimU`), it keeps the input's
shape (`ShapeFacts`), and a program is transformed function by function. This file states the
same theorems for **any pass `T : Clif.Function → Clif.Function` with these facts**:

* `passProg T p`, `passEntry T f cs`: the transformed program and the entry state of `T f`
  corresponding to an entry state `cs` of `f`;
* `pass_entry` (`pass_entryX` with unwinding): the source run from `f`'s entry is refined by the
  transformed program's run from that entry; `pass_lift` (`pass_liftU`): so every
  per-activation conclusion closed under that refinement (`ArmRefines`, `ArmRefinesT`,
  `ArmRefinesU`) for every run of the transformed program holds for the source run;
* **`backend_correct_pass`**, **`backend_correct_pass_cleanup`**: `backend_correct_opt_exe{,_cleanup}`
  for `T`;
* **`backend_correct_pass_finalTCF`**: the typed `backend_correct_finalTCF` composed with `T`;
* **`backend_correct_pass_unwind_any`**, **`backend_correct_pass_cleanup_unwind_any`**: with
  unwinding (`backend_correct_opt_exe{,_cleanup}_unwind_any` for `T`);
* **`backend_correct_legal_pass_wide`**, **`backend_correct_legal_pass_wide_cleanup`**: an `i128`
  function legalised (`Opt.Legal.checkW`), then transformed (`backend_correct_legal_opt_wide{,_cleanup}`
  for `T`); **`backend_correct_legal_pass_unwind_any`**: with unwinding
  (`backend_correct_legal_opt_unwind_any` for `T`).

The instances `lean-backend` uses (constant-phi removal `Opt.ConstPhi.run`, and it followed by the
mid-end) are in `FV/E2E/ConstPhiE2E.lean`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables

variable (T : Clif.Function → Clif.Function)

/-- The program with every function transformed by `T`. -/
def passProg (p : Clif.Program) : Clif.Program := { p with funcs := p.funcs.map T }

/-- The entry state of `T f` corresponding to the entry state `cs` of `f`. -/
def passEntry (f : Clif.Function) (cs : Clif.State) : Clif.State :=
  match (T f).entry? with
  | some b => ⟨⟨T f, cs.frame.regs, cs.frame.slots, b.body, b.term⟩, [], cs.mem⟩
  | none => cs

variable {T}

theorem ShapeFacts.trans {f g h : Clif.Function} (h1 : ShapeFacts f g) (h2 : ShapeFacts g h) :
    ShapeFacts f h :=
  ⟨h2.name.trans h1.name, h2.sig.trans h1.sig, h2.slots.trans h1.slots,
    h2.externs.trans h1.externs, h2.sigDecls.trans h1.sigDecls,
    fun h => h2.subsetE (h1.subsetE h), fun fn hm => h1.callees fn (h2.callees fn hm),
    fun fn hm => h1.tryCallees fn (h2.tryCallees fn hm),
    fun i hm => h1.indSigIds i (h2.indSigIds i hm), fun hg => h1.retCall (h2.retCall hg),
    fun hg => h1.indCall (h2.indCall hg), fun hf => h2.blocksNil (h1.blocksNil hf)⟩

theorem passProg_func? (hS : ∀ f, ShapeFacts f (T f)) (p : Clif.Program) (n : String) :
    (passProg T p).func? n = (p.func? n).map T := by
  have hname : ∀ g : Clif.Function, (T g).name = g.name := fun g => (hS g).name
  simp only [Clif.Program.func?, passProg, List.find?_map]
  rw [show ((fun x : Clif.Function => x.name == n) ∘ T) = (fun x => x.name == n) from by
    funext g; simp [hname]]

/-- The transformed function is in the backend's subset when the source function is. -/
theorem inSubset_pass (hS : ∀ f, ShapeFacts f (T f)) {p : Clif.Program} {f : Clif.Function}
    (hsub : InSubset p f) : InSubset (passProg T p) (T f) := by
  have hF := hS f
  refine ⟨hF.subsetE hsub.subsetE, ?_, ?_, ?_, fun s hs => hsub.indSigs s (hF.indSigs hs)⟩
  · intro b hb st hst fn args hc e he
    obtain ⟨b0, hb0, st0, hst0, args0, hc0⟩ :=
      Opt.mem_callees.1 (hF.callees fn (Opt.mem_callees.2 ⟨b, hb, st, hst, args, hc⟩))
    have he0 : f.extern? fn = some e := by
      simpa [Clif.Function.extern?, hF.externs] using he
    rw [passProg_func? hS, hsub.externCalls b0 hb0 st0 hst0 fn args0 hc0 e he0]; rfl
  · intro b hb fn args et ht e he
    obtain ⟨b0, hb0, args0, et0, ht0⟩ :=
      mem_tryCallees.1 (hF.tryCallees fn (mem_tryCallees.2 ⟨b, hb, args, et, ht⟩))
    have he0 : f.extern? fn = some e := by
      simpa [Clif.Function.extern?, hF.externs] using he
    rw [passProg_func? hS, hsub.tryExterns b0 hb0 fn args0 et0 ht0 e he0]; rfl
  · constructor
    · rw [hF.sig]; exact hsub.abiSigs.1
    · intro e he
      have : e ∈ f.externs := by rw [← hF.externs]; exact he
      exact hsub.abiSigs.2 e this

/-! ## Entries -/

/-- The frame of an entry state of `f`. -/
theorem ClifEntry.frame_eq {f : Clif.Function} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) {b : Clif.Block} (hbody : cs.frame.body = b.body)
    (hterm : cs.frame.term = b.term) :
    cs.frame = ⟨f, cs.frame.regs, cs.frame.slots, b.body, b.term⟩ := by
  have h1 := hcs.func
  cases hfr0 : cs.frame with
  | mk fu re sl bo te =>
    rw [hfr0] at h1 hbody hterm
    simp only at h1 hbody hterm
    rw [h1, hbody, hterm]

theorem clifEntry_pass (hT : ∀ f, Opt.FunSimX f (T f)) {f : Clif.Function}
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    ClifEntry (T f) args (passEntry T f cs) ∧ Opt.SRX cs.mem.symbols cs (passEntry T f cs) := by
  have hsim := hT f
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : passEntry T f cs =
      ⟨⟨T f, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [passEntry, hb']
  rw [hoe]
  refine ⟨⟨rfl, rfl, by rw [hsim.sig]; exact hcs.sig, ⟨b', hb', rfl, rfl, by rw [hpar]; exact hty,
    by rw [hpar]; exact hregs⟩, by rw [hsim.slots]; exact hcs.slotIds⟩, rfl, rfl,
    Opt.GRX.of hR ?_, ?_⟩
  · rw [ClifEntry.frame_eq hcs hbody hterm]
    exact hrel args cs.frame.regs cs.frame.slots (hty.symm) hregs hcs.slotIds
  · rw [hcs.callers]; exact .nil _

/-- **The source run from `f`'s entry, refined by the transformed program's run** from the
corresponding entry (`passEntry`); the facts the backend theorems need of that entry. -/
theorem pass_entry (hT : ∀ f, Opt.FunSimX f (T f)) {p : Clif.Program} {f : Clif.Function}
    {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) (fuel : Nat) :
    ClifEntry (T f) args (passEntry T f cs) ∧
      (passEntry T f cs).frame.slots = cs.frame.slots ∧ (passEntry T f cs).mem = cs.mem ∧
      ∃ n', Opt.OutcomeRefines (Clif.runLoop env p fuel cs)
        (Clif.runLoop env (passProg T p) n' (passEntry T f cs)) := by
  obtain ⟨hcs', hSR⟩ := clifEntry_pass hT hcs
  have hP : Opt.FunsSimX p.funcs (passProg T p).funcs := Opt.FunsSimX.map hT
  obtain ⟨n', hn, -⟩ := Opt.runLoop_refinesX hE hP fuel cs (passEntry T f cs) hSR
  obtain ⟨b, hb, -⟩ := hcs.entry
  obtain ⟨R, -, hent'⟩ := (hT f).sim cs.mem.symbols
  obtain ⟨b', hb', -⟩ := hent' b hb
  exact ⟨hcs', by simp [passEntry, hb'], by simp [passEntry, hb'], n', hn⟩

/-- **Every per-activation conclusion lifts through the pass**: a predicate `R` of outcomes
closed under `Opt.OutcomeRefines` (`armRefines_of_outcome`, `armRefinesT_of_outcome`) that
holds for every run of the transformed program from `T f`'s entry holds for the source run from
`f`'s entry. -/
theorem pass_lift (hT : ∀ f, Opt.FunSimX f (T f)) {p : Clif.Program} {f : Clif.Function}
    {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) {R : Clif.Outcome → Prop}
    (hR : ∀ o o', Opt.OutcomeRefines o o' → R o' → R o)
    (h : ∀ n, R (Clif.runLoop env (passProg T p) n (passEntry T f cs))) (fuel : Nat) :
    R (Clif.runLoop env p fuel cs) := by
  obtain ⟨-, -, -, n', hn⟩ := pass_entry hT (p := p) hE hcs fuel
  exact hR _ _ hn (h n')

theorem armRefinesT_of_outcome {fb : FnBin} {base ra : BitVec 64}
    {step : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {o o' : Clif.Outcome}
    (h : Opt.OutcomeRefines o o') (hA : ArmRefinesT fb base ra step s o') :
    ArmRefinesT fb base ra step s o := by
  obtain ⟨hret, htrap⟩ := h
  cases hrn : o with
  | returned vals m => rw [hret vals m hrn] at hA; exact hA
  | trapped c => rw [htrap c hrn] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

/-- The entry states of `f` and of `T f` are related with unwinding. -/
theorem clifEntry_passU (hU : ∀ f, Opt.FunSimU f (T f)) {f : Clif.Function}
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    Opt.SRU cs.mem.symbols cs.toX (passEntry T f cs).toX := by
  have hsim := hU f
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : passEntry T f cs =
      ⟨⟨T f, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [passEntry, hb']
  have hcx : cs.toX = ⟨cs, []⟩ := by simp [Clif.State.toX, hcs.callers]
  rw [hcx, hoe]
  refine ⟨rfl, rfl, Opt.GRU.of hR ?_, ?_⟩
  · show R cs.frame ⟨T f, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩
    rw [ClifEntry.frame_eq hcs hbody hterm]
    exact hrel args cs.frame.regs cs.frame.slots (hty.symm) hregs hcs.slotIds
  · show Opt.CallersRelU _ _ cs.callers [] [] []
    rw [hcs.callers]; exact .nil _

/-- **The source run with unwinding from `f`'s entry, refined by the transformed program's run
with unwinding** from the corresponding entry (`pass_entry` with unwinding: returns, traps and
exceptions leaving the run are matched). -/
theorem pass_entryX (hU : ∀ f, Opt.FunSimU f (T f)) {p : Clif.Program} {f : Clif.Function}
    {env : Clif.XEnv} (hE : Opt.EnvKeepsSymbolsX env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) (fuel : Nat) :
    ClifEntry (T f) args (passEntry T f cs) ∧
      (passEntry T f cs).frame.slots = cs.frame.slots ∧ (passEntry T f cs).mem = cs.mem ∧
      ∃ n', Opt.XOutcomeRefines (Clif.runLoopX env p fuel cs.toX)
        (Clif.runLoopX env (passProg T p) n' (passEntry T f cs).toX) := by
  obtain ⟨hcs', hsl, hmem, -⟩ :=
    pass_entry (fun f => (hU f).toX) (p := p) (env := env.toEnv) hE.toEnv hcs fuel
  exact ⟨hcs', hsl, hmem,
    Opt.runLoopX_refinesU hE (Opt.FunsSimU.map hU) fuel _ _ (clifEntry_passU hU hcs)⟩

/-- `pass_lift` with unwinding. -/
theorem pass_liftU (hU : ∀ f, Opt.FunSimU f (T f)) {p : Clif.Program} {f : Clif.Function}
    {env : Clif.XEnv} (hE : Opt.EnvKeepsSymbolsX env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) {R : Clif.XOutcome → Prop}
    (hR : ∀ o o', Opt.XOutcomeRefines o o' → R o' → R o)
    (h : ∀ n, R (Clif.runLoopX env (passProg T p) n (passEntry T f cs).toX)) (fuel : Nat) :
    R (Clif.runLoopX env p fuel cs.toX) := by
  obtain ⟨-, -, -, n', hn⟩ := pass_entryX hU (p := p) hE hcs fuel
  exact hR _ _ hn (h n')

/-! ## The theorems -/

/-- **End-to-end theorem over a pass** (`backend_correct_opt_exe` for any pass `T` whose output
simulates its input and keeps its shape): for an in-subset function `f` of `p`, the Arm run of
the compiled `T f` refines the CLIF run of the *source* program `p` from `f`'s entry state.
Premises: `backend_correct_final`'s about the compiled `T f`, externs keep the link-time symbols
(`hE`), and the transformed program's run traps only explicitly (`htr`). Non-vacuity:
`ConstPhiE2EWitness.pass_applies`. -/
theorem backend_correct_pass (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : Compiled (T f) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T f).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T f) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (T f)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entry hT hE hcs fuel (p := p)
  exact armRefines_of_outcome hn (backend_correct_final (inSubset_pass hS hsub) hc hcov hC hCT
    hTls (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_pass` for the backend with the dead-instruction cleanup**
(`CompiledCleanup`, `lean-backend`'s default). Non-vacuity: `ConstPhiE2EWitness.pass_cleanup_applies`. -/
theorem backend_correct_pass_cleanup (hT : ∀ f, Opt.FunSimX f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : CompiledCleanup (T f) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T f).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T f) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (T f)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entry hT hE hcs fuel (p := p)
  exact armRefines_of_outcome hn (backend_correct_final_cleanup (inSubset_pass hS hsub) hc hcov
    hC hCT hTls (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **The typed final theorem with the proven float operations over a pass**
(`backend_correct_finalTCF` composed with `T`): for `T f` in the typed scope (`InSubsetTCF` of
the transformed program) compiled by the typed pipeline (`CompiledTCF`), the Arm run of the
compiled `T f` refines the CLIF run of the *source* program `p` from `f`'s entry state, returned
values by class (`ArmRefinesT`). Premises: `backend_correct_finalTCF`'s about the compiled `T f`,
externs keep the link-time symbols (`hE`), the transformed program's run traps only explicitly
(`htr`). Non-vacuity: `ConstPhiE2EWitness.pass_finalTCF_applies`. -/
theorem backend_correct_pass_finalTCF (hT : ∀ f, Opt.FunSimX f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTCF (passProg T p) (T f)) (hc : CompiledTCF (T f) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T f).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T f) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (T f)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    ArmRefinesT fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entry hT hE hcs fuel (p := p)
  exact armRefinesT_of_outcome hn (backend_correct_finalTCF hsub hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **End-to-end theorem with unwinding over a pass** (`backend_correct_opt_exe_cleanup_unwind_any`
for any pass `T` whose output simulates its input with the handler edges and keeps its shape):
the Arm code compiled from `T f` through the dead cleanup, run on the machine with unwinding,
refines the run with unwinding of the *source* program from `f`'s entry (`ArmRefinesU`).
Non-vacuity: `ConstPhiE2EWitness.pass_unwind_applies`. -/
theorem backend_correct_pass_cleanup_unwind_any (hU : ∀ f, Opt.FunSimU f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : CompiledCleanup (T f) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (T f) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {Tb : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T f).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T f) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hUw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (T f)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (T f)) (fun sl cm w =>
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
    (htr : TrapsExplicitX env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U Tb fa) s (Clif.runLoopX env p fuel cs.toX) := by
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entryX hU hE hcs fuel (p := p)
  exact armRefinesU_of_outcome hn (backend_correct_final_cleanup_unwind_any
    (inSubset_pass hS hsub) hc hlU hcov hC hCT hTls hUw
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXR s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXRi s')
    hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_pass_cleanup_unwind_any` for the backend without the dead-instruction
cleanup** (`Compiled`, `backend_correct_final_unwind_any`). Non-vacuity:
`ConstPhiE2EWitness.pass_unwind_legacy_applies`. -/
theorem backend_correct_pass_unwind_any (hU : ∀ f, Opt.FunSimU f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f)
    (hc : Compiled (T f) k vc vcp rf af fa fb)
    (hunw : unwCheck (T f) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {Tb : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T f).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T f) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (T f)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (T f)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : ∀ s, XRaiseExcl env (f.externs.map (·.2)) (indSigs (T f))
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
    (hlsda : Tb.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : Tb.cie = cieInsns)
    (hfde : Tb.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U Tb fa) s (Clif.runLoopX env p fuel cs.toX) := by
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entryX hU hE hcs fuel (p := p)
  exact armRefinesU_of_outcome hn (backend_correct_final_unwind_any (inSubset_pass hS hsub)
    hc hunw hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXR s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXRi s')
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hXE s')
    hsym hslot hUnw hsites hlsda hpad hrows hcie hfde hsaved hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-! ## Legalisation, then the pass -/

/-- The source run of `f` refined by the (wide) legalisation's run, refined by the transformed
legalisation's run from the corresponding entry (`legal_opt_refines_wide` for `T`). -/
theorem legal_pass_refines_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (hT : ∀ f, Opt.FunSimX f (T f))
    {p p' : Clif.Program} {env : Clif.Env}
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
        Clif.runLoop env (passProg T p') n' (passEntry T g cs') = .returned vals' m) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → ∃ n',
      Clif.runLoop env (passProg T p') n' (passEntry T g cs') = .trapped c) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hEnv : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK, hind, hsigs⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hTr := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2⟩ := Opt.Legal.checkW_refines (C := C) hchk hEnv hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hTr hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst] at hr1 hr2
  rw [hst'] at hr1 hr2
  refine ⟨fun vals m hrun => ?_, fun c hrun => ?_⟩
  · obtain ⟨vals', hv, k, hk⟩ := hr1 vals m hrun
    obtain ⟨-, -, -, n', hn⟩ := pass_entry hT hE hcs' k (p := p')
    exact ⟨vals', hv, n', hn.1 _ _ hk⟩
  · obtain ⟨k, hk⟩ := hr2 c hrun
    obtain ⟨-, -, -, n', hn⟩ := pass_entry hT hE hcs' k (p := p')
    exact ⟨n', hn.2 _ hk⟩

/-- `ArmRefinesLegal` of the source outcome from the Arm refinement of every transformed run. -/
theorem armRefinesLegal_of_pass_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (hT : ∀ f, Opt.FunSimX f (T f))
    {p p' : Clif.Program} {env : Clif.Env}
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
      (Clif.runLoop env (passProg T p') n (passEntry T g cs'))) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra astep s
      (Clif.runLoop env p fuel cs) := by
  obtain ⟨hr1, hr2⟩ := legal_pass_refines_wide hchk hT hH hXL hK hE hext hext' hind hsigs hexp
    hcs hcs' hsl hmem hM htrS fuel
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

/-- **End-to-end theorem for an `i128` function legalised, then transformed by a pass**, any
environment with the contracts of `checkW_refines` keeping the link-time symbols
(`backend_correct_legal_opt_env_wide` for `T`). Non-vacuity: through
`backend_correct_legal_pass_wide` (`ConstPhiE2EWitness.legal_pass_applies`). -/
theorem backend_correct_legal_pass_env_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (hT : ∀ f, Opt.FunSimX f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled (T g) k vc vcp rf af fa fb)
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
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (T g)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (passProg T p') (passEntry T g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop env p fuel cs) := by
  have hF := hS g
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  refine armRefinesLegal_of_pass_wide hchk hT hH hXL hK hE hext hext' hind hsigs hexp hcs hcs' hsl
    hmem hM htrS (fun n => ?_) fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := pass_entry hT hE hcs' 0 (p := p')
  exact backend_correct_final (inSubset_pass hS hsub) hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs''
    (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n

/-- **`backend_correct_legal_pass_env_wide` for the backend with the dead-instruction cleanup.**
Non-vacuity: through `backend_correct_legal_pass_wide_cleanup`. -/
theorem backend_correct_legal_pass_env_wide_cleanup {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (hT : ∀ f, Opt.FunSimX f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup (T g) k vc vcp rf af fa fb)
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
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (T g)) (fun sl cm w =>
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
    (htr : TrapsExplicit env (passProg T p') (passEntry T g cs')) (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop env p fuel cs) := by
  have hF := hS g
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hrel
  refine armRefinesLegal_of_pass_wide hchk hT hH hXL hK hE hext hext' hind hsigs hexp hcs hcs' hsl
    hmem hM htrS (fun n => ?_) fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := pass_entry hT hE hcs' 0 (p := p')
  exact backend_correct_final_cleanup (inSubset_pass hS hsub) hc hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs''
    (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n

/-- **The end-to-end theorem for `i128` functions legalised, then transformed by a pass**, under
the trusted Rust environment `Clif.Rust.env` (`backend_correct_legal_opt_wide` for `T`).
Non-vacuity: `ConstPhiE2EWitness.legal_pass_applies`. -/
theorem backend_correct_legal_pass_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (hT : ∀ f, Opt.FunSimX f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : Compiled (T g) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs (T g)) (fun sl cm w =>
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
    (htr : TrapsExplicit Clif.Rust.env (passProg T p') (passEntry T g cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_pass_env_wide hchk hT hS hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext' hind
    (fun _ _ _ h => by cases h)
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_pass_wide` for the backend with the dead-instruction cleanup**
(`lean-backend`'s default). Non-vacuity: `ConstPhiE2EWitness.legal_pass_cleanup_applies`. -/
theorem backend_correct_legal_pass_wide_cleanup {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true) (hT : ∀ f, Opt.FunSimX f (T f))
    (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g)
    (hc : CompiledCleanup (T g) k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs (T g)) (fun sl cm w =>
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
    (htr : TrapsExplicit Clif.Rust.env (passProg T p') (passEntry T g cs'))
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) :=
  backend_correct_legal_pass_env_wide_cleanup hchk hT hS hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext' hind
    (fun _ _ _ h => by cases h)
    hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

/-- **End-to-end theorem with unwinding for an `i128` function legalised, then transformed by a
pass** (`backend_correct_legal_opt_unwind_env_any` for `T`), any environment with the contracts
of `check_refinesX` and `pass_entryX`. Non-vacuity: through `backend_correct_legal_pass_unwind_any`. -/
theorem backend_correct_legal_pass_unwind_env_any {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    (hUs : ∀ f, Opt.FunSimU f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup (T g) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (T g) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {Tb : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hE : Opt.Legal.X.EnvOkX env ⟨f, g, cert⟩ p p') (hEs : Opt.EnvKeepsSymbolsX env)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs (T g)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs (T g)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
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
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX env p cs)
    (htr : TrapsExplicitX env (passProg T p') (passEntry T g cs')) (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U Tb fa) s (Clif.runLoopX env p fuel cs.toX) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hF := hS g
  -- the transformed legalisation's Arm code refines every run with unwinding of `g`
  have hB : ∀ n, ArmRefinesU fb base ra (Unw.ArmStepU X H U Tb fa) s
      (Clif.runLoopX env p' n cs'.toX) := by
    intro n
    obtain ⟨hcs'', hsl', hmem', n', hn⟩ := pass_entryX hUs hEs hcs' n (p := p')
    exact armRefinesU_of_outcome hn (backend_correct_final_cleanup_unwind_any
      (inSubset_pass hS hsub)
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
  have hTr := noMemTrapX_of_trapsExplicitX htrS hcs.callers
  have hI := noIndInternalX_of_trapsExplicitX htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2, hr3⟩ := Opt.Legal.X.check_refinesX (C := C) hchk hexn hE hb hb' hcs.func h2 h3
    h4 h5 hcs'.func h2' h3' h5' hsl hexp hM hTr hI fuel
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

/-- **The end-to-end theorem with unwinding for `i128` functions legalised, then transformed by a
pass** (`backend_correct_legal_opt_unwind_any` for `T`), under the trusted Rust environment with
unwinding `Clif.Rust.xenvWith raises obj`. Non-vacuity: `ConstPhiE2EWitness.legal_pass_unwind_applies`. -/
theorem backend_correct_legal_pass_unwind_any {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true) (hexn : Opt.Legal.exnOk f g cert = true)
    (hUs : ∀ f, Opt.FunSimU f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hsub : InSubset p' g) (hc : CompiledCleanup (T g) k vc vcp rf af fa fb)
    (hlU : lowerCheckU (T g) vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {Tb : Unw.FnTables}
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
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk (Clif.Rust.xenvWith raises obj).toEnv (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk (Clif.Rust.xenvWith raises obj).toEnv (indSigs (T g))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.Rust.xenvWith raises obj) (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk (Clif.Rust.xenvWith raises obj) (indSigs (T g))
      (fun sl cm w =>
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X XR)
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
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicitX (Clif.Rust.xenvWith raises obj) p cs)
    (htr : TrapsExplicitX (Clif.Rust.xenvWith raises obj) (passProg T p') (passEntry T g cs'))
    (fuel : Nat) :
    ArmRefinesLegalU ((Opt.Legal.groups f.sig.returns).getD []) fb base ra
      (Unw.ArmStepU X H U Tb fa) s (Clif.runLoopX (Clif.Rust.xenvWith raises obj) p fuel cs.toX) :=
  backend_correct_legal_pass_unwind_env_any hchk hexn hUs hS hsub hc hlU
    (Clif.Rust.xenvWith_envOkX raises obj (C := ⟨f, g, cert⟩) (Opt.Legal.indOldB_of_check hchk)
      hext hext' hind)
    (xenvWith_keepsSymbolsX raises obj) hcov hC hCT hTls hU hX hXI hXR hXRi hsym hslot hsites hlsda
    hrows hcie hfde hpad hsaved hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel

end E2E

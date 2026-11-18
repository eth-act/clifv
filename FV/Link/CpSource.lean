import FV.Link.ConstPhiExe

/-! # The bundle's program through the `i128` legalisation and constant-phi removal (#1052)

`lean-link` compiles the constant-phi-removed input (`LinkSpec.cp`, `FnInput.cp`): a function the
pass changes is printed after the `i128` legalisation, every other one stays as the bundle wrote
it. So the source program of the compiled input (`LinkInput.srcProg`) is neither the bundle's
program nor its legalisation, and where a changed and an unchanged function meet at an `i128`
signature it is outside `SrcScopeB` (`declSigB`), although the bundle's program is in it
(`Link.ConstPhiSrcScopeWitness`).

This file states the source side about the **bundle's program** instead. For inputs `I0` (the
bundle's) and `I` whose functions are `I0`'s constant-phi removals (`I.funcs = I0.funcs.map
FnInput.cp`):

* `LinkInput.cpRel`: their programs are `OptRel`-related (`FnInput.cp_pair`, as
  `LinkSpec.cpRel`);
* `srcCtx_cp`: the source domain of `I0`'s program (`ProgCtx`), from `SrcScopeB I0` and the facts
  of the compiled program `I.prog` that the routes' checks establish (`names`, `free`, `declSig`,
  `indScope`), transferred back through `OptRel`;
* **`cpSource`**: a run of `I0`'s source program from `f`'s entry that returns (or traps without a
  load/store trap) is a run of the compiled program `I.prog` from the entry of its function named
  `f`'s name on the ABI-split arguments, with the results split by `f`'s return groups and the same
  memory (the same trap): the legalisation's refinement (`legalProg_refines`) composed with
  constant-phi removal's (`OptRel.refines`);
* **`cpSource_depth`**: the same, keeping the call depth (`legalProg_refines_depth`).

The routes' `…_sourceCp` theorems compose these with their `…_correct{,_peak}` theorems. The
refinement of constant-phi removal is proven over base environments keeping the link-time symbols
(`Opt.EnvKeepsSymbols`, as `cpRun`, `cp_lift` and `compileExeOpt_correct_source`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.LegalProgram Opt.Legalize128

/-- Two inputs whose functions are the constant-phi removals of each other's: their programs are
`OptRel`-related. -/
theorem _root_.E2E.LinkCheck.LinkInput.cpRel {I0 I : LinkInput}
    (hcp : I.funcs = I0.funcs.map FnInput.cp) : OptRel I0.prog I.prog := by
  show Opt.Pw2 OptPair (I0.funcs.map FnInput.func) (I.funcs.map FnInput.func)
  rw [hcp, List.map_map]
  generalize I0.funcs = l
  induction l with
  | nil => exact .nil
  | cons fi fs ih => exact .cons fi.cp_pair ih

/-- **The source domain of the bundle's program** from `SrcScopeB` of the bundle's input and the
compiled (constant-phi-removed, legalised) program's facts. -/
theorem srcCtx_cp {I0 I : LinkInput} (hcp : I.funcs = I0.funcs.map FnInput.cp)
    (hs : SrcScopeB I0 = true) {B : Clif.Env} {syms : String → Option Nat}
    (hnd : (I.prog.funcs.map (·.name)).Nodup) (hfree : ∀ g ∈ I.prog.funcs, Clif.LinkFree g)
    (hdecl : ∀ g ∈ I.prog.funcs, ∀ e ∈ g.externs.map (·.2), ∀ h,
      I.prog.func? e.name = some h → e.sig = h.sig)
    (hind : ∀ g ∈ I.prog.funcs, ¬ Clif.IndFree g → Clif.IndScope I.prog B syms)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B ∧ Opt.Legal.ExtLegal B ∧ Opt.Legal.EnvKeepsBounded B)
    (hsig : (∃ g ∈ I.prog.funcs, ¬ Clif.IndFree g) → ∀ n, B.sigOf n = none) :
    ProgCtx I0.srcProg B syms := by
  have hR := LinkInput.cpRel hcp
  refine srcCtx hs (hR.nodup hnd) (hR.free hfree) (hR.declSig hdecl) (hR.indScope hind) hlegal ?_
  rintro ⟨g, hg, hng⟩
  obtain ⟨g', hg', hp⟩ := hR.mem hg
  exact hsig ⟨g', hg', fun h => hng (indFreeB_sound (hp.2.indCall (indFree_of h)))⟩

/-- **The bundle's program refines through the legalisation and constant-phi removal**: on the
source domain of `I0`'s program, a run of it from `f`'s entry `cs` that returns is a return of the
compiled program `I.prog` (`I`'s functions: `I0`'s constant-phi removals) from the entry `cs'` of
its function `f'` named `f`'s name on the ABI-split arguments `args'`, with the results split by
`f`'s return groups and the same memory; a trap of a run without load/store traps is the same
trap. -/
theorem cpSource {I0 I : LinkInput} (hcp : I.funcs = I0.funcs.map FnInput.cp)
    {B : Clif.Env} {syms : String → Option Nat} (hC : ProgCtx I0.srcProg B syms)
    (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f f' : Clif.Function}
    (hf : I0.srcProg.func? n = some f) (hf' : I.prog.func? n = some f')
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args' cs')
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hsym : SomeInd (legalProg I0.srcProg) → cs.mem.symbols = syms)
    (hbnd : ∀ s', Opt.Legal.SReach B I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ∃ m, Clif.runLoop B I.prog m cs' = .returned vals' cm) ∧
    (Opt.Legal.NoMemTrap B I0.srcProg cs → ∀ c, Clif.runLoop B I0.srcProg M cs = .trapped c →
      ∃ m, Clif.runLoop B I.prog m cs' = .trapped c) := by
  have hR := LinkInput.cpRel hcp
  have hpe : I0.prog = legalProg I0.srcProg := LinkInput.prog_eq I0
  have hfP := (Clif.Program.func?_some hf).1
  have hfL : I0.prog.func? n = some (legalize f) := by rw [hpe]; exact hC.func?_some hf
  -- the entries: the compiled function's `cs'`, the legalisation's `csL`, the source's `cs`
  obtain ⟨csL, hcsL, -, hsL, hmL, -, hSR⟩ := hR.entry hfL hf' hcs'
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcsL.entry
  have hE : EntryRel f args args' cs.frame csL.frame :=
    ⟨hcs.func, hcsL.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩,
      by rw [hsL, hsl], hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hstL : (⟨csL.frame, [], cs.mem⟩ : Clif.State) = csL := by
    rw [← hcsL.callers, ← hmem, ← hmL]
  have hLe : Clif.LInv I0.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hsym' : SomeInd (legalProg I0.srcProg) → Opt.EnvKeepsSymbols B ∧ cs.mem.symbols = syms :=
    fun hI => ⟨hkeep, hsym hI⟩
  -- legal run → compiled run
  have hcpR : ∀ k, ∃ m,
      (∀ v cm, Clif.runLoop B (legalProg I0.srcProg) k csL = .returned v cm →
        Clif.runLoop B I.prog m cs' = .returned v cm) ∧
      (∀ c, Clif.runLoop B (legalProg I0.srcProg) k csL = .trapped c →
        Clif.runLoop B I.prog m cs' = .trapped c) := by
    intro k
    obtain ⟨m, h1, h2, -⟩ := hR.refines hkeep hSR k
    exact ⟨m, fun v cm hk => h1 v cm (by rw [hpe]; exact hk),
      fun c hk => h2 c (by rw [hpe]; exact hk)⟩
  refine ⟨fun vals cm hrun => ?_, fun hnmt c hrun => ?_⟩
  · have hG : GoodFrom B I0.srcProg (SomeInd (legalProg I0.srcProg)) syms
        ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym'
    rw [← hst] at hrun
    obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines hC hfP hE hG M).1 vals cm hrun
    rw [hstL] at hk
    obtain ⟨m, h1, -⟩ := hcpR k
    exact ⟨rv', hrel, m, h1 _ _ hk⟩
  · have hG : GoodFrom B I0.srcProg (SomeInd (legalProg I0.srcProg)) syms
        ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym'
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hstL] at hk
    obtain ⟨m, -, h2⟩ := hcpR k
    exact ⟨m, h2 _ hk⟩

/-- **`cpSource` keeping the call depth**: if the run of the bundle's program from `cs` has call
depth at most `d` (`Clif.DepthLe`), so has the compiled program's run from `cs'`. -/
theorem cpSource_depth {I0 I : LinkInput} (hcp : I.funcs = I0.funcs.map FnInput.cp)
    {B : Clif.Env} {syms : String → Option Nat} (hC : ProgCtx I0.srcProg B syms)
    (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f f' : Clif.Function}
    (hf : I0.srcProg.func? n = some f) (hf' : I.prog.func? n = some f')
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args' cs')
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hsym : SomeInd (legalProg I0.srcProg) → cs.mem.symbols = syms)
    (hbnd : ∀ s', Opt.Legal.SReach B I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    {d : Nat} (hd : Clif.DepthLe B I0.srcProg d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        (∃ m, Clif.runLoop B I.prog m cs' = .returned vals' cm) ∧
        Clif.DepthLe B I.prog d cs') ∧
    (Opt.Legal.NoMemTrap B I0.srcProg cs → ∀ c, Clif.runLoop B I0.srcProg M cs = .trapped c →
      (∃ m, Clif.runLoop B I.prog m cs' = .trapped c) ∧ Clif.DepthLe B I.prog d cs') := by
  have hR := LinkInput.cpRel hcp
  have hpe : I0.prog = legalProg I0.srcProg := LinkInput.prog_eq I0
  have hfP := (Clif.Program.func?_some hf).1
  have hfL : I0.prog.func? n = some (legalize f) := by rw [hpe]; exact hC.func?_some hf
  obtain ⟨csL, hcsL, -, hsL, hmL, -, hSR⟩ := hR.entry hfL hf' hcs'
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcsL.entry
  have hE : EntryRel f args args' cs.frame csL.frame :=
    ⟨hcs.func, hcsL.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩,
      by rw [hsL, hsl], hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hstL : (⟨csL.frame, [], cs.mem⟩ : Clif.State) = csL := by
    rw [← hcsL.callers, ← hmem, ← hmL]
  have hLe : Clif.LInv I0.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B I0.srcProg d ⟨cs.frame, [], cs.mem⟩ := by rw [hst]; exact hd
  have hsym' : SomeInd (legalProg I0.srcProg) → Opt.EnvKeepsSymbols B ∧ cs.mem.symbols = syms :=
    fun hI => ⟨hkeep, hsym hI⟩
  -- legal run (call depth `d`) → compiled run (call depth `d`)
  have hcpR : ∀ k, Clif.DepthLe B (legalProg I0.srcProg) d csL → ∃ m,
      (∀ v cm, Clif.runLoop B (legalProg I0.srcProg) k csL = .returned v cm →
        Clif.runLoop B I.prog m cs' = .returned v cm ∧ Clif.DepthLe B I.prog d cs') ∧
      (∀ c, Clif.runLoop B (legalProg I0.srcProg) k csL = .trapped c →
        Clif.runLoop B I.prog m cs' = .trapped c ∧ Clif.DepthLe B I.prog d cs') := by
    intro k hdL
    obtain ⟨m, h1, h2, h3⟩ := hR.refines hkeep hSR k
    rw [← hpe] at hdL
    refine ⟨m, fun v cm hk => ?_, fun c hk => ?_⟩
    · rw [← hpe] at hk
      exact ⟨h1 v cm hk, h3 (by rw [hk]; trivial) d hdL⟩
    · rw [← hpe] at hk
      exact ⟨h2 c hk, h3 (by rw [hk]; trivial) d hdL⟩
  refine ⟨fun vals cm hrun => ?_, fun hnmt c hrun => ?_⟩
  · have hG : GoodFrom B I0.srcProg (SomeInd (legalProg I0.srcProg)) syms
        ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym'
    rw [← hst] at hrun
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdL⟩ :=
      (legalProg_refines_depth hC hfP hE hG hd' M).1 vals cm hrun
    rw [hstL] at hk hdL
    obtain ⟨m, h1, -⟩ := hcpR k hdL
    obtain ⟨hm, hdO⟩ := h1 _ _ hk
    exact ⟨rv', hrel, ⟨m, hm⟩, hdO⟩
  · have hG : GoodFrom B I0.srcProg (SomeInd (legalProg I0.srcProg)) syms
        ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym'
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdL⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hstL] at hk hdL
    obtain ⟨m, -, h2⟩ := hcpR k hdL
    obtain ⟨hm, hdO⟩ := h2 _ hk
    exact ⟨⟨m, hm⟩, hdO⟩

end Link

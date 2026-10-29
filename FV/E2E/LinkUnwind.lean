import FV.E2E.FinalUnwind
import FV.E2E.Link
import FV.Clif.LinkClifX

/-!
# Linking with unwinding: the end-to-end theorem against the whole-program runs with unwinding
(S10f, #233)

`docs/plans/unwinding.md` §4; `FV/E2E/Link.lean`'s counterpart. `backend_correct_final_unwind`
(`FV/E2E/FinalUnwind.lean`) is per function: the Arm code of `f` on the machine with unwinding
refines `Clif.runLoopX env (P.only f)`, assuming the callees' contracts, normal
(`XCallsOk env.toEnv`) and exceptional (`XRaiseOk env`, `XRaiseExcl env`).

* `Clif.runLoopX_link` (`FV/Clif/LinkClifX.lean`): a whole-program run with unwinding is a
  per-function run of `P.only f` under `Clif.linkEnvX P env` (a call of another function `g` of
  `P` is atomic: `g`'s whole-program run with unwinding, whose `unwound` outcome is raised at the
  call).
* `armRefinesU_link`: per-function refinement for every fuel ⇒ whole-program refinement.
* **`backend_correct_linked_unwind`**: the Arm code of `f` refines the **whole-program** run
  with unwinding `Clif.runLoopX env P fuel cs.toX`, from `backend_correct_final_unwind`'s
  premises at `env := Clif.linkEnvX P env`, `p := P.only f`; **`backend_correct_linked_unwind_any`**
  without the check `lastCallsOk` (#622; the former is its corollary).
* `xCallsOk_linkX`, `xRaiseOk_linkX`, `xRaiseExcl_linkX` split the callee contracts of the linked
  environment into the base environment's (externs outside `P`) and the program functions';
  `xCallsOk_progX`, `xRaiseOk_progX`, `xRaiseExcl_progX` state the program functions' part on
  the callees' whole-program runs with unwinding (`Clif.runLimX` from their entry states):
  a call of `g` that returns relates to `g`'s run returning, a raise to `g`'s run ending
  `unwound`. As in `backend_correct_linked`, these program-callee contracts stay premises (the
  Arm-level linking step discharging them from each callee's own theorem is open).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables

/-! ## Whole-program refinement from per-function refinement -/

/-- An entry state of a function of `P` satisfies the invariant of `Clif.runLoopX_link`. -/
theorem xinv_entry {P : Clif.Program} {f : Clif.Function} {args : List Clif.Val}
    {cs : Clif.State} (hf : f ∈ P.funcs) (hcs : ClifEntry f args cs) : Clif.XInv P cs.toX :=
  ⟨runInv_entry hf hcs, by simp [Clif.XState.Aligned, Clif.State.toX]⟩

/-- **Whole-program refinement with unwinding from per-function refinement**. -/
theorem armRefinesU_link {P : Clif.Program} {env : Clif.XEnv} {f : Clif.Function}
    (hP : Linkable P) (hf : f ∈ P.funcs) {xs : Clif.XState} (hinv : Clif.XInv P xs)
    {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    (h : ∀ m, ArmRefinesU fb base ra astep s
      (Clif.runLoopX (Clif.linkEnvX P env) (P.only f) m xs))
    (fuel : Nat) : ArmRefinesU fb base ra astep s (Clif.runLoopX env P fuel xs) := by
  have hlink := Clif.runLoopX_link (env := env) hP.names hf hP.free hP.indFree fuel xs hinv
  cases ho : Clif.runLoopX env P fuel xs with
  | stuck m => trivial
  | outOfFuel => trivial
  | returned vals mem =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h)
      (by rw [ho]; exact fun h => nomatch h)
    have := h m
    rwa [hm, ho] at this
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h)
      (by rw [ho]; exact fun h => nomatch h)
    have := h m
    rwa [hm, ho] at this
  | unwound e mem =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h)
      (by rw [ho]; exact fun h => nomatch h)
    have := h m
    rwa [hm, ho] at this

/-! ## The callee contracts of a linked function -/

section
variable {P : Clif.Program} {env : Clif.XEnv} {exts : List Clif.ExtFunc} {MR : MemRelT}
  {X : ExtSem} {XR : XRaise}

/-- The normal-return contract of the linked environment splits into the base environment's
(externs outside `P`) and the program functions'. -/
theorem xCallsOk_linkX
    (hbase : XCallsOk env.toEnv (exts.filter fun e => (P.func? e.name).isNone) MR X)
    (hprog : XCallsOk (Clif.linkEnvX P env).toEnv (exts.filter fun e => (P.func? e.name).isSome)
      MR X) :
    XCallsOk (Clif.linkEnvX P env).toEnv exts MR X := by
  intro ext hin g sl cm w d uses args vals rvals cm' hg
  cases hpf : P.func? ext.name with
  | none =>
    rw [Clif.linkEnvX_toEnv_none hpf] at hg
    exact hbase ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals cm'
      hg
  | some _ =>
    exact hprog ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals
      cm' hg

/-- The exceptional-result contract of the linked environment splits likewise. -/
theorem xRaiseOk_linkX
    (hbase : XRaiseOk env (exts.filter fun e => (P.func? e.name).isNone) MR X XR)
    (hprog : XRaiseOk (Clif.linkEnvX P env) (exts.filter fun e => (P.func? e.name).isSome) MR X
      XR) :
    XRaiseOk (Clif.linkEnvX P env) exts MR X XR := by
  intro ext hin g sl cm w d uses args vals e m hg
  cases hpf : P.func? ext.name with
  | none =>
    rw [Clif.linkEnvX_none hpf] at hg
    exact hbase ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals e m hg
  | some _ =>
    exact hprog ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals e m hg

/-- The exclusivity of the linked environment splits likewise (no indirect calls). -/
theorem xRaiseExcl_linkX
    (hbase : XRaiseExcl env (exts.filter fun e => (P.func? e.name).isNone) [] MR X XR)
    (hprog : XRaiseExcl (Clif.linkEnvX P env) (exts.filter fun e => (P.func? e.name).isSome) []
      MR X XR) :
    XRaiseExcl (Clif.linkEnvX P env) exts [] MR X XR := by
  refine ⟨fun ext hin g sl cm w d uses args vals rvals cm' hg => ?_, fun _ h => nomatch h⟩
  cases hpf : P.func? ext.name with
  | none =>
    rw [Clif.linkEnvX_none hpf] at hg
    exact hbase.1 ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals
      cm' hg
  | some _ =>
    exact hprog.1 ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals
      cm' hg

/-- The linked environment's extern of a function `g` of `P` on `vals` from `cm`: `g`'s
whole-program run with unwinding from its entry state. -/
theorem linkEnvX_prog_run {n : String} {G : List Clif.Val → Clif.Mem → Clif.XOutcome}
    (hG : (Clif.linkEnvX P env).extern n = some G) (hn : (P.func? n).isSome = true)
    (vals : List Clif.Val) (cm : Clif.Mem) {o : Clif.XOutcome} (ho : G vals cm = o)
    (hne : ∀ c, o ≠ .trapped c) (hns : ∀ msg, o ≠ .stuck msg) :
    ∃ s, Clif.initState P n vals cm = .ok s ∧ Clif.runLimX env P s.toX = o := by
  obtain ⟨g, hpf⟩ := Option.isSome_iff_exists.mp hn
  rw [Clif.linkEnvX_some hpf] at hG
  cases hG
  dsimp only at ho
  cases hi : Clif.initState P n vals cm with
  | ok s => rw [hi] at ho; exact ⟨s, rfl, ho⟩
  | trap c => rw [hi] at ho; exact absurd ho.symm (hne c)
  | stuck msg => rw [hi] at ho; exact absurd ho.symm (hns msg)

/-- **The program callees' exceptional contract, on their runs**: a call of a function of `P`
whose whole-program run with unwinding from its entry state ends `unwound e m` raises an object
related to `e`, the world after the unwinder related to `m`. -/
theorem xRaiseOk_progX
    (h : ∀ ext ∈ exts.filter (fun e => (P.func? e.name).isSome), ∀ (sl : List (Clif.SlotId × Nat))
      (cm : Clif.Mem) (w : Arm.ArmState) (d : Option String) (uses args : List CV)
      (vals : List Clif.Val) (s : Clif.State) (e : Clif.Exn) (m : Clif.Mem),
      Clif.initState P ext.name vals cm = .ok s →
      (d = some ext.name ∧ uses = args ∨
        d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) →
      ArgsAt ext.sig vals args w → MR sl cm w → Clif.runLimX env P s.toX = .unwound e m →
      ∃ obj w', XR.raise d uses w = some (obj, w') ∧ ExnRel e obj ∧ MR sl m w') :
    XRaiseOk (Clif.linkEnvX P env) (exts.filter fun e => (P.func? e.name).isSome) MR X XR := by
  intro ext hin g sl cm w d uses args vals e m hg hd hargs hmr hu
  obtain ⟨s, hi, hr⟩ := linkEnvX_prog_run hg (List.mem_filter.mp hin).2 vals cm hu
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  exact h ext hin sl cm w d uses args vals s e m hi hd hargs hmr hr

/-- **The program callees' normal-return contract, on their runs**. -/
theorem xCallsOk_progX
    (h : ∀ ext ∈ exts.filter (fun e => (P.func? e.name).isSome), ∀ (sl : List (Clif.SlotId × Nat))
      (cm : Clif.Mem) (w : Arm.ArmState) (d : Option String) (uses args : List CV)
      (vals : List Clif.Val) (s : Clif.State) (rvals : List Clif.Val) (cm' : Clif.Mem),
      Clif.initState P ext.name vals cm = .ok s →
      (d = some ext.name ∧ uses = args ∨
        d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) →
      ArgsAt ext.sig vals args w → MR sl cm w → Clif.runLimX env P s.toX = .returned rvals cm' →
      rvals.length = ext.sig.returns.length →
      ∃ outs w', X.call d uses w = some (outs, w') ∧ outs.length = (sigRets ext.sig).length ∧
        PrefixHold rvals outs ∧ MR sl cm' w') :
    XCallsOk (Clif.linkEnvX P env).toEnv (exts.filter fun e => (P.func? e.name).isSome) MR X := by
  intro ext hin g sl cm w d uses args vals rvals cm' hg hd hargs hmr hret hrl
  simp only [Clif.XEnv.toEnv, Option.map_eq_some_iff] at hg
  obtain ⟨G, hG, rfl⟩ := hg
  have hr : G vals cm = .returned rvals cm' := by
    dsimp only at hret
    cases ho : G vals cm with
    | returned v m =>
      rw [ho] at hret
      simp only [Clif.XOutcome.toOutcome, Clif.Outcome.returned.injEq] at hret
      rw [hret.1, hret.2]
    | _ => rw [ho] at hret; simp [Clif.XOutcome.toOutcome] at hret
  obtain ⟨s, hi, hrun⟩ := linkEnvX_prog_run hG (List.mem_filter.mp hin).2 vals cm hr
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  exact h ext hin sl cm w d uses args vals s rvals cm' hi hd hargs hmr hrun hrl

/-- **The program callees' exclusivity, on their runs**: a call of a function of `P` whose
whole-program run returns does not raise. -/
theorem xRaiseExcl_progX
    (h : ∀ ext ∈ exts.filter (fun e => (P.func? e.name).isSome), ∀ (sl : List (Clif.SlotId × Nat))
      (cm : Clif.Mem) (w : Arm.ArmState) (d : Option String) (uses args : List CV)
      (vals : List Clif.Val) (s : Clif.State) (rvals : List Clif.Val) (cm' : Clif.Mem),
      Clif.initState P ext.name vals cm = .ok s →
      (d = some ext.name ∧ uses = args ∨
        d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) →
      ArgsAt ext.sig vals args w → MR sl cm w → Clif.runLimX env P s.toX = .returned rvals cm' →
      XR.raise d uses w = none) :
    XRaiseExcl (Clif.linkEnvX P env) (exts.filter fun e => (P.func? e.name).isSome) [] MR X XR := by
  refine ⟨fun ext hin g sl cm w d uses args vals rvals cm' hg hd hargs hmr hr => ?_,
    fun _ h => nomatch h⟩
  obtain ⟨s, hi, hrun⟩ := linkEnvX_prog_run hg (List.mem_filter.mp hin).2 vals cm hr
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  exact h ext hin sl cm w d uses args vals s rvals cm' hi hd hargs hmr hrun

end

theorem xRaiseIndOk_nil (env : Clif.XEnv) (MR : MemRelT) (X : ExtSem) (XR : XRaise) :
    XRaiseIndOk env [] MR X XR := fun _ h => nomatch h

/-! ## The linked theorem with unwinding -/

/-- **`backend_correct_linked_unwind` without the check on the calls of the last block** (#622;
`backend_correct_final_unwind_any`). Non-vacuity: as `backend_correct_linked_unwind` (the
witnesses below; its premises are among `backend_correct_linked_unwind`'s). -/
theorem backend_correct_linked_unwind_any {P : Clif.Program} {env : Clif.XEnv}
    {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hP : Linkable P) (hf : f ∈ P.funcs)
    (hsub : InSubset (P.only f) f) (hc : Compiled f k vc vcp rf af fa fb)
    (hunw : unwCheck f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk (Clif.linkEnvX P env).toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.linkEnvX P env) (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : ∀ s, XRaiseExcl (Clif.linkEnvX P env) (f.externs.map (·.2)) [] (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hUnw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX (Clif.linkEnvX P env) (P.only f) cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env P fuel cs.toX) := by
  have hnil := indSigs_nil_of_indFree (hP.indFree f hf)
  refine armRefinesU_link hP hf (xinv_entry hf hcs) (fun m => ?_) fuel
  exact backend_correct_final_unwind_any hsub hc hunw hcov hC hCT hTls hX
    (fun _ => by rw [hnil]; exact xCallsIndOk_nil _ _ _) hXR
    (fun _ => by rw [hnil]; exact xRaiseIndOk_nil _ _ _ _) (fun s' => by rw [hnil]; exact hXE s')
    hsym hslot hUnw hsites hlsda hpad hrows hcie hfde hsaved hent hres hbe hargs hcs hrel htr m

/-- **The backend's end-to-end theorem with unwinding against the whole program**: for a
function `f` of a program `P` (`Linkable`) compiled from its own file `P.only f`, the Arm run on
the machine with unwinding refines the **whole-program** CLIF run with unwinding
`Clif.runLoopX env P` (calls and `try_call`s of functions of `P` enter them; an exception
propagates through their frames by their pending tables): returns and traps as
`backend_correct_linked`, and a run that ends by an exception is an Arm return to the caller with
the exception object in x0 and the memory agreeing. The premises are
`backend_correct_final_unwind`'s at `env := Clif.linkEnvX P env`, `p := P.only f`: the callee
contracts for a call of a function `g` of `P` are about `g`'s whole-program run with unwinding
(`xCallsOk_linkX`/`xRaiseOk_linkX`/`xRaiseExcl_linkX` with `xCallsOk_progX`/`xRaiseOk_progX`/
`xRaiseExcl_progX`); the indirect-call contracts are vacuous (`Linkable`). Statement kept for its
callers; `backend_correct_linked_unwind_any` drops `lastCallsOk`. -/
theorem backend_correct_linked_unwind {P : Clif.Program} {env : Clif.XEnv} {f : Clif.Function}
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hP : Linkable P) (hf : f ∈ P.funcs)
    (hsub : InSubset (P.only f) f) (hc : Compiled f k vc vcp rf af fa fb)
    (hunw : unwCheck f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk (Clif.linkEnvX P env).toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk (Clif.linkEnvX P env) (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : ∀ s, XRaiseExcl (Clif.linkEnvX P env) (f.externs.map (·.2)) [] (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hUnw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (_hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX (Clif.linkEnvX P env) (P.only f) cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env P fuel cs.toX) :=
  backend_correct_linked_unwind_any hP hf hsub hc hunw hcov hC hCT hTls hX hXR hXE hsym hslot hUnw
    hsites hlsda hpad hrows hcie hfde hsaved hent hres hbe hargs hcs hrel htr fuel

/-! ## Non-vacuity

The program callees' exceptional contract (`xRaiseOk_progX`) holds for a program whose callees do
raise: in the environment in which every extern unwinds with a Rust panic (object 77,
`IselSimUWitness.env`), an exception that leaves a function of `P` is that panic
(`Clif.runLimX_unwound_only`), so a raising callee `XR` reporting object 77 meets it, for every
program `P`; and `%mid` of `Clif.UnwindWitness.prog` (which calls an extern) does end
`unwound` with the panic's payload. With `Clif.UnwindLinkWitness.link_caught` (the linking step
itself on a run where an exception leaves a program callee and is caught) and
`backend_correct_final_unwind_premises` (the per-function premises), the premise groups of
`backend_correct_linked_unwind` are satisfiable with raising callees. -/

namespace LinkUnwindWitness

theorem env_raisesOnly : IselSimUWitness.env.RaisesOnly (IselSimUWitness.exn 77) := by
  intro n g hg vals mem e m hu
  simp only [IselSimUWitness.env, Option.some.injEq] at hg
  subst hg
  simp only [Clif.XOutcome.unwound.injEq] at hu
  exact hu.1.symm

/-- The program callees' exceptional contract holds in the panic environment (memory relation
unconstrained), for every program. -/
theorem xRaiseOk_prog (P : Clif.Program) (exts : List Clif.ExtFunc) (X : ExtSem) :
    XRaiseOk (Clif.linkEnvX P IselSimUWitness.env) (exts.filter fun e => (P.func? e.name).isSome)
      (fun _ _ _ => True) X IselSimUWitness.XR :=
  xRaiseOk_progX fun _ _ _ _ w _ _ _ _ _ _ _ _ _ _ _ hr =>
    ⟨77, w, rfl, by rw [Clif.runLimX_unwound_only env_raisesOnly P hr]; exact IselSimUWitness.exnRel,
      trivial⟩

/-- `%mid` (a function of the witness program calling an extern) ends `unwound` with the panic's
payload in the panic environment. -/
theorem mid_raises :
    (Clif.runX IselSimUWitness.env Clif.UnwindWitness.prog "mid" [⟨.i64, 5⟩] 20).unwoundPayload? =
      some [⟨.i64, 77⟩, ⟨.i64, 0⟩] := by
  decide +kernel

end LinkUnwindWitness

end E2E

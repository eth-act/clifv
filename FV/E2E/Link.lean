import FV.E2E.Final
import FV.E2E.LinkClif

/-! # Linking: the end-to-end theorem against the whole-program CLIF semantics

`cargo fv` compiles every function `f` of a program `P` as its own CLIF file `P.only f`, in
which every other function of `P` is an extern. `backend_correct_final` is per function: the
Arm code of `f` refines `Clif.runLoop env (P.only f)`, assuming its callees meet the contracts
`CalleeOk` (the machine's call hook) and `XCallsOk env` (the external semantics).

* `Clif.runLoop_link` (`FV/E2E/LinkClif.lean`): a whole-program run `Clif.runLoop base P`
  (`call`s and `try_call`s of functions of `P` enter them) that returns or traps is a per-function run of
  `P.only f` under `Clif.linkEnv P base` (a call of another function `g` of `P` is atomic and
  returns what `g`'s whole-program run returns).
* `armRefines_link`: per-function refinement for every fuel ⇒ whole-program refinement.
* **`backend_correct_linked`**: the Arm code of `f` refines the **whole-program** run
  `Clif.runLoop base P fuel cs`, from the premises of `backend_correct_final` at
  `env := Clif.linkEnv P base`, `p := P.only f`. `xCallsOk_link` splits the external contract into
  the base environment's (externs outside `P`) and the program functions' (`linkEnv`).
* The program callees' contracts `hC`/`hX` stay premises: discharging them from each callee's
  own theorem (the Arm-level linking step) is open (docs/contracts/e2e.md, "Linking"). They are
  satisfiable by callees that push a frame below `sp` (`E2E.calleeOk_nonLeaf`,
  `FV/E2E/NonVacuity.lean`): the callee contract leaves the callees' dead stack (`K` bytes below
  the caller's `sp`) unspecified.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The program conditions -/

/-- The programs the linking theorem covers: distinct function names, and no `call_indirect`,
`try_call_indirect` or `return_call` in any function (`Clif.LinkFree`; `call` and `try_call`
are allowed). -/
structure Linkable (P : Clif.Program) : Prop where
  names : (P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ P.funcs, Clif.LinkFree g

/-- An entry state of a function of `P` satisfies the run invariant of `Clif.runLoop_link`. -/
theorem runInv_entry {P : Clif.Program} {f : Clif.Function} {args : List Clif.Val}
    {cs : Clif.State} (hf : f ∈ P.funcs) (hcs : ClifEntry f args cs) :
    Clif.LInv P cs := by
  obtain ⟨b, hb, hbody, hterm, -, -⟩ := hcs.entry
  refine ⟨⟨by rw [hcs.func]; exact hf, .inl ⟨b, ?_, ?_, hterm⟩⟩, ?_⟩
  · rw [hcs.func]; exact List.mem_of_mem_head? hb
  · rw [hbody]; exact List.suffix_refl _
  · rw [hcs.callers]; exact fun _ h => nomatch h

/-- **Whole-program refinement from per-function refinement**: if the Arm run refines every
per-function run of `f` under the linked environment, it refines the whole-program run. -/
theorem armRefines_link {P : Clif.Program} {baseEnv : Clif.Env} {f : Clif.Function}
    (hP : Linkable P) (hf : f ∈ P.funcs) {cs : Clif.State} (hinv : Clif.LInv P cs)
    {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    (h : ∀ m, ArmRefines fb base ra astep s (Clif.runLoop (Clif.linkEnv P baseEnv) (P.only f) m cs))
    (fuel : Nat) : ArmRefines fb base ra astep s (Clif.runLoop baseEnv P fuel cs) := by
  have hlink := Clif.runLoop_link (base := baseEnv) hP.names hf hP.free fuel cs hinv
  cases ho : Clif.runLoop baseEnv P fuel cs with
  | stuck m => trivial
  | outOfFuel => trivial
  | returned vals mem =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    have := h m
    rwa [hm, ho] at this
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    have := h m
    rwa [hm, ho] at this

/-! ## The external contract of a linked function -/

/-- The external contract of the linked environment splits into the base environment's for the
externs that are not functions of `P` and the linked one for the program functions. -/
theorem xCallsOk_link {P : Clif.Program} {baseEnv : Clif.Env} {exts : List Clif.ExtFunc}
    {MR : MemRelT} {X : ExtSem}
    (hbase : XCallsOk baseEnv (exts.filter fun e => (P.func? e.name).isNone) MR X)
    (hprog : XCallsOk (Clif.linkEnv P baseEnv) (exts.filter fun e => (P.func? e.name).isSome) MR X) :
    XCallsOk (Clif.linkEnv P baseEnv) exts MR X := by
  intro ext hin g sl cm w d uses args vals rvals cm' hg
  cases hpf : P.func? ext.name with
  | none =>
    rw [Clif.linkEnv_none hpf] at hg
    exact hbase ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals cm' hg
  | some _ =>
    exact hprog ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals cm' hg

/-- A function without `call_indirect`/`try_call_indirect` has no indirect-call signatures. -/
theorem indSigs_nil_of_linkFree {f : Clif.Function} (h : Clif.LinkFree f) : indSigs f = [] :=
  indSigs_eq_nil (fun B hB st hst sig callee args => (h B hB).1 st hst sig callee args)
    (fun B hB callee args et => (h B hB).2.1 callee args et)

/-! ## The linked theorem -/

/-- **The backend's end-to-end theorem against the whole program** (`docs/contracts/e2e.md`,
"Linking"): for a function `f` of a program `P` (`Linkable`: distinct names, no indirect calls
or `return_call`) compiled from its own file `P.only f`, the Arm run refines the
**whole-program** CLIF run `Clif.runLoop base P` (calls and `try_call`s of functions of `P`
enter them). The premises are `backend_correct_final`'s at `env := Clif.linkEnv P base`,
`p := P.only f`: in particular the external contract `hX` for a call of a function `g` of `P` is
the CLIF semantics of `g`'s whole-program run (`xCallsOk_link` separates it from the base
environment's). The indirect-call contract is vacuous (`Linkable`). -/
theorem backend_correct_linked {P : Clif.Program} {baseEnv : Clif.Env} {f : Clif.Function}
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hP : Linkable P) (hf : f ∈ P.funcs)
    (hsub : InSubset (P.only f) f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.CallSite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk (Clif.linkEnv P baseEnv) (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit (Clif.linkEnv P baseEnv) (P.only f) cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop baseEnv P fuel cs) := by
  refine armRefines_link hP hf (runInv_entry hf hcs) (fun m => ?_) fuel
  exact backend_correct_final hsub hc hcov hC hCT hTls hX
    (fun _ => by rw [indSigs_nil_of_linkFree (hP.free f hf)]; exact xCallsIndOk_nil _ _ _) hsym
    hslot hent hres hbe hargs hcs hrel htr m

end E2E

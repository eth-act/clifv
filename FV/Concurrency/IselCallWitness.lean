import FV.Concurrency.IselCall
import FV.Concurrency.RealizeWitness
import FV.Concurrency.IselRefinesWitness
import FV.Concurrency.CallLoadData

/-!
# Witness: layer 2 pausing at calls (#473, (2a))

* `driverHypT_of`: `DriverHypT` and the check admitting calls for a checked function whose
  externs are not the environment's (its calls are calls of program functions);
* the caller `CallSeg.WitnessC.fC` (`v1 = call fn0(v0); return v1`, `fn0 = colocated %ld`) as
  the driver lowers it: `threadCheck` rejects it (`checksFC`), `threadCheckC` accepts it, and
  **`isel_pause_fC`**: every premise of `IselCall.isel_pauseC` holds for it in the program
  `pCL` (the caller and the compiled `atomic_load`) but the CLIF entry state, its relation to the
  entry world, the arguments and the run; `atCall_csC`: its CLIF entry state is at the call.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.IselCall.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  IselThread ThreadRefine E2E ClifCStepTerm RealizeCompiled.Witness IselRefines.Witness
  CallSeg.WitnessC

/-- A program without functions. -/
def pNil : Clif.Program := { funcs := [] }

/-- A checked function is in the subset of the program without functions. -/
theorem inSubset_nil {f : Clif.Function} (hv : verifiable f = true) : InSubset pNil f := by
  simp only [verifiable, abiSigs, indSigsOk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_assoc] at hv
  obtain ⟨hE, hf, hext', hind⟩ := hv
  exact ⟨hE, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ⟨hf, hext'⟩, hind⟩

/-- **`DriverHypT` and the check admitting calls for a checked function** (module doc;
`RealizeCompiled.Witness.driverHyp_of`'s construction). -/
theorem driverHypT_of {f : Clif.Function} {vc : VCode} {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem}
    {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    (hlow : lowerCheck f vc = true) (hthr : IselCheck.threadCheckC f = true)
    (hext : ∀ e ∈ f.externs, env.extern e.2.name = none) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A, DriverHypT f vc ctx st0 R gn bl A (csem Γ.F fctx X) (RelW Γ f c) env p ∧
      IselCheck.threadCheckBlC f bl = true := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl⟩ :=
    IselCheck.obligations_of_threadCheckC hlow hthr
  have hsub := inSubset_nil hv
  have hX : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X := by
    intro ext hmem g _ _ _ _ _ _ _ _ _ hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
    rw [hext e he] at hg; cases hg
  have hXI : XCallsIndOk env (indSigs f) (RelW Γ f c) X := by
    rw [hind]; intro s h; cases h
  have hRef : Refines Γ.F (csem Γ.F fctx X) := refines_csem Γ.F fctx X
  have hmem : MemRefines Γ.F Γ.slotOff Γ.syms (csem Γ.F fctx X) :=
    memRefines_csem Γ.F fctx X hslot hsym
  have hcalls := callsRefine_csem (F := Γ.F) (ctx := fctx) hX
  have hicalls := indCallsRefine_csem (F := Γ.F) (ctx := fctx) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB : vc.outgoing ≤ Γ.out := by rw [hout0]; exact Nat.zero_le _
  refine ⟨ctx, st0, R, gn, bl, A, {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem Γ.F fctx X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hlow) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hlow) houtB⟩
    tryExt := fun B hB fn args et ht => by
      have := List.all_eq_true.mp hnt B hB
      rw [ht] at this; cases this
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef
      (mrStable_relW Γ f c) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := hcfg }, hbl⟩

/-! ## The caller of `atomic_load` -/

theorem checksFC : lowerCheck fC vcC = true ∧ IselCheck.threadCheckC fC = true ∧
    IselCheck.threadCheck fC = false ∧ fC.externs.map (·.2.name) = ["ld"] ∧
    (indSigs fC).isEmpty = true ∧ verifiable fC = true ∧
    fC.blocks.all (fun B => !B.term.isTry) = true ∧
    IselThread.Witness.isOkB vcC.cfg = true ∧ vcC.outgoing = 0 ∧
    (locsOf fC.sig).all (fun l => match l with | .stack _ => false | _ => true) = true := by
  native_decide

theorem cfgFC : ∃ ss ps, vcC.cfg = .ok (ss, ps) := by
  have h := checksFC.2.2.2.2.2.2.2.1
  revert h
  cases vcC.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

theorem fC_reg : ∀ off, ArgLoc.stack off ∉ locsOf fC.sig := by
  intro off hm
  have := List.all_eq_true.mp checksFC.2.2.2.2.2.2.2.2.2 _ hm
  simp at this

/-- The caller's CLIF entry state is at its call. -/
theorem atCall_csC : AtCallS csC :=
  ⟨_, [], 0, [0], by rw [show csC.frame.body = B0C.body from rfl, clifC.1], rfl⟩

/-- **Layer 2 from the caller's entry, pausing at its call** (module doc): with an environment
without the extern `ld` (`ld` is a function of `pCL`). -/
theorem isel_pause_fC {Γ : E2E.Rel} {fctx : FnCtx} {c : BitVec 64} {env : Clif.Env}
    (henv : env.extern "ld" = none) (hc : c.toNat % 16 = 0) (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → VCodeThread.Witness.X0.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A,
      DriverHypT fC vcC ctx st0 R gn bl A (csem Γ.F fctx VCodeThread.Witness.X0) (RelW Γ fC c)
        env pCL ∧
      ∀ (slots : List (Clif.SlotId × Nat)) (cs : Clif.State) (B0 : Clif.Block)
        (args : List Clif.Val) (ρ₀ : Nat → CV) (w₀ : ArmState) (tr : List (List Ev))
        (cT : VConf CV ArmState),
        fC.blocks[0]? = some B0 → cs.callers = [] → cs.frame.func = fC →
        cs.frame.slots = slots → cs.frame.body = B0.body → cs.frame.term = B0.term →
        Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs →
        args.map (·.ty) = B0.params.map (·.2) → args.map (·.ty) = fC.sig.params.map (·.ty) →
        RelW Γ fC c slots cs.mem w₀ → ArgsAtEntry Γ.F fC.sig args w₀ →
        VTRun vcC (csem Γ.F fctx VCodeThread.Witness.X0) (cEvs Γ.F fctx) (.run ⟨0, 0, ρ₀, w₀⟩)
          tr cT →
        ∃ n trS t ψ, n ≤ tr.length ∧ CRun env pCL (.run cs) trS t ∧
          Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
          ((((n = tr.length ∧ ∃ c', VStep vcC (csem Γ.F fctx VCodeThread.Witness.X0) cT c') ∨
              Stop env pCL t) ∧ ∀ v, t = .ret v → n = tr.length) ∨
            n = tr.length ∧ ∃ s' vs', t = .run s' ∧ AtCallS s' ∧ cT = .run vs' ∧
              Match fC ctx R gn bl A (RelW Γ fC c) slots s' vs') := by
  obtain ⟨hlow, hthr, -, hnames, hind, hv, hnt, -, hout0, -⟩ := checksFC
  have hext : ∀ e ∈ fC.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames, List.mem_singleton] at this
    rw [this]; exact henv
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverHypT_of (Γ := Γ) (fctx := fctx)
    (X := VCodeThread.Witness.X0) (c := c) (env := env) (p := pCL) hlow hthr hext
    (List.isEmpty_iff.mp hind) hv hnt cfgFC hout0 hslot hsym
  refine ⟨ctx, st0, R, gn, bl, A, H, fun slots cs B0 args ρ₀ w₀ tr cT hB0 hcall hfunc hslots
    hbody hterm hregs hty hsig hmr hargs hr => ?_⟩
  exact isel_pauseC H hchk (memRelOk_relW Γ fC c) (relW_wf hc) VCodeThread.Witness.X0_tls
    (fun _ _ _ => rfl) (memRefines_csem Γ.F fctx _ hslot hsym) (mrStable_relW Γ fC c) fC_reg hB0
    hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr

end Concurrency.IselCall.Witness

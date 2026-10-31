import FV.Concurrency.IselResume
import FV.Concurrency.RealizeWitness
import FV.Concurrency.IselRefinesWitness
import FV.Concurrency.CallLoadData

/-!
# Witness: layer 2 pausing at calls (#473, (2a))

* the caller `CallSeg.WitnessC.fC` (`v1 = call fn0(v0); return v1`, `fn0 = colocated %ld`) as
  the driver lowers it: `threadCheck` rejects it (`checksFC`), `threadCheckC` accepts it, and
  **`isel_pause_fC`**: every premise of `IselCall.isel_pauseC` holds for it in the program
  `pCL` (the caller and the compiled `atomic_load`) but the CLIF entry state, its relation to the
  entry world, the arguments and the run; `atCall_csC`: its CLIF entry state is at the call;
* **`isel_resume_fC`**: every premise of `IselResume.isel_resumeC` but the match at the call and
  the callee's return holds for it.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.IselCall.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  IselThread ThreadRefine E2E ClifCStepTerm RealizeCompiled.Witness IselRefines.Witness
  CallSeg.WitnessC IselResume

/-! ## The caller of `atomic_load` -/

theorem checksFC : lowerCheck fC vcC = true ∧ IselCheck.threadCheckC fC = true ∧
    IselCheck.threadCheck fC = false ∧ fC.externs.map (·.2.name) = ["ld"] ∧
    (indSigs fC).isEmpty = true ∧ verifiable fC = true ∧
    fC.blocks.all (fun B => !B.term.isTry) = true ∧
    IselThread.Witness.isOkB vcC.cfg = true ∧ vcC.outgoing = 0 ∧
    (locsOf fC.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    fC.externs = [(0, extF)] := by
  native_decide

theorem cfgFC : ∃ ss ps, vcC.cfg = .ok (ss, ps) := by
  have h := checksFC.2.2.2.2.2.2.2.1
  revert h
  cases vcC.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

theorem fC_reg : ∀ off, ArgLoc.stack off ∉ locsOf fC.sig := by
  intro off hm
  have := List.all_eq_true.mp checksFC.2.2.2.2.2.2.2.2.2.1 _ hm
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
  obtain ⟨hlow, hthr, -, hnames, hind, hv, hnt, -, hout0, -, -⟩ := checksFC
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

/-- **Layer 2 resuming after the caller's call** (module doc): every premise of
`IselResume.isel_resumeC` but the match at the call and the callee's return. -/
theorem isel_resume_fC {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem} {c : BitVec 64}
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx R gn bl A, ∀ (slots : List (Clif.SlotId × Nat)) (s : Clif.State) (b k : Nat)
      (ρ : Nat → CV) (w : ArmState) (stm : Clif.Stmt) (rest : List Clif.Stmt) (fn : Clif.FnRef)
      (args : List Clif.ValueId) (ext : Clif.ExtFunc) (vals rvals : List Clif.Val)
      (cm' : Clif.Mem) (regs' : Clif.Regs) (outs : List CV) (y : ArmState),
      Match fC ctx R gn bl A (RelW Γ fC c) slots s ⟨b, k, ρ, w⟩ →
      s.frame.body = stm :: rest → stm.inst = .call fn args → s.frame.func.extern? fn = some ext →
      s.frame.getMany args = .ok vals → vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params →
      rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns →
      s.frame.regs.setMany stm.results rvals = some regs' →
      outs.length = ext.sig.returns.length → PrefixHold rvals outs → RelW Γ fC c slots cm' y →
      ∃ ρ', VStep vcC (csem Γ.F fctx (xcallX X outs y)) (.run ⟨b, k, ρ, w⟩)
          (.run ⟨b, k + 1, ρ', y⟩) ∧
        Match fC ctx R gn bl A (RelW Γ fC c) slots
          { s with frame := { s.frame with regs := regs', body := rest }, mem := cm' }
          ⟨b, k + 1, ρ', y⟩ := by
  obtain ⟨hlow, hthr, -, -, hind, hv, hnt, -, hout0, -, hexts⟩ := checksFC
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hchk⟩ :=
    IselCheck.obligations_of_threadCheckC hlow hthr
  refine ⟨ctx, R, gn, bl, A, fun slots s b k ρ w stm rest fn args ext vals rvals cm' regs'
    outs y hm hbody hc hext hvals htys hrty hregs hlen hpre hmr => ?_⟩
  have hfunc : s.frame.func = fC := hm.2.1
  have hextF : ext = extF := by
    rw [hfunc, Clif.Function.extern?, hexts] at hext
    simp only [List.lookup] at hext
    split at hext
    · exact (Option.some.inj hext).symm
    · cases hext
  refine isel_resumeC hshape hcert hbr hchk hlow (List.isEmpty_iff.mp hind) hv hnt cfgFC hout0
    hslot hsym hm hbody hc hext ?_ hvals htys hrty hregs hlen hpre hmr
  intro e he _
  rw [hexts, List.mem_singleton] at he
  rw [he, hextF]

end Concurrency.IselCall.Witness

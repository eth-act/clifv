import FV.Concurrency.IselEntry
import FV.Concurrency.IselThreadWitnessData
import FV.Concurrency.VCodeThreadWitness
import FV.E2E.RegLevelFrame

/-!
# Witness: layer 2 on the compiled atomics function (T2h, #311, layer 2e)

**`isel_refines_fA`**: for the function `SegShape.Witness.fA` (`atomic_load`, `atomic_store`,
`atomic_rmw`, `atomic_cas`, `fence`, `load`, `store`, `iadd`, `return`), lowered by the real
driver (`IselThread.Witness.vcA`), every premise of `IselRefines.isel_refines` but the match and
the run is discharged: the driver hypothesis (`driverHypA`, all M4 obligations from the rules),
the multi-threaded check on the same lowering (`threadCheckBl`, evaluated), the memory relation
`E2E.RelW Γ fA c` (`memRelOk_relW`; no model error, and `sp = c` aligned: `relW_wf`) and the
external semantics `VCodeThread.Witness.X0` (`TlsMemFree`).

**`isel_refines_entry_fA`**: likewise for `IselEntry.isel_refines_entry`, from `fA`'s entry
(`fA_reg`: its parameters are passed in registers; `memRefines_csem`, `mrStable_relW`): only the
CLIF entry state, its relation to the entry world, the arguments and the run remain.
-/

namespace Concurrency.IselRefines.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  IselThread ThreadRefine E2E IselThread.Witness SegShape.Witness ClifCStepTerm

/-- `RelW` worlds are error-free and, with `sp = c` aligned, aligned. -/
theorem relW_wf {Γ : E2E.Rel} {f : Clif.Function} {c : BitVec 64} (hc : c.toNat % 16 = 0) :
    ∀ sl cm w, RelW Γ f c sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w :=
  fun _ _ w ⟨_, hsp, herr⟩ => ⟨herr, (checkSP_iff w).mpr (by
    have : spOf w = c := hsp
    rw [this]; exact hc)⟩

/-- **Layer 2 on `fA`** (module doc). -/
theorem isel_refines_fA {Γ : E2E.Rel} {fctx : FnCtx} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} (hc : c.toNat % 16 = 0) (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → VCodeThread.Witness.X0.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A,
      DriverHyp fA vcA ctx st0 R gn bl A (csem Γ.F fctx VCodeThread.Witness.X0) (RelW Γ fA c)
        env p ∧
      ∀ (slots : List (Clif.SlotId × Nat)) (s : Clif.State) (cv : VState CV ArmState)
        (tr : List (List Ev)) (cT : VConf CV ArmState),
        Match fA ctx R gn bl A (RelW Γ fA c) slots s cv →
        VTRun vcA (csem Γ.F fctx VCodeThread.Witness.X0) (cEvs Γ.F fctx) (.run cv) tr cT →
        ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧
          Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
          (n = tr.length ∨ Stop env p t) := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverHypA (env := env) (p := p) (c := c) hslot hsym
  refine ⟨ctx, st0, R, gn, bl, A, H, fun slots s cv tr cT hm hr => ?_⟩
  exact isel_refines H hchk (memRelOk_relW Γ fA c) (relW_wf hc) VCodeThread.Witness.X0_tls hm hr

/-- `fA` takes its parameters in registers. -/
theorem fA_reg : ∀ off, ArgLoc.stack off ∉ locsOf fA.sig := by
  have h : (locsOf fA.sig).all (fun l => match l with | .stack _ => false | _ => true) = true := by
    native_decide
  intro off hm
  have := List.all_eq_true.mp h _ hm
  simp at this

/-- **Layer 2 from `fA`'s entry** (module doc). -/
theorem isel_refines_entry_fA {Γ : E2E.Rel} {fctx : FnCtx} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} (hc : c.toNat % 16 = 0) (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → VCodeThread.Witness.X0.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A,
      DriverHyp fA vcA ctx st0 R gn bl A (csem Γ.F fctx VCodeThread.Witness.X0) (RelW Γ fA c)
        env p ∧
      ∀ (slots : List (Clif.SlotId × Nat)) (cs : Clif.State) (B0 : Clif.Block)
        (args : List Clif.Val) (ρ₀ : Nat → CV) (w₀ : ArmState) (tr : List (List Ev))
        (cT : VConf CV ArmState),
        fA.blocks[0]? = some B0 → cs.callers = [] → cs.frame.func = fA →
        cs.frame.slots = slots → cs.frame.body = B0.body → cs.frame.term = B0.term →
        Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs →
        args.map (·.ty) = B0.params.map (·.2) → args.map (·.ty) = fA.sig.params.map (·.ty) →
        RelW Γ fA c slots cs.mem w₀ → ArgsAtEntry Γ.F fA.sig args w₀ →
        VTRun vcA (csem Γ.F fctx VCodeThread.Witness.X0) (cEvs Γ.F fctx) (.run ⟨0, 0, ρ₀, w₀⟩)
          tr cT →
        ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run cs) trS t ∧
          Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
          (n = tr.length ∨ Stop env p t) := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverHypA (env := env) (p := p) (c := c) hslot hsym
  refine ⟨ctx, st0, R, gn, bl, A, H, fun slots cs B0 args ρ₀ w₀ tr cT hB0 hcall hfunc hslots
    hbody hterm hregs hty hsig hmr hargs hr => ?_⟩
  exact IselEntry.isel_refines_entry H hchk (memRelOk_relW Γ fA c) (relW_wf hc)
    VCodeThread.Witness.X0_tls (memRefines_csem Γ.F fctx _ hslot hsym) (mrStable_relW Γ fA c)
    fA_reg hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr

end Concurrency.IselRefines.Witness

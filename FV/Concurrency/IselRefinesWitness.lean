import FV.Concurrency.IselRefines
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
`E2E.RelW Γ fA c` (`memRelOk_relW`; no model error, and `sp = c` aligned) and the external
semantics `VCodeThread.Witness.X0` (`TlsMemFree`).
-/

namespace Concurrency.IselRefines.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  IselThread ThreadRefine E2E IselThread.Witness SegShape.Witness ClifCStepTerm

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
  have hMRw : ∀ sl cm w, RelW Γ fA c sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w :=
    fun _ _ w ⟨_, hsp, herr⟩ => ⟨herr, (checkSP_iff w).mpr (by
      have : spOf w = c := hsp
      rw [this]; exact hc)⟩
  exact isel_refines H hchk (memRelOk_relW Γ fA c) hMRw VCodeThread.Witness.X0_tls hm hr

end Concurrency.IselRefines.Witness

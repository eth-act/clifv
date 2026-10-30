import FV.Concurrency.CallEntryWitness
import FV.Concurrency.CallSegAbi

/-!
# Witness: all layers from the caller's ABI entry (#473, step (4))

**`arm_abiCRN_fC`**: `CallSegAbi.arm_isel_refines_abiCRN` for the compiled caller of
`atomic_load` (`CallSeg.WitnessC.RC`, `fC`) on the linked machine `MC2` from its ABI entry
`RC.s0`, every premise holding but the CLIF entry state, its relation to the entry world and the
arguments (as `CallRetsN.Witness.arm_entryCRN_fC`, which starts after the prologue).
-/

namespace Concurrency.CallSegAbi.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  AllocThread ArmAllocThread IselThread ThreadRefine E2E ClifCStepTerm RealizeCompiled.Witness
  IselRefines.Witness CallSeg.WitnessC IselResume IselCall IselCall.Witness CallEntry.Witness
  IselCallRet CallRetsEnd

/-- **All layers of the caller from its ABI entry** (module doc). -/
theorem arm_abiCRN_fC {env : Clif.Env} (henv : env.extern "ld" = none) {c : BitVec 64}
    (hc : c.toNat % 16 = 0) :
    ∃ (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
      (A : Nat → Nat → List Clif.ValueId) (L : Nat → Prop) (ss' : Array (Array Nat))
      (cc : CheckCtx) (ins : Array (Option AState)),
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      ∀ (slots : List (Clif.SlotId × Nat)) (cs : Clif.State) (B0 : Clif.Block)
        (args : List Clif.Val) (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
        fC.blocks[0]? = some B0 → cs.callers = [] → cs.frame.func = fC →
        cs.frame.slots = slots → cs.frame.body = B0.body → cs.frame.term = B0.term →
        Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs →
        args.map (·.ty) = B0.params.map (·.2) → args.map (·.ty) = fC.sig.params.map (·.ty) →
        RelW ΓC fC c slots cs.mem w₀C → ArgsAtEntry RC.F fC.sig args w₀C →
        PRun Policy.arm MC2 (OkPriv RC) (RC.s0, mon) ls t' →
        ∃ k trS t ψ, k ≤ ls.length ∧ CRun env pCL (.run cs) trS t ∧
          Refines Maps (PrivA RC) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
          (k = ls.length ∨ Stop env pCL t ∨
            (∃ tE s' vV' vP' cM', PRun Policy.arm MC2 (OkPriv RC) (RC.s0, mon) (ls.take k) tE ∧
              RelQ RC tE (.run cM') ∧ Pause RC (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
              Match fC ctx R gn bl A (RelW ΓC fC c) slots s' vV' ∧
              PMatch vcC RC.vc (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) L ss' (.run vV') (.run vP') ∧
              MatchRun cc ins ckeep (fun r => locVal RC.fr (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize).length RC.s0) (.reg r)) cM' vP') ∨
            (∃ tE s', PRun Policy.arm MC2 (OkPriv RC) (RC.s0, mon) (ls.take k) tE ∧ t = .run s' ∧
              AtRetS s' ∧ RetEnd RC 0x4000#64 env pCL (RelW ΓC fC c) slots
                (fun r => locVal RC.fr (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize).length RC.s0) (.reg r)) tE.1 s')) := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverC henv c
  obtain ⟨L, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcC) (vcp := RC.vc)
    CallResumeL.Witness.prepC
  obtain ⟨cc, ins, a0, hat, hm4⟩ := CallLayers.alloc_init (vc := RC.vc) (rf := RC.rf) allocC ckeep
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  refine ⟨ctx, st0, R, gn, bl, A, L, ss', cc, ins, H, fun slots cs B0 args mon ls t' hB0 hcall hfunc
    hslots hbody hterm hregs hty hsig hmr hargs hr => ?_⟩
  exact arm_isel_refines_abiCRN wfRC scopeRC rfl agreesAt_MC2 abiRC H hchk
    (memRelOk_relW ΓC fC c) (relW_wf hc) VCodeThread.Witness.X0_tls (fun _ _ _ => rfl)
    (memRefines_csem RC.F RC.ctx _ rfl (fun _ _ h => by cases h)) (mrStable_relW ΓC fC c) fC_reg
    H3 (hm3 _ _) hat hm4 hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hq hA hr

/-- **The caller's realized prefix from its ABI entry is exclusive-closed**
(`arm_isel_refines_abiCRNX` on the same compiled caller and machine). -/
theorem arm_abiCRNX_fC {env : Clif.Env} (henv : env.extern "ld" = none) {c : BitVec 64}
    (hc : c.toNat % 16 = 0) :
    ∃ (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
      (A : Nat → Nat → List Clif.ValueId),
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      ∀ (slots : List (Clif.SlotId × Nat)) (cs : Clif.State) (B0 : Clif.Block)
        (args : List Clif.Val) (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
        fC.blocks[0]? = some B0 → cs.callers = [] → cs.frame.func = fC →
        cs.frame.slots = slots → cs.frame.body = B0.body → cs.frame.term = B0.term →
        Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs →
        args.map (·.ty) = B0.params.map (·.2) → args.map (·.ty) = fC.sig.params.map (·.ty) →
        RelW ΓC fC c slots cs.mem w₀C → ArgsAtEntry RC.F fC.sig args w₀C →
        PRun Policy.arm MC2 (OkPriv RC) (RC.s0, mon) ls t' →
        ∃ k trS t, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧
          CRun env pCL (.run cs) trS t := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverC henv c
  obtain ⟨L, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcC) (vcp := RC.vc)
    CallResumeL.Witness.prepC
  obtain ⟨cc, ins, a0, hat, hm4⟩ := CallLayers.alloc_init (vc := RC.vc) (rf := RC.rf) allocC ckeep
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  refine ⟨ctx, st0, R, gn, bl, A, H, fun slots cs B0 args mon ls t' hB0 hcall hfunc
    hslots hbody hterm hregs hty hsig hmr hargs hr => ?_⟩
  obtain ⟨k, trS, t, -, hk, hx, hrun, -⟩ := arm_isel_refines_abiCRNX wfRC scopeRC rfl agreesAt_MC2
    abiRC H hchk (memRelOk_relW ΓC fC c) (relW_wf hc) VCodeThread.Witness.X0_tls (fun _ _ _ => rfl)
    (memRefines_csem RC.F RC.ctx _ rfl (fun _ _ h => by cases h)) (mrStable_relW ΓC fC c) fC_reg
    H3 (hm3 _ _) hat hm4 hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hq hA hr
  exact ⟨k, trS, t, hk, hx, hrun⟩

end Concurrency.CallSegAbi.Witness

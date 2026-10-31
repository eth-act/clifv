import FV.Concurrency.ArmAllocLinkedWitness
import FV.Concurrency.CallResumeWitness
import FV.Concurrency.IselRetT
import FV.Concurrency.IselCallRet

/-!
# Witness: all layers from the caller's entry, pausing at calls and returns (#473, (1))

On the compiled caller of `atomic_load` (`CallSeg.WitnessC.RC`, its CLIF function `fC`):

* **`arm_entry_fC`**: `CallLayers.arm_isel_refines_entryC` on the linked machine `MC2` from the
  state after the caller's prologue (`Q ∧ AInv` at the allocated entry configuration by
  `q_init_lines`, the entry relations by `prep_init`/`alloc_init`), every premise holding but
  the CLIF entry state, its relation to the entry world and the arguments;
* **`isel_cr_fC`**: `IselCallRet.isel_refinesCR` for the caller (every premise but the match
  and the run);
* **`term_ret_fC`**: `IselRetT.term_stepRT` for the caller.
-/

namespace Concurrency.CallEntry.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  AllocThread ArmAllocThread IselThread ThreadRefine E2E ClifCStepTerm RealizeCompiled.Witness
  IselRefines.Witness CallSeg.WitnessC IselResume IselCall IselCall.Witness

/-- The caller's memory relation's parameters: the activation's private set, no symbols. -/
def ΓC : E2E.Rel := ⟨RC.F, fun _ => none, RC.ctx.slotBase, 0⟩

theorem driverC {env : Clif.Env} (henv : env.extern "ld" = none) (c : BitVec 64) :
    ∃ ctx st0 R gn bl A,
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      IselCheck.threadCheckBlC fC bl = true := by
  obtain ⟨hlow, hthr, -, hnames, hind, hv, hnt, -, hout0, -, -⟩ := checksFC
  have hext : ∀ e ∈ fC.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames, List.mem_singleton] at this
    rw [this]; exact henv
  exact driverHypT_of (Γ := ΓC) (fctx := RC.ctx) (X := VCodeThread.Witness.X0) (c := c)
    (env := env) (p := pCL) hlow hthr hext (List.isEmpty_iff.mp hind) hv hnt cfgFC hout0 rfl
    (fun _ _ h => by cases h)

/-- **All layers of the caller from its entry on the linked machine** (module doc). -/
theorem arm_entry_fC {env : Clif.Env} (henv : env.extern "ld" = none) {c : BitVec 64}
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
        PRun Policy.arm MC2 (OkPriv RC)
          (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize).length RC.s0, mon) ls t' →
        ∃ k trS t ψ, k ≤ ls.length ∧ CRun env pCL (.run cs) trS t ∧
          Refines Maps (PrivA RC) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
          (k = ls.length ∨ Stop env pCL t ∨
            (∃ tE cE, PRun Policy.arm MC2 (OkPriv RC)
                (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize).length RC.s0, mon) (ls.take k) tE ∧
              RelQ RC tE cE ∧ AtRets RC cE) ∨
            (∃ tE s' vV' vP' cM', PRun Policy.arm MC2 (OkPriv RC)
                (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize).length RC.s0, mon) (ls.take k) tE ∧
              RelQ RC tE (.run cM') ∧ Pause RC (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
              Match fC ctx R gn bl A (RelW ΓC fC c) slots s' vV' ∧
              PMatch vcC RC.vc (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) L ss' (.run vV')
                (.run vP') ∧
              MatchRun cc ins ckeep (fun r => locVal RC.fr
                (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize).length RC.s0) (.reg r)) cM' vP')) := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverC henv c
  obtain ⟨L, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcC) (vcp := RC.vc)
    CallResumeL.Witness.prepC
  obtain ⟨cc, ins, a0, hat, hm4⟩ := CallLayers.alloc_init (vc := RC.vc) (rf := RC.rf) allocC ckeep
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  refine ⟨ctx, st0, R, gn, bl, A, L, ss', cc, ins, H, fun slots cs B0 args mon ls t' hB0 hcall hfunc
    hslots hbody hterm hregs hty hsig hmr hargs hr => ?_⟩
  exact CallLayers.arm_isel_refines_entryC wfRC scopeRC rfl agreesAt_MC2 H hchk
    (memRelOk_relW ΓC fC c) (relW_wf hc) VCodeThread.Witness.X0_tls (fun _ _ _ => rfl)
    (memRefines_csem RC.F RC.ctx _ rfl (fun _ _ h => by cases h)) (mrStable_relW ΓC fC c) fC_reg
    H3 (hm3 _ _) hat hm4 hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hq hA hr

/-- **Layer 2 of the caller pausing at calls and returns** (module doc). -/
theorem isel_cr_fC {env : Clif.Env} (henv : env.extern "ld" = none) {c : BitVec 64}
    (hc : c.toNat % 16 = 0) :
    ∃ ctx st0 R gn bl A,
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      ∀ (slots : List (Clif.SlotId × Nat)) (s : Clif.State) (v : VState CV ArmState)
        (tr : List (List Ev)) (cT : VConf CV ArmState),
        Match fC ctx R gn bl A (RelW ΓC fC c) slots s v →
        VTRun vcC (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) (.run v) tr cT →
        ∃ n trS t ψ, n ≤ tr.length ∧ CRun env pCL (.run s) trS t ∧
          Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
          ((((n = tr.length ∧ ∃ c', VStep vcC (csem RC.F RC.ctx RC.X) cT c') ∨ Stop env pCL t) ∧
              ∀ v, t = .ret v → n = tr.length) ∨
            ∃ s' vs', t = .run s' ∧ IselCallRet.AtCR s' ∧
              Match fC ctx R gn bl A (RelW ΓC fC c) slots s' vs' ∧
              VTRun vcC (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) (.run vs') (tr.drop n) cT) := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverC henv c
  exact ⟨ctx, st0, R, gn, bl, A, H, fun slots s v tr cT hm hr =>
    IselCallRet.isel_refinesCR H hchk (memRelOk_relW ΓC fC c) (relW_wf hc)
      VCodeThread.Witness.X0_tls hm hr⟩

/-- **The caller's `return` on `DriverHypT`** (module doc). -/
theorem term_ret_fC {env : Clif.Env} (henv : env.extern "ld" = none) (c : BitVec 64) :
    ∃ ctx st0 R gn bl A,
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      ∀ (slots : List (Clif.SlotId × Nat)) (s : Clif.State) (b k : Nat) (ρ : Nat → CV)
        (w : ArmState), Match fC ctx R gn bl A (RelW ΓC fC c) slots s ⟨b, k, ρ, w⟩ →
        s.frame.body = [] → s.frame.term.isTry = false → ∀ vals cm,
        Clif.step env pCL s = .done vals cm →
        ∃ us outs w', VRetFrom vcC (csem RC.F RC.ctx RC.X) ⟨b, k, ρ, w⟩ us outs w' ∧
          RetPins vals us ∧ us.length = outs.length ∧
          PrefixHold vals outs ∧ RelW ΓC fC c slots s.mem w' ∧
          cm = (s.mem.free (slots.map (·.2))).leave := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, -⟩ := driverC henv c
  exact ⟨ctx, st0, R, gn, bl, A, H, fun slots s b k ρ w hm hb hnt =>
    (IselRetT.term_stepRT H hm hb hnt).2.1⟩

end Concurrency.CallEntry.Witness

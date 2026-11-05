import FV.E2E.UnwindPrepare
import FV.E2E.UnwindValueSem
import FV.E2E.DeadCleanupPipeline

/-!
# The dead cleanup with unwinding (S10e, #232)

The shipped compiler runs the dead cleanup `prune` between the lowering and `prepare`
(`E2E.CompiledCleanup`). Its simulation (`star_sim`, `rel_kept`: generic in the semantics, for
any semantics whose pure producers keep the world and continue) also carries the exceptional
ends: a run of `vc` ending at a raising `call` is a run of `prune vc` ending at the same call
(a call is never pruned, and the kept instructions read the same operand values).

* `unwinds_clean`/`unwinds_prune`, `pruneCorrectU` (`prune_correct`'s counterpart),
  `prepareCorrectU_trans`, `prepareCorrectU_cleanup` (`prune` then `prepare`, any semantics with
  `DriverSem` and pure producers) and its value-semantics instance
  `prepareCorrectU_cleanup_value`;
* `backend_correct_cleanup_layersU_ex`: the composition with unwinding over the cleanup
  pipeline, from the CLIF → VCode layer (`IselSimU`) and the register-level layer
  (`RegLevelCorrectUEx`) of a semantics as above.
-/

namespace Backend.DeadCleanup

open Backend Backend.Proof Backend.Proof.Driver E2E

/-- **Cleaning keeps the exceptional ends.** -/
theorem unwinds_clean {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {XR : XRaise} {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {obj : BitVec 64} {w : Arm.ArmState}
    (h : VUnwinds vc sem XR ρ₀ w₀ obj w) : VUnwinds (clean vc) sem XR ρ₀ w₀ obj w := by
  obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hb, hi, hop, hraise, hs, hlen⟩ := h
  obtain ⟨vb0, hb0⟩ : ∃ vb0, vc.blocks[0]? = some vb0 := by
    cases hstar with
    | refl => exact ⟨vb, hb⟩
    | step h _ => cases h with | step he _ _ _ _ _ => exact ⟨_, he⟩
  obtain ⟨c1, hstar', hr⟩ := star_sim hp hcmp ht (rel_entry hb0 ρ₀ w₀) hstar
  obtain ⟨k', ρ', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop rfl rfl rfl
  exact ⟨b, k', ρ', w1, cleanBlock vc 0 vb, info, ops, outs, hstar', hb', hi', hop,
    by rw [← hu]; exact hraise, by rw [← hu]; exact hs, hlen⟩

/-- **`prune` keeps the exceptional ends.** -/
theorem unwinds_prune {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    {XR : XRaise} {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {obj : BitVec 64} {w : Arm.ArmState}
    (h : VUnwinds vc sem XR ρ₀ w₀ obj w) : VUnwinds (prune vc) sem XR ρ₀ w₀ obj w := by
  unfold prune
  cases hc : vc.cfg with
  | error e => exact h
  | ok p => exact unwinds_clean hp hcmp (terminated_of_cfg hc) h

/-- **`prune` preserves returns, traps and exceptional ends** (`prune_correct` with
unwinding). -/
theorem pruneCorrectU {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem) (XR : XRaise) :
    PrepareCorrectU sem XR vc (prune vc) :=
  ⟨prune_correct hp hcmp, fun _ _ _ _ h => unwinds_prune hp hcmp h⟩

end Backend.DeadCleanup

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `PrepareCorrectU` composes. -/
theorem prepareCorrectU_trans {sem : Sem} {XR : XRaise} {vc vcm vcp : VCode}
    (h1 : PrepareCorrectU sem XR vc vcm) (h2 : PrepareCorrectU sem XR vcm vcp) :
    PrepareCorrectU sem XR vc vcp := by
  refine ⟨fun a w => ⟨fun us vals w' h => ?_, fun c h => ?_⟩, fun ρ₀ w₀ obj w h => ?_⟩
  · exact (h2.1 a w).1 _ _ _ ((h1.1 a w).1 _ _ _ h)
  · exact (h2.1 a w).2 _ ((h1.1 a w).2 _ h)
  · exact h2.2 _ _ _ _ (h1.2 _ _ _ _ h)

/-- **The cleanup pipeline's VCode → prepared VCode layer with unwinding**: `prune`, then
`prepare` (validated by `prepCheck`), for a semantics with `DriverSem` whose pure producers keep
the world and continue and whose compares' flags the next compare overwrites. -/
theorem prepareCorrectU_cleanup {sem : Sem} {vc vcp : VCode} (hds : DriverSem sem)
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (h : prepCheck (prune vc) vcp = true) (XR : XRaise) : PrepareCorrectU sem XR vc vcp :=
  prepareCorrectU_trans (pruneCorrectU hp hcmp XR) (prepareCorrectU_of_check hds h XR)

/-- `prepareCorrectU_cleanup` for the value semantics with unwinding, from the code after the skip
of unused instructions (`skipStage f vc`, which the production cleanup stage prunes). -/
theorem prepareCorrectU_cleanup_value {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    PrepareCorrectU (valueSemU F ctx X XR) XR (skipStage f vc) vcp :=
  prepareCorrectU_cleanup (vc := skipStage f vc) (driverSem_valueSemU F ctx X XR)
    (fun _ _ _ _ _ _ hp h => valueSemU_pure hp h) (valueSemU_cmpOverwrite F ctx X XR) hc.prepOk XR

/-- **The composition with unwinding over the cleanup pipeline**: the CLIF → VCode layer of the
code after the skip of unused instructions (`skipStage f vc`, `IselSimU`), the cleanup and
`prepare` (`prepareCorrectU_cleanup`), and the
register-level layer of the prepared `vcp` (`RegLevelCorrectUEx`), for a semantics with
`DriverSem` whose pure producers keep the world and continue (`backend_correct_cleanup_ex`'s
shape; the entry's arguments as there, `ArgsIn` and `StackArgsAvoid`). -/
theorem backend_correct_cleanup_layersU_ex {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {XR : XRaise} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.XEnv}
    (hIsel : ∀ s, IselSimU (sem s) XR ⟨F s, syms, slotOff, out⟩ env p f (skipStage f vc))
    (hds : ∀ s, DriverSem (sem s))
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (hReg : RegLevelCorrectUEx sem XR F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra astep s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_of_layersU_ex hIsel
    (fun s' => prepareCorrectU_cleanup (vc := skipStage f vc) (hds s') (hPure s') (hCmp s') hc.prepOk XR)
    hReg hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs hargF)
    hcs hrel htr fuel

end E2E

/-! ## Non-vacuity -/

namespace Backend.DeadCleanup.UnwindWitness

open Backend Backend.Proof Backend.Proof.Driver E2E Backend.Proof.UnwindSemWitness

/-- A dead producer, then a plain call of a raising callee (`f`, raising object 77), then a
return. -/
def vc : VCode :=
  ⟨"cleanup_unwind", #[⟨0, #[deadMvn, .call info, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩

def mvnOps : Array Operand :=
  #[⟨2, .int, .def, .late, .reg⟩, ⟨1, .int, .use, .early, .reg⟩]

def rho0 : Nat → CV := fun _ => 0#128

def rho1 : Nat → CV := vdefUpd mvnOps [ofX (~~~(0#64))] rho0

/-- The raw VCode ends by the exception after running the dead producer, and so does the pruned
one (whose dead producer is gone). -/
example (F : BitVec 64 → Prop) (X : ExtSem) (w : Arm.ArmState) :
    VUnwinds vc (valueSemU F ⟨0, 0⟩ X XR) XR rho0 w 77 w ∧
    VUnwinds (prune vc) (valueSemU F ⟨0, 0⟩ X XR) XR rho0 w 77 w ∧
    (prune vc).blocks[0]?.map (·.insts.size) = some 2 := by
  have h : VUnwinds vc (valueSemU F ⟨0, 0⟩ X XR) XR rho0 w 77 w := by
    have h1 : VStep vc (valueSemU F ⟨0, 0⟩ X XR) (.run ⟨0, 0, rho0, w⟩) (.run ⟨0, 1, rho1, w⟩) :=
      VStep.step rfl rfl (show deadMvn.operands = .ok mvnOps from rfl) rfl rfl
        (VNext.next (by decide))
    exact ⟨0, 1, rho1, w, _, info, _, _, .step h1 (.refl _), rfl, rfl, rfl, rfl,
      valueSemU_call_raise rfl, rfl⟩
  exact ⟨h, unwinds_prune (fun _ _ _ _ _ _ hp hs => valueSemU_pure hp hs)
    (valueSemU_cmpOverwrite F ⟨0, 0⟩ X XR) h, by decide +kernel⟩

end Backend.DeadCleanup.UnwindWitness

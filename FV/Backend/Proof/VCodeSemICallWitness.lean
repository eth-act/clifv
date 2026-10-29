module

public import FV.Backend.Proof.VCodeSemICall
public import FV.Backend.Proof.VCodeSemISeqWitness

@[expose] public section

/-!
# Witnesses for the one-call transfer to `csemI` (`FV/Backend/Proof/VCodeSemICall.lean`)

* `call_seq`: the straight-line run of one `call` (no results) from counter `3` falls through at
  counter `4`, and `seqRun_csemI_le1` gives it from the `csem` run at index `3`.
* `nop_le1`: `LowerInstOk.csemI_le1` on `nop`'s empty lowering.
-/

namespace Backend.Proof.VCodeSemICallWitness

open Backend Backend.Proof Backend.Proof.VCodeSemISeqWitness

/-- Every call returns no results and keeps the world. -/
def XE : ExtSemI :=
  { call := fun _ _ _ w => some ([], w), sym := fun _ _ => 0, tp := 0,
    tlsFlags := fun _ w => Arm.read_pstate w }

theorem callsI_call : callsI [.call default] = 1 := rfl

/-- One `call` from counter `3` falls through at counter `4`. -/
theorem call_seq (F : BitVec 64 → Prop) (fctx : FnCtx) (ρ : Nat → CV) (w : Arm.ArmState) :
    ∃ ρ', seqRun (csemI F fctx XE) [.call default] ρ (w, 3) = some (.fall ρ' (w, 4)) :=
  ⟨_, rfl⟩

/-- `seqRun_csemI_le1` on it: the `csem` run at index `3`, the counter counting the call. -/
theorem call_seq_le1 (F : BitVec 64 → Prop) (fctx : FnCtx) (ρ : Nat → CV) (w : Arm.ArmState) :
    seqRun (csemI F fctx XE) [.call default] ρ (w, 3) =
      (seqRun (csem F fctx (XE.at 3)) [.call default] ρ w).map (SeqEnd.liftI [.call default] 3) :=
  seqRun_csemI_le1 F fctx XE (Nat.le_of_eq callsI_call) ρ w 3

/-- `LowerInstOk.csemI_le1` on `nop`'s empty lowering (no calls, any counter invariant). -/
theorem nop_le1 (F : BitVec 64 → Prop) (fctx : FnCtx) (MR : MemRelT) (Q : Clif.Mem → Nat → Prop)
    (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (st : LState) :
    LowerInstOk (csemI F fctx XE) (fun sl cm w => MR sl cm w.1 ∧ Q cm w.2) env p ctx .nop [] st []
      st [] :=
  LowerInstOk.csemI_le1 (fun n => nop_csem F fctx (XE.at n) MR env p ctx st) (by decide)
    fun fr cm vals cm' n h hq => by
      rw [instOutcome_nop] at h
      cases h
      exact hq

end Backend.Proof.VCodeSemICallWitness

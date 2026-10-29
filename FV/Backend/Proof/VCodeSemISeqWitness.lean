module

public import FV.Backend.Proof.VCodeSemISeq
public import FV.Backend.Proof.VCodeSemIWitness

@[expose] public section

/-!
# Witnesses for the call-free transfer to `csemI` (`FV/Backend/Proof/VCodeSemISeq.lean`)

* `nop_ok`: the empty lowering of `nop` is correct for `csem` (any memory relation), and by
  `LowerInstOk.csemI` for `csemI` with the counted memory relation (any counter invariant).
* `jump_seq`: `seqRun_csemI_noCall` on `[jump]` from counter `4` with the call-numbered
  externals `XW`.
-/

namespace Backend.Proof.VCodeSemISeqWitness

open Backend Backend.Proof Backend.Proof.VCodeSemIWitness

/-- `nop` neither fails nor changes the memory. -/
theorem instOutcome_nop (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame) (cm : Clif.Mem) :
    instOutcome env p fr cm .nop = .ok ([], cm) := rfl

/-- The empty lowering of `nop` is correct for `csem`. -/
theorem nop_csem (F : BitVec 64 → Prop) (fctx : FnCtx) (X : ExtSem) (MR : MemRelT)
    (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (st : LState) :
    LowerInstOk (csem F fctx X) MR env p ctx .nop [] st [] st [] where
  mono := Nat.le_refl _
  defs := fun _ h => nomatch h
  run := fun fr cm ρ w _ _ _ hmr => by
    simp only [instOutcome_nop]
    exact ⟨fun _ h => (nomatch h), ρ, w, rfl, .inl trivial, hmr⟩

/-- **`LowerInstOk.csemI` on `nop`**: its empty lowering is correct for the counted semantics. -/
theorem nop_ok (F : BitVec 64 → Prop) (fctx : FnCtx) (MR : MemRelT) (Q : Clif.Mem → Nat → Prop)
    (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (st : LState) :
    LowerInstOk (csemI F fctx XW) (fun sl cm w => MR sl cm w.1 ∧ Q cm w.2) env p ctx .nop [] st []
      st [] :=
  LowerInstOk.csemI (m := 0) (nop_csem F fctx (XW.at 0) MR env p ctx st) (fun _ h => nomatch h)
    fun fr cm vals cm' n h hq => by
      rw [instOutcome_nop] at h
      cases h
      exact hq

/-- `seqRun_csemI_noCall` on `[jump]`: the counted run is the `csem` one at counter `4`. -/
theorem jump_seq (F : BitVec 64 → Prop) (fctx : FnCtx) (ρ : Nat → CV) (w : Arm.ArmState) :
    seqRun (csemI F fctx XW) [.jump default] ρ (w, 4) =
      (seqRun (csem F fctx (XW.at 0)) [.jump default] ρ w).map (SeqEnd.mapW fun w => (w, 4)) :=
  seqRun_csemI_noCall F fctx XW 0 (by decide) ρ w 4

end Backend.Proof.VCodeSemISeqWitness

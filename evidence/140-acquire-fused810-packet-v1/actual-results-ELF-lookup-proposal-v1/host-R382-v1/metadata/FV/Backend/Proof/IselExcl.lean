import FV.Backend.Proof.IselExclSound

/-!
# `ExcludedUnmatchable program`

Every root rule of `lower` is a closure root or passes the abstract pattern checker
(`exclOk_program`: one kernel decision over the exported rule list), and a rule that passes the
checker matches no instruction of a `CtxInv` context (`fails_sound`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000 in
/-- Every root rule of `lower` is a closure root or cannot match an instruction (checked). -/
theorem exclOk_program : (program.rulesOf TId.lower).all (exclOk program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-- **`ExcludedUnmatchable`**: the root rules of `lower` outside the closure never match an
instruction of a `CtxInv` context. -/
theorem excludedUnmatchable : ExcludedUnmatchable program := by
  intro r hr hroot f ctx hctx hE ii info inst hi hc cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp exclOk_program r hr
  rw [closureRoot_eq] at hroot
  simp only [exclOk, hroot, Bool.false_or] at hok
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    split at hok
    · rename_i q hargs
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      exact fails_sound hctx q .inst _ _ _ _ hok
        ⟨ii, info, inst, rfl, hi, hc,
          hctx.data ii info inst hi hc⟩ h1
    · cases hok

end Backend.Proof

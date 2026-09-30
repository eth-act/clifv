import FV.Opt.Proof.LegalShift

/-! # Variable-amount `i128` shifts, 8-bit amount (split for build time) -/

namespace Opt.Legal

open Clif

set_option maxHeartbeats 4000000

theorem pat_varShift8 (op0 : BinaryOp)
    (hop : op0 = .ishl ∨ op0 = .ushr ∨ op0 = .sshr ∨ op0 = .rotl ∨ op0 = .rotr)
    (xl xh : BitVec 64) (a : BitVec 8) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, ⟨.i8, a⟩]) (Pat.varShiftFull op0 .narrow) = some ρ ∧
      Out128 ρ 3 4 (shiftV op0 (xh ++ xl) (a.toNat % 128)) := by
  rw [shiftV_eq a (by omega)]
  generalize hX : shiftVbv op0 (xh ++ xl) (a.setWidth 128 &&& 127#128) = X
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp only [shiftVbv] at hX <;> vs_fin a

end Opt.Legal

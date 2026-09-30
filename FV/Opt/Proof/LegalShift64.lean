import FV.Opt.Proof.LegalShift

/-! # Variable-amount `i128` shifts, 64-bit amount (split for build time) -/

namespace Opt.Legal

open Clif

set_option maxHeartbeats 4000000

/-- The variable-shift patterns with a 64-bit amount `a` (`amt128` from the low half of an
`i128` amount or from an `i64` amount). -/
theorem pat_varShift64 (op0 : BinaryOp)
    (hop : op0 = .ishl ∨ op0 = .ushr ∨ op0 = .sshr ∨ op0 = .rotl ∨ op0 = .rotr)
    (xl xh a : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 a]) (Pat.varShiftFull op0 .wide) = some ρ ∧
      Out128 ρ 3 4 (shiftV op0 (xh ++ xl) (a.toNat % 128)) := by
  rw [shiftV_eq a (by omega)]
  generalize hX : shiftVbv op0 (xh ++ xl) (a.setWidth 128 &&& 127#128) = X
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp only [shiftVbv] at hX <;> vs_fin a

end Opt.Legal

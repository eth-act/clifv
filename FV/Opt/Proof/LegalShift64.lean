import FV.Opt.Proof.LegalShift

/-! # Variable-amount `i128` shifts, 64-bit amount (split for build time) -/

namespace Opt.Legal

open Clif

set_option maxHeartbeats 4000000

/-- The variable-shift patterns with a 64-bit amount `a` (`amt128` from the low half of an
`i128` amount or from an `i64` amount). -/
theorem pat_varShift64 (op0 : BinaryOp)
    (hop : op0 = .ishl ∨ op0 = .ushr ∨ op0 = .sshr ∨ op0 = .rotl ∨ op0 = .rotr)
    (xl xh : BitVec 64) (a : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 a]) (Pat.varShiftFull op0 .wide) = some ρ ∧
      Out128 ρ 3 4 (shiftV op0 (xh ++ xl) (a.toNat % 128)) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · vs_shift a
  · vs_shift a
  · vs_shift a
  · rw [shiftV_rotl (by omega) a]
    exact rot_glue (pre := (Pat.amt .wide false 5).1) rotCore_6_7 (amtK_lt (by omega) a)
      (by vs_pre)
  · rw [shiftV_rotr (by omega) a]
    exact rot_glue (pre := (Pat.amt .wide true 5).1) rotCore_11_12 (rotrAmt_lt (by omega) a)
      (by vs_pre)

end Opt.Legal

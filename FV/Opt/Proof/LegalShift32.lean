import FV.Opt.Proof.LegalShift

/-! # Variable-amount `i128` shifts, 32-bit amount (split for build time) -/

namespace Opt.Legal

open Clif

set_option maxHeartbeats 4000000

theorem pat_varShift32 (op0 : BinaryOp)
    (hop : op0 = .ishl ∨ op0 = .ushr ∨ op0 = .sshr ∨ op0 = .rotl ∨ op0 = .rotr)
    (xl xh : BitVec 64) (a : BitVec 32) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, ⟨.i32, a⟩]) (Pat.varShiftFull op0 .narrow) = some ρ ∧
      Out128 ρ 3 4 (shiftV op0 (xh ++ xl) (a.toNat % 128)) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · vs_shift a
  · vs_shift a
  · vs_shift a
  · rw [shiftV_rotl (by omega) a]
    exact rot_glue (pre := (Pat.amt .narrow false 5).1) rotCore_7_8 (amtK_lt (by omega) a)
      (by vs_pre)
  · rw [shiftV_rotr (by omega) a]
    exact rot_glue (pre := (Pat.amt .narrow true 5).1) rotCore_12_13 (rotrAmt_lt (by omega) a)
      (by vs_pre)

end Opt.Legal

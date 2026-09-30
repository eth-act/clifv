import FV.Opt.Proof.LegalArith

/-!
# Variable-amount `i128` shifts and rotates (`Opt.Legal.Pat.varShiftFull`)

Split from `LegalArith.lean` (the `bv_decide` calls here dominate its build time).
-/

namespace Opt.Legal

open Clif

set_option maxHeartbeats 4000000

/-! ## Variable shifts -/

theorem kA_toNat {v : Nat} (A : BitVec v) (hv : v ≤ 128) :
    (A.setWidth 128 &&& 127#128).toNat = A.toNat % 128 := by
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
    have := A.isLt; exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hv))]
  show A.toNat &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- The source shifts at `i128`, by an amount `n < 128`. -/
def shiftV (op : BinaryOp) (X : BitVec 128) (n : Nat) : BitVec 128 :=
  match op with
  | .ishl => X <<< n
  | .ushr => X >>> n
  | .sshr => X.sshiftRight n
  | .rotl => X.rotateLeft n
  | _ => X.rotateRight n

/-- The source shift by `A mod 128` as a shift by the bit vector `A mod 128`. -/
theorem shiftV_bv {op : BinaryOp} {v : Nat} (A : BitVec v) (hv : v ≤ 128) (X : BitVec 128) :
    shiftV op X (A.toNat % 128) = match op with
      | .ishl => X <<< (A.setWidth 128 &&& 127#128)
      | .ushr => X >>> (A.setWidth 128 &&& 127#128)
      | .sshr => X.sshiftRight' (A.setWidth 128 &&& 127#128)
      | .rotl => X <<< (A.setWidth 128 &&& 127#128) |||
          X >>> (128#128 - (A.setWidth 128 &&& 127#128))
      | _ => X >>> (A.setWidth 128 &&& 127#128) |||
          X <<< (128#128 - (A.setWidth 128 &&& 127#128)) := by
  have hk := kA_toNat A hv
  have hlt : A.toNat % 128 < 128 := Nat.mod_lt _ (by omega)
  have h128 : (128#128 - (A.setWidth 128 &&& 127#128)).toNat = 128 - A.toNat % 128 := by
    rw [BitVec.toNat_sub, hk]; simp; omega
  cases op <;> simp only [shiftV, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.sshiftRight', hk, h128] <;>
    first
    | rfl
    | (rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hlt])
    | (rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hlt])

/-- The end of a variable-shift proof: the source value opaque during the run. -/
macro "vs_fin " a:term : tactic => `(tactic| (
  simp only [Pat.varShiftFull, Pat.amt, Pat.varShift, Pat.cross, List.cons_append,
    List.nil_append, beq_self_eq_true, reduceCtorEq, beq_iff_eq, ite_true, ite_false,
    Bool.false_eq_true]
  pat_eval
  simp only [ishl64, ushr64, sshr64, Sem.binary, Sem.bor, Sem.band, Sem.isub, select_bif,
    Sem.icmp, Sem.intcc, bool8_eq, Sem.uextend]
  subst_vars
  generalize hk : BitVec.setWidth 128 $a &&& 127#128 = k at *
  try (generalize hk2 : 128#128 - k = k2 at *)
  constructor <;> bv_decide))

/-- The bit-vector form of the source shift by `A mod 128` (`shiftV_bv`). -/
def shiftVbv (op : BinaryOp) (X K : BitVec 128) : BitVec 128 :=
  match op with
  | .ishl => X <<< K
  | .ushr => X >>> K
  | .sshr => X.sshiftRight' K
  | .rotl => X <<< K ||| X >>> (128#128 - K)
  | _ => X >>> K ||| X <<< (128#128 - K)

theorem shiftV_eq {op : BinaryOp} {v : Nat} (A : BitVec v) (hv : v ≤ 128) (X : BitVec 128) :
    shiftV op X (A.toNat % 128) = shiftVbv op X (A.setWidth 128 &&& 127#128) := by
  rw [shiftV_bv A hv]; cases op <;> rfl

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

theorem pat_varShift8 (op0 : BinaryOp)
    (hop : op0 = .ishl ∨ op0 = .ushr ∨ op0 = .sshr ∨ op0 = .rotl ∨ op0 = .rotr)
    (xl xh : BitVec 64) (a : BitVec 8) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, ⟨.i8, a⟩]) (Pat.varShiftFull op0 .narrow) = some ρ ∧
      Out128 ρ 3 4 (shiftV op0 (xh ++ xl) (a.toNat % 128)) := by
  rw [shiftV_eq a (by omega)]
  generalize hX : shiftVbv op0 (xh ++ xl) (a.setWidth 128 &&& 127#128) = X
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp only [shiftVbv] at hX <;> vs_fin a

theorem pat_varShift16 (op0 : BinaryOp)
    (hop : op0 = .ishl ∨ op0 = .ushr ∨ op0 = .sshr ∨ op0 = .rotl ∨ op0 = .rotr)
    (xl xh : BitVec 64) (a : BitVec 16) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, ⟨.i16, a⟩]) (Pat.varShiftFull op0 .narrow) = some ρ ∧
      Out128 ρ 3 4 (shiftV op0 (xh ++ xl) (a.toNat % 128)) := by
  rw [shiftV_eq a (by omega)]
  generalize hX : shiftVbv op0 (xh ++ xl) (a.setWidth 128 &&& 127#128) = X
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp only [shiftVbv] at hX <;> vs_fin a

theorem pat_varShift32 (op0 : BinaryOp)
    (hop : op0 = .ishl ∨ op0 = .ushr ∨ op0 = .sshr ∨ op0 = .rotl ∨ op0 = .rotr)
    (xl xh : BitVec 64) (a : BitVec 32) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, ⟨.i32, a⟩]) (Pat.varShiftFull op0 .narrow) = some ρ ∧
      Out128 ρ 3 4 (shiftV op0 (xh ++ xl) (a.toNat % 128)) := by
  rw [shiftV_eq a (by omega)]
  generalize hX : shiftVbv op0 (xh ++ xl) (a.setWidth 128 &&& 127#128) = X
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp only [shiftVbv] at hX <;> vs_fin a

end Opt.Legal

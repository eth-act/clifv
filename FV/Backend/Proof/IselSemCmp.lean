import FV.Backend.Proof.IselContract
import FV.Backend.Proof.IselExtern

/-!
# Flag lemmas for the compare family (`icmp`, `select`, min/max, division checks)

`ConditionHolds` after a flag-setting instruction depends only on the flags it wrote
(`conditionHolds_write_pstate`); on the flags of `subs a, b` (`cmpFlags`) the Arm condition
`condOf cc` is CLIF's `intcc cc` at 32 and 64 bits (`condOn_cmp_32`/`_64`, bit-blasted per
condition code); narrow operands compared after sign/zero extension to 32 bits keep the
comparison (`intcc_signExtend`, `intcc_zeroExtend`); `Cond.invert` negates a condition.
-/

namespace Backend.Proof

open Backend

/-- `ConditionHolds` on explicit flags. -/
def condOn (cond : BitVec 4) (ps : Arm.PState) : Bool :=
  let N := ps.n
  let Z := ps.z
  let C := ps.c
  let V := ps.v
  let result :=
    match (BitVec.extractLsb' 1 3 cond) with
      | 0b000#3 => Z = 1#1
      | 0b001#3 => C = 1#1
      | 0b010#3 => N = 1#1
      | 0b011#3 => V = 1#1
      | 0b100#3 => C = 1#1 ∧ Z = 0#1
      | 0b101#3 => N = V
      | 0b110#3 => N = V ∧ Z = 0#1
      | 0b111#3 => true
  if (Arm.BitVec.lsb cond 0) = 1#1 ∧ cond ≠ 0b1111#4 then
    not result
  else
    result

theorem conditionHolds_write_pstate (c : BitVec 4) (ps : Arm.PState) (w : Arm.ArmState) :
    Arm.ConditionHolds c (Arm.write_pstate ps w) = condOn c ps := by
  simp only [Arm.ConditionHolds, Arm.read_flag, Arm.write_pstate, condOn, Arm.r_of_w_same,
    ne_eq, Arm.StateField.FLAG.injEq, reduceCtorEq, not_false_eq_true, Arm.r_of_w_different]
  rfl

/-- The flags of `subs a, b` (`cmp`). -/
def cmpFlags {n : Nat} (a b : BitVec n) : Arm.PState := (Arm.AddWithCarry a (~~~b) 1#1).2

section Cmp
set_option maxHeartbeats 1000000

theorem condOn_cmp_32 (cc : Clif.IntCC) (a b : BitVec 32) :
    condOn (condOf cc).bits (cmpFlags a b) = Clif.Sem.intcc cc a b := by
  cases cc <;>
    simp only [condOn, condOf, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq,
      Clif.Sem.intcc] <;> bv_decide

theorem condOn_cmp_64 (cc : Clif.IntCC) (a b : BitVec 64) :
    condOn (condOf cc).bits (cmpFlags a b) = Clif.Sem.intcc cc a b := by
  cases cc <;>
    simp only [condOn, condOf, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq,
      Clif.Sem.intcc] <;> bv_decide

end Cmp

/-- Signed conditions (`signed_cond_code`). -/
def signedCC : Clif.IntCC → Bool
  | .slt | .sge | .sgt | .sle => true
  | _ => false

theorem intcc_signExtend_8 (cc : Clif.IntCC) (hs : signedCC cc = true) (a b : BitVec 8) :
    Clif.Sem.intcc cc (a.signExtend 32) (b.signExtend 32) = Clif.Sem.intcc cc a b := by
  cases cc <;> simp [signedCC] at hs <;> simp only [Clif.Sem.intcc] <;> bv_decide

theorem intcc_signExtend_16 (cc : Clif.IntCC) (hs : signedCC cc = true) (a b : BitVec 16) :
    Clif.Sem.intcc cc (a.signExtend 32) (b.signExtend 32) = Clif.Sem.intcc cc a b := by
  cases cc <;> simp [signedCC] at hs <;> simp only [Clif.Sem.intcc] <;> bv_decide

theorem intcc_zeroExtend_8 (cc : Clif.IntCC) (hs : signedCC cc = false) (a b : BitVec 8) :
    Clif.Sem.intcc cc (a.zeroExtend 32) (b.zeroExtend 32) = Clif.Sem.intcc cc a b := by
  cases cc <;> simp [signedCC] at hs <;> simp only [Clif.Sem.intcc] <;> bv_decide

theorem intcc_zeroExtend_16 (cc : Clif.IntCC) (hs : signedCC cc = false) (a b : BitVec 16) :
    Clif.Sem.intcc cc (a.zeroExtend 32) (b.zeroExtend 32) = Clif.Sem.intcc cc a b := by
  cases cc <;> simp [signedCC] at hs <;> simp only [Clif.Sem.intcc] <;> bv_decide

/-- `Cond.invert` negates every condition but `al`/`nv`. -/
theorem condOn_invert (c : Cond) (hc : c ≠ .al ∧ c ≠ .nv) (ps : Arm.PState) :
    condOn c.invert.bits ps = !condOn c.bits ps := by
  obtain ⟨n, z, c', v⟩ := ps
  cases c <;> simp at hc <;>
    simp only [condOn, Cond.invert, Cond.bits] <;> bv_decide

/-- `a ≥ b ↔ a > b - 1` for an unsigned `b ≠ 0` (`emit_icmp` rule 5, `uge` with odd `b`). -/
theorem condOn_hi_pred_32 (a b : BitVec 32) (hb : b ≠ 0) :
    condOn Cond.hi.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .uge a b := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq, Clif.Sem.intcc]
  bv_decide

theorem condOn_hi_pred_64 (a b : BitVec 64) (hb : b ≠ 0) :
    condOn Cond.hi.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .uge a b := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq, Clif.Sem.intcc]
  bv_decide

/-- `a ≥ b ↔ a > b - 1` for a signed `b ≠ MIN` (`emit_icmp` rule 5, `sge` with odd `b`). -/
theorem condOn_gt_pred_32 (a b : BitVec 32) (hb : b ≠ BitVec.intMin 32) :
    condOn Cond.gt.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .sge a b := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq, Clif.Sem.intcc]
  bv_decide

theorem condOn_gt_pred_64 (a b : BitVec 64) (hb : b ≠ BitVec.intMin 64) :
    condOn Cond.gt.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .sge a b := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq, Clif.Sem.intcc]
  bv_decide

/-- `cmp r, #0` then `eq`/`ne`: the register is (non)zero. -/
theorem condOn_cmp_zero_32 (a : BitVec 32) :
    condOn Cond.ne.bits (cmpFlags a 0) = (a != 0) ∧ condOn Cond.eq.bits (cmpFlags a 0) = (a == 0) := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq]
  constructor <;> bv_decide

theorem condOn_cmp_zero_64 (a : BitVec 64) :
    condOn Cond.ne.bits (cmpFlags a 0) = (a != 0) ∧ condOn Cond.eq.bits (cmpFlags a 0) = (a == 0) := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq]
  constructor <;> bv_decide

/-- `tst r, #255` then `ne`: the low byte is non-zero (`is_nonzero` at `i8`). -/
theorem condOn_tst255 (a : BitVec 32) :
    condOn Cond.ne.bits (andsFlags (a &&& BitVec.ofNat 32 255)) = (a.setWidth 8 != 0) := by
  simp only [condOn, Cond.bits, andsFlags, Arm.make_pstate]
  bv_decide

end Backend.Proof

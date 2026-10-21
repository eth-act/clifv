import FV.Backend.Proof.IselSemCmp
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend
/-- Standard-kernel zero flag arithmetic for all comparison widths. -/
theorem stock_cmp_zero_flag {n : Nat} (a b : BitVec n) :
    condOn Cond.eq.bits (cmpFlags a b) = (a == b) := by
  have normalized : condOn Cond.eq.bits (cmpFlags a b) =
      decide ((Arm.AddWithCarry a (~~~b) 1#1).1 = 0) := by
    simp [condOn,Cond.bits,cmpFlags,Arm.AddWithCarry,Arm.make_pstate]
  rw [normalized,Arm.fst_AddWithCarry_eq_sub_neg,BitVec.not_not]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq]
  rw [BitVec.sub_eq_iff_eq_add]
  simp
private theorem unsigned_sum_nat {n : Nat} (width : n = 32 ∨ n = 64) (a b : BitVec n) :
    (a.zeroExtend (n+1) + (~~~b).zeroExtend (n+1) + (1#1).zeroExtend (n+1)).toNat =
      a.toNat + 2^n - b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have notb := (~~~b).isLt
  have extendedA : (a.zeroExtend (n+1)).toNat = a.toNat := BitVec.toNat_setWidth_of_le (by omega)
  have extendedB : ((~~~b).zeroExtend (n+1)).toNat = (~~~b).toNat := BitVec.toNat_setWidth_of_le (by omega)
  have one : ((1#1).zeroExtend (n+1)).toNat = 1 := by rcases width with rfl | rfl <;> rfl
  rw [BitVec.toNat_add,BitVec.toNat_add,extendedA,extendedB,one,BitVec.toNat_not]
  have sumFits : a.toNat + (2^n-1-b.toNat) < 2^(n+1) := by rcases width with rfl | rfl <;> omega
  rw [Nat.mod_eq_of_lt sumFits]
  have sumOneFits : a.toNat + (2^n-1-b.toNat) + 1 < 2^(n+1) := by rcases width with rfl | rfl <;> omega
  rw [Nat.mod_eq_of_lt sumOneFits]
  omega
/-- The actual comparison carry flag recognizes unsigned greater-or-equal;
legacy fixed-width native lemmas remain unchanged. -/
theorem stock_cmp_carry_flag {n : Nat} (width : n = 32 ∨ n = 64) (a b : BitVec n) :
    condOn Cond.hs.bits (cmpFlags a b) = decide (b.toNat ≤ a.toNat) := by
  let unsigned := a.zeroExtend (n+1) + (~~~b).zeroExtend (n+1) + (1#1).zeroExtend (n+1)
  let result := unsigned.zeroExtend n
  have normalized : condOn Cond.hs.bits (cmpFlags a b) = decide (result.zeroExtend (n+1) ≠ unsigned) := by
    simp [condOn,Cond.bits,cmpFlags,Arm.AddWithCarry,Arm.make_pstate,result,unsigned]
    decide
  rw [normalized]
  have value : unsigned.toNat = a.toNat + 2^n - b.toNat := unsigned_sum_nat width a b
  have resultNat : result.toNat = unsigned.toNat % 2^n := by simp [result,BitVec.toNat_setWidth]
  have extendedNat : (result.zeroExtend (n+1)).toNat = result.toNat := BitVec.toNat_setWidth_of_le (by omega)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,ne_eq,← BitVec.toNat_inj,extendedNat,resultNat,value]
  have ha := a.isLt
  have hb := b.isLt
  have power : 0 < 2^n := Nat.two_pow_pos n
  constructor
  · intro different
    by_cases ordered : b.toNat ≤ a.toNat
    · exact ordered
    · have fits : a.toNat + 2^n - b.toNat < 2^n := by omega
      exact False.elim (different (Nat.mod_eq_of_lt fits))
  · intro ordered equal
    have remainder := Nat.mod_lt (a.toNat+2^n-b.toNat) power
    omega
private theorem signed_difference {n : Nat} (width : n = 32 ∨ n = 64) (a b : BitVec n) :
    (a.signExtend (n+1) - b.signExtend (n+1)).toInt = a.toInt-b.toInt := by
  have alo := BitVec.toInt_intMin_le a
  have blo := BitVec.toInt_intMin_le b
  have ahi := BitVec.toInt_lt (x := a)
  have bhi := BitVec.toInt_lt (x := b)
  have positive : 0 < n := by omega
  rw [BitVec.toInt_intMin_of_pos positive] at alo blo
  rw [BitVec.toInt_sub,BitVec.toInt_signExtend_of_le (by omega),BitVec.toInt_signExtend_of_le (by omega)]
  apply Int.bmod_eq_of_le
  all_goals rcases width with rfl | rfl <;> omega
private theorem signed_sum_int {n : Nat} (width : n = 32 ∨ n = 64) (a b : BitVec n) :
    (a.signExtend (n+1) + (~~~b).signExtend (n+1) + (1#1).zeroExtend (n+1)).toInt = a.toInt-b.toInt := by
  have notAdd : (~~~b).signExtend (n+1) + (1#1).zeroExtend (n+1) = -(b.signExtend (n+1)) := by
    rw [BitVec.signExtend_not (by omega)]
    rcases width with rfl | rfl <;> exact (BitVec.neg_eq_not_add _).symm
  rw [BitVec.add_assoc,notAdd,← BitVec.sub_eq_add_neg]
  exact signed_difference width a b
private theorem balanced_difference {n : Nat} (width : n = 32 ∨ n = 64) (a b : BitVec n) :
    (a-b).toInt = if a.toInt-b.toInt < -(2^(n-1) : Int) then a.toInt-b.toInt+2^n
      else if (2^(n-1) : Int) ≤ a.toInt-b.toInt then a.toInt-b.toInt-2^n else a.toInt-b.toInt := by
  have alo := BitVec.toInt_intMin_le a
  have blo := BitVec.toInt_intMin_le b
  have ahi := BitVec.toInt_lt (x := a)
  have bhi := BitVec.toInt_lt (x := b)
  rw [BitVec.toInt_intMin_of_pos (by omega)] at alo blo
  rw [BitVec.toInt_sub]
  split
  · rename_i low
    apply (Int.bmod_eq_iff (Nat.two_pow_pos n)).mpr
    rcases width with rfl | rfl <;> refine ⟨by omega,by omega,1,by omega⟩
  · split
    · rename_i low high
      apply (Int.bmod_eq_iff (Nat.two_pow_pos n)).mpr
      rcases width with rfl | rfl <;> refine ⟨by omega,by omega,-1,by omega⟩
    · rename_i low high
      apply Int.bmod_eq_of_le
      all_goals rcases width with rfl | rfl <;> omega
private theorem last_bit_msb {n : Nat} (a : BitVec n) :
    Arm.BitVec.lsb a (n-1) = BitVec.ofBool a.msb := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bounded
  have zero : i = 0 := by omega
  subst i
  simp [Arm.BitVec.lsb,BitVec.msb_eq_getLsbD_last]
/-- Signed greater-or-equal follows the actual negative/overflow flags using
ordinary integer bounds, including both signed subtraction overflow regions. -/
theorem stock_cmp_signed_ge_flag {n : Nat} (width : n = 32 ∨ n = 64) (a b : BitVec n) :
    condOn Cond.ge.bits (cmpFlags a b) = decide (b.toInt ≤ a.toInt) := by
  let result := a-b
  let signed := a.signExtend (n+1) + (~~~b).signExtend (n+1) + (1#1).zeroExtend (n+1)
  have value : (Arm.AddWithCarry a (~~~b) 1#1).1 = result := by
    rw [Arm.fst_AddWithCarry_eq_sub_neg,BitVec.not_not]
  have signedInt : signed.toInt = a.toInt-b.toInt := signed_sum_int width a b
  have negative : (cmpFlags a b).n = BitVec.ofBool (decide (result.toInt < 0)) := by
    change Arm.BitVec.lsb (Arm.AddWithCarry a (~~~b) 1#1).1 (n-1) = _
    rw [value,last_bit_msb,BitVec.msb_eq_toInt]
  have overflow : (cmpFlags a b).v = BitVec.ofBool (decide (result.toInt ≠ a.toInt-b.toInt)) := by
    change (if (Arm.AddWithCarry a (~~~b) 1#1).1.signExtend (n+1) = signed then 0#1 else 1#1) = _
    rw [value]
    have same : result.signExtend (n+1) = signed ↔ result.toInt = a.toInt-b.toInt := by
      rw [← BitVec.toInt_inj,BitVec.toInt_signExtend_of_le (by omega),signedInt]
    simp only [same]
    by_cases equal : result.toInt = a.toInt-b.toInt <;> simp [equal]
  have normalized : condOn Cond.ge.bits (cmpFlags a b) = decide ((cmpFlags a b).n = (cmpFlags a b).v) := by
    simp [condOn,Cond.bits]
    decide
  rw [normalized,negative,overflow]
  simp only [BitVec.ofBool_eq_iff_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  have balanced := balanced_difference width a b
  change result.toInt = _ at balanced
  rw [balanced]
  have alo := BitVec.toInt_intMin_le a
  have blo := BitVec.toInt_intMin_le b
  have ahi := BitVec.toInt_lt (x := a)
  have bhi := BitVec.toInt_lt (x := b)
  rw [BitVec.toInt_intMin_of_pos (by omega)] at alo blo
  by_cases low : a.toInt-b.toInt < -(2^(n-1) : Int)
  all_goals by_cases high : (2^(n-1) : Int) ≤ a.toInt-b.toInt
  all_goals simp only [low,high,ite_true,ite_false]
  all_goals rcases width with rfl | rfl <;> omega
private theorem one_bit_cases (x : BitVec 1) : x = 0 ∨ x = 1 := by
  have bound := x.isLt
  have cases : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases cases with zero | one
  · left; apply BitVec.eq_of_toNat_eq; exact zero
  · right; apply BitVec.eq_of_toNat_eq; exact one
private theorem condition_relations (ps : Arm.PState) :
    condOn Cond.ne.bits ps = !condOn Cond.eq.bits ps ∧
    condOn Cond.lo.bits ps = !condOn Cond.hs.bits ps ∧
    condOn Cond.hi.bits ps = (condOn Cond.hs.bits ps && !condOn Cond.eq.bits ps) ∧
    condOn Cond.ls.bits ps = !(condOn Cond.hs.bits ps && !condOn Cond.eq.bits ps) ∧
    condOn Cond.lt.bits ps = !condOn Cond.ge.bits ps ∧
    condOn Cond.gt.bits ps = (condOn Cond.ge.bits ps && !condOn Cond.eq.bits ps) ∧
    condOn Cond.le.bits ps = !(condOn Cond.ge.bits ps && !condOn Cond.eq.bits ps) := by
  obtain ⟨n,z,c,v⟩ := ps
  rcases one_bit_cases n with rfl | rfl <;>
    rcases one_bit_cases z with rfl | rfl <;>
    rcases one_bit_cases c with rfl | rfl <;>
    rcases one_bit_cases v with rfl | rfl <;> decide +kernel
/-- All ten original integer comparison predicates agree with actual Arm
subtraction flags, using standard-kernel arithmetic at both machine widths. -/
theorem stock_cmp_conditions {n : Nat} (width : n = 32 ∨ n = 64)
    (cc : Clif.IntCC) (a b : BitVec n) :
    condOn (condOf cc).bits (cmpFlags a b) = Clif.Sem.intcc cc a b := by
  obtain ⟨ne,lo,hi,ls,lt,gt,le⟩ := condition_relations (cmpFlags a b)
  have equalNat : (a == b) = decide (a.toNat = b.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq,BitVec.toNat_inj]
  have equalInt : (a == b) = decide (a.toInt = b.toInt) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq,BitVec.toInt_inj]
  cases cc <;> simp only [condOf,Clif.Sem.intcc]
  all_goals simp only [ne,lo,hi,ls,lt,gt,le,stock_cmp_zero_flag,
    stock_cmp_carry_flag width,stock_cmp_signed_ge_flag width]
  all_goals first
    | rfl
    | (apply Bool.eq_iff_iff.mpr
       first
       | (simp only [equalInt,BitVec.slt,BitVec.sle,Bool.and_eq_true,Bool.not_eq_true,not_decide_eq_true,Bool.not_and,Bool.or_eq_true,Bool.not_not,bne_iff_ne,beq_iff_eq,
            decide_eq_true_eq,decide_eq_false_iff_not]; omega)
       | (simp only [equalNat,BitVec.ult,BitVec.ule,Bool.and_eq_true,Bool.not_eq_true,not_decide_eq_true,Bool.not_and,Bool.or_eq_true,Bool.not_not,bne_iff_ne,beq_iff_eq,
            decide_eq_true_eq,decide_eq_false_iff_not]; omega))
/-- Standard-kernel extension preserves every signed comparison predicate. -/
theorem stock_cmp_signed_extension {n m : Nat} (bounded : n ≤ m)
    (cc : Clif.IntCC) (signed : signedCC cc = true) (a b : BitVec n) :
    Clif.Sem.intcc cc (a.signExtend m) (b.signExtend m) = Clif.Sem.intcc cc a b := by
  cases cc <;> simp [signedCC] at signed <;>
    simp [Clif.Sem.intcc,BitVec.slt,BitVec.sle,BitVec.toInt_signExtend_of_le bounded]
/-- Standard-kernel extension preserves every unsigned comparison predicate. -/
theorem stock_cmp_unsigned_extension {n m : Nat} (bounded : n ≤ m)
    (cc : Clif.IntCC) (unsigned : signedCC cc = false) (a b : BitVec n) :
    Clif.Sem.intcc cc (a.zeroExtend m) (b.zeroExtend m) = Clif.Sem.intcc cc a b := by
  have equal : a.zeroExtend m = b.zeroExtend m ↔ a = b := by
    rw [← BitVec.toNat_inj,BitVec.toNat_setWidth_of_le bounded,BitVec.toNat_setWidth_of_le bounded,BitVec.toNat_inj]
  cases cc <;> simp [signedCC] at unsigned <;>
    (try simp only [Clif.Sem.intcc,BitVec.ult,BitVec.ule,BitVec.toNat_setWidth_of_le bounded])
  all_goals first
    | rfl
    | (apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq,bne_iff_ne,decide_eq_true_eq]; simpa only [BitVec.zeroExtend] using equal)
    | (apply congrArg Bool.not; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; exact equal)
/-- The odd-immediate unsigned comparison rewrite preserves the original
predicate without changing its nonzero guard. -/
theorem stock_cmp_unsigned_predecessor {n : Nat} (width : n = 32 ∨ n = 64)
    (a b : BitVec n) (nonzero : b ≠ 0) :
    condOn Cond.hi.bits (cmpFlags a (b-1)) = Clif.Sem.intcc .uge a b := by
  have positive : 0 < b.toNat := by
    have noZero : b.toNat ≠ 0 := by intro zero; apply nonzero; apply BitVec.eq_of_toNat_eq; exact zero
    omega
  have value : (b-1).toNat = b.toNat-1 := by
    have one : (1 : BitVec n).toNat = 1 := by rcases width with rfl | rfl <;> rfl
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def,one]; omega),one]
  have flags := stock_cmp_conditions width .ugt a (b-1)
  change condOn Cond.hi.bits (cmpFlags a (b-1)) = _ at flags
  rw [flags]
  apply Bool.eq_iff_iff.mpr
  simp only [Clif.Sem.intcc,BitVec.ult,BitVec.ule,decide_eq_true_eq,value]
  omega
/-- The signed predecessor rewrite is valid at every original operand except
signed minimum, exactly the existing helper guard. -/
theorem stock_cmp_signed_predecessor {n : Nat} (width : n = 32 ∨ n = 64)
    (a b : BitVec n) (notMinimum : b ≠ BitVec.intMin n) :
    condOn Cond.gt.bits (cmpFlags a (b-1)) = Clif.Sem.intcc .sge a b := by
  have lower := BitVec.toInt_intMin_le b
  have upper := BitVec.toInt_lt (x := b)
  have minInt := BitVec.toInt_intMin_of_pos (v := n) (by omega)
  rw [minInt] at lower
  have excluded : b.toInt ≠ -(2^(n-1) : Int) := by
    intro equal
    apply notMinimum
    apply BitVec.toInt_inj.mp
    exact equal.trans minInt.symm
  have value : (b-1).toInt = b.toInt-1 := by
    rw [BitVec.toInt_sub]
    have one : (1 : BitVec n).toInt = 1 := by rcases width with rfl | rfl <;> rfl
    rw [one]
    apply Int.bmod_eq_of_le
    all_goals rcases width with rfl | rfl <;> omega
  have flags := stock_cmp_conditions width .sgt a (b-1)
  change condOn Cond.gt.bits (cmpFlags a (b-1)) = _ at flags
  rw [flags]
  apply Bool.eq_iff_iff.mpr
  simp only [Clif.Sem.intcc,BitVec.slt,BitVec.sle,decide_eq_true_eq,value]
  omega
/-- Inversion of a valid Arm condition, using a closed standard-kernel
case split on its four one-bit flags; old native variants are preserved. -/
theorem stock_cmp_condition_invert (c : Cond) (valid : c ≠ .al ∧ c ≠ .nv) (ps : Arm.PState) :
    condOn c.invert.bits ps = !condOn c.bits ps := by
  obtain ⟨n,z,carry,v⟩ := ps
  rcases one_bit_cases n with rfl | rfl <;>
    rcases one_bit_cases z with rfl | rfl <;>
    rcases one_bit_cases carry with rfl | rfl <;>
    rcases one_bit_cases v with rfl | rfl <;>
    cases c <;> (try simp at valid) <;> decide +kernel
end Backend.Stock.Proof.ScalarCmp

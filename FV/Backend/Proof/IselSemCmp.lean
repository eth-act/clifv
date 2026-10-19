import FV.Backend.Proof.IselContract
import FV.Backend.Proof.IselExtern

/-!
# Flag lemmas for the compare family (`icmp`, `select`, min/max, division checks)

`ConditionHolds` after a flag-setting instruction depends only on the flags it wrote
(`conditionHolds_write_pstate`); on the flags of `subs a, b` (`cmpFlags`) the Arm condition
`condOf cc` is CLIF's `intcc cc` at 32 and 64 bits (`condOn_cmp_32`/`_64`, from the flags read as
arithmetic facts: `Z` is `a = b`, `C` is `b ≤ a` unsigned, `N = V` is `b ≤ a` signed); narrow
operands compared after sign/zero extension to 32 bits keep the
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

/-! ### The flags of `cmpFlags`, as arithmetic facts (32 and 64 bits) -/

private theorem not_toInt {n : Nat} (hn : n = 32 ∨ n = 64) (b : BitVec n) :
    (~~~b).toInt = -b.toInt - 1 := by
  rcases hn with rfl | rfl <;>
  · rw [BitVec.toInt_not]
    simp only [BitVec.toInt_eq_toNat_cond, Int.bmod_def]
    have := b.isLt
    split <;> split <;> omega

private theorem toInt_cases {n : Nat} (a : BitVec n) :
    (2 * a.toNat < 2 ^ n ∧ a.toInt = a.toNat) ∨ (2 ^ n ≤ 2 * a.toNat ∧ a.toInt = a.toNat - 2 ^ n) := by
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · exact .inl ⟨‹_›, rfl⟩
  · exact .inr ⟨by omega, by simp⟩

private theorem cmpFlags_z {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) :
    (cmpFlags a b).z = if a = b then 1#1 else 0#1 := by
  rcases hn with rfl | rfl <;>
  · simp only [cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq]
    split <;> split <;> bv_omega

private theorem cmpFlags_c {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) :
    (cmpFlags a b).c = if b.toNat ≤ a.toNat then 1#1 else 0#1 := by
  rcases hn with rfl | rfl <;>
  · simp only [cmpFlags, Arm.AddWithCarry, Arm.make_pstate]
    split <;> split <;> bv_omega

/-- The overflow flag of `subs a, b`: set iff `a - b` leaves the signed range. -/
private theorem cmpFlags_v {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) :
    (cmpFlags a b).v =
      if -2 ^ (n - 1) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ (n - 1) then 0#1 else 1#1 := by
  have hr := Arm.fst_AddWithCarry_eq_sub_neg a (~~~b)
  simp only [cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.not_not] at hr ⊢
  rw [hr]
  have h1 := BitVec.toInt_lt (x := a); have h2 := BitVec.le_toInt a
  have h3 := BitVec.toInt_lt (x := b); have h4 := BitVec.le_toInt b
  have hnb := not_toInt hn b
  congr 1
  apply propext
  rw [← BitVec.toInt_inj]
  rcases hn with rfl | rfl <;>
  · rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_add, BitVec.toInt_add,
      BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_signExtend_of_le (by decide),
      BitVec.toInt_sub, hnb, BitVec.toInt_setWidth]
    simp only [Int.bmod_def] at *
    simp only [Nat.reduceSub, Nat.reducePow, Nat.reduceAdd, BitVec.toNat_ofNat] at *
    repeat' split
    all_goals omega

private theorem cmpFlags_n {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) :
    (cmpFlags a b).n = if 2 ^ (n - 1) ≤ (a - b).toNat then 1#1 else 0#1 := by
  have hr := Arm.fst_AddWithCarry_eq_sub_neg a (~~~b)
  simp only [cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.not_not] at hr ⊢
  rw [hr]
  apply BitVec.eq_of_toNat_eq
  generalize a - b = r
  rcases hn with rfl | rfl <;>
  · have := r.isLt
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    split <;> simp <;> omega

private theorem cmpFlags_nv {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) :
    ((cmpFlags a b).n = (cmpFlags a b).v) ↔ b.toInt ≤ a.toInt := by
  rw [cmpFlags_n hn, cmpFlags_v hn]
  have ha := toInt_cases a; have hb := toInt_cases b
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h1 : 2 ^ (n - 1) ≤ (2 ^ n - b.toNat + a.toNat) % 2 ^ n <;>
  by_cases h2 : -2 ^ (n - 1) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ (n - 1) <;>
  simp only [h1, h2, ite_true, ite_false] <;> simp <;> rcases hn with rfl | rfl <;> omega

/-- `condOn` on each condition, with the encoding decoded. -/
private def condSpec : Cond → Arm.PState → Bool
  | .eq, ps => ps.z = 1#1
  | .ne, ps => !(ps.z = 1#1)
  | .hs, ps => ps.c = 1#1
  | .lo, ps => !(ps.c = 1#1)
  | .mi, ps => ps.n = 1#1
  | .pl, ps => !(ps.n = 1#1)
  | .vs, ps => ps.v = 1#1
  | .vc, ps => !(ps.v = 1#1)
  | .hi, ps => ps.c = 1#1 ∧ ps.z = 0#1
  | .ls, ps => !(ps.c = 1#1 ∧ ps.z = 0#1)
  | .ge, ps => ps.n = ps.v
  | .lt, ps => !(ps.n = ps.v)
  | .gt, ps => ps.n = ps.v ∧ ps.z = 0#1
  | .le, ps => !(ps.n = ps.v ∧ ps.z = 0#1)
  | .al, _ => true
  | .nv, _ => true

private theorem condOn_spec (c : Cond) (ps : Arm.PState) : condOn c.bits ps = condSpec c ps := by
  cases c <;> rfl

private theorem condOn_cmp {n : Nat} (hn : n = 32 ∨ n = 64) (cc : Clif.IntCC) (a b : BitVec n) :
    condOn (condOf cc).bits (cmpFlags a b) = Clif.Sem.intcc cc a b := by
  have hz := cmpFlags_z hn a b; have hc := cmpFlags_c hn a b; have hnv := cmpFlags_nv hn a b
  rw [condOn_spec]
  generalize cmpFlags a b = ps at *
  obtain ⟨N, Z, C, V⟩ := ps
  simp only at hz hc hnv
  subst hz hc
  cases cc <;> simp [condOf, condSpec, Clif.Sem.intcc, hnv, BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule]
  all_goals
    rw [Bool.eq_iff_iff]
    first
    | (simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not, BitVec.le_def, BitVec.lt_def, BitVec.toNat_eq, beq_iff_eq,
        bne_eq_false_iff_eq] <;> omega)
    | (simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not, ← BitVec.toInt_inj]; omega)

theorem condOn_cmp_32 (cc : Clif.IntCC) (a b : BitVec 32) :
    condOn (condOf cc).bits (cmpFlags a b) = Clif.Sem.intcc cc a b :=
  condOn_cmp (.inl rfl) cc a b

theorem condOn_cmp_64 (cc : Clif.IntCC) (a b : BitVec 64) :
    condOn (condOf cc).bits (cmpFlags a b) = Clif.Sem.intcc cc a b :=
  condOn_cmp (.inr rfl) cc a b

/-- Signed conditions (`signed_cond_code`). -/
def signedCC : Clif.IntCC → Bool
  | .slt | .sge | .sgt | .sle => true
  | _ => false

private theorem intcc_signExtend {w : Nat} (hw : w ≤ 32) (cc : Clif.IntCC) (hs : signedCC cc = true)
    (a b : BitVec w) :
    Clif.Sem.intcc cc (a.signExtend 32) (b.signExtend 32) = Clif.Sem.intcc cc a b := by
  cases cc <;> simp [signedCC] at hs <;>
    simp only [Clif.Sem.intcc, BitVec.slt, BitVec.sle, BitVec.toInt_signExtend_of_le hw]

private theorem intcc_zeroExtend {w : Nat} (hw : w = 8 ∨ w = 16) (cc : Clif.IntCC)
    (hs : signedCC cc = false) (a b : BitVec w) :
    Clif.Sem.intcc cc (a.zeroExtend 32) (b.zeroExtend 32) = Clif.Sem.intcc cc a b := by
  have ha : (a.setWidth 32).toNat = a.toNat := by
    have := a.isLt; rcases hw with rfl | rfl <;> simp only [BitVec.toNat_setWidth] <;> omega
  have hb : (b.setWidth 32).toNat = b.toNat := by
    have := b.isLt; rcases hw with rfl | rfl <;> simp only [BitVec.toNat_setWidth] <;> omega
  have he : (a.setWidth 32 = b.setWidth 32) ↔ a = b := by
    rw [BitVec.toNat_eq, BitVec.toNat_eq, ha, hb]
  cases cc <;> simp [signedCC] at hs <;> simp only [Clif.Sem.intcc, BitVec.ult, BitVec.ule, ha, hb] <;>
    (rw [Bool.eq_iff_iff]; simp [he])

theorem intcc_signExtend_8 (cc : Clif.IntCC) (hs : signedCC cc = true) (a b : BitVec 8) :
    Clif.Sem.intcc cc (a.signExtend 32) (b.signExtend 32) = Clif.Sem.intcc cc a b :=
  intcc_signExtend (by decide) cc hs a b

theorem intcc_signExtend_16 (cc : Clif.IntCC) (hs : signedCC cc = true) (a b : BitVec 16) :
    Clif.Sem.intcc cc (a.signExtend 32) (b.signExtend 32) = Clif.Sem.intcc cc a b :=
  intcc_signExtend (by decide) cc hs a b

theorem intcc_zeroExtend_8 (cc : Clif.IntCC) (hs : signedCC cc = false) (a b : BitVec 8) :
    Clif.Sem.intcc cc (a.zeroExtend 32) (b.zeroExtend 32) = Clif.Sem.intcc cc a b :=
  intcc_zeroExtend (.inl rfl) cc hs a b

theorem intcc_zeroExtend_16 (cc : Clif.IntCC) (hs : signedCC cc = false) (a b : BitVec 16) :
    Clif.Sem.intcc cc (a.zeroExtend 32) (b.zeroExtend 32) = Clif.Sem.intcc cc a b :=
  intcc_zeroExtend (.inr rfl) cc hs a b

/-- `Cond.invert` negates every condition but `al`/`nv`. -/
theorem condOn_invert (c : Cond) (hc : c ≠ .al ∧ c ≠ .nv) (ps : Arm.PState) :
    condOn c.invert.bits ps = !condOn c.bits ps := by
  rw [condOn_spec, condOn_spec]
  cases c <;> simp at hc <;> simp [Cond.invert, condSpec]

private theorem condOn_hi_pred {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n) (hb : b ≠ 0) :
    condOn Cond.hi.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .uge a b := by
  rw [condOn_spec]
  simp only [condSpec, cmpFlags_c hn, cmpFlags_z hn, Clif.Sem.intcc, BitVec.ule]
  rcases hn with rfl | rfl <;>
  · by_cases h1 : (b - 1).toNat ≤ a.toNat <;> by_cases h2 : a = b - 1 <;>
      simp only [h1, h2, ite_true, ite_false] <;> simp <;> bv_omega

/-- `a ≥ b ↔ a > b - 1` for an unsigned `b ≠ 0` (`emit_icmp` rule 5, `uge` with odd `b`). -/
theorem condOn_hi_pred_32 (a b : BitVec 32) (hb : b ≠ 0) :
    condOn Cond.hi.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .uge a b :=
  condOn_hi_pred (.inl rfl) a b hb

theorem condOn_hi_pred_64 (a b : BitVec 64) (hb : b ≠ 0) :
    condOn Cond.hi.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .uge a b :=
  condOn_hi_pred (.inr rfl) a b hb

private theorem condOn_gt_pred {n : Nat} (hn : n = 32 ∨ n = 64) (a b : BitVec n)
    (hb : b ≠ BitVec.intMin n) :
    condOn Cond.gt.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .sge a b := by
  rw [condOn_spec]
  simp only [condSpec, cmpFlags_nv hn, cmpFlags_z hn, Clif.Sem.intcc, BitVec.sle]
  have hbi : b.toInt ≠ (BitVec.intMin n).toInt := fun h => hb (BitVec.toInt_inj.mp h)
  have h1 := BitVec.toInt_lt (x := b); have h2 := BitVec.le_toInt b
  have hsub : (b - 1).toInt = b.toInt - 1 := by
    rw [BitVec.toInt_sub]
    rcases hn with rfl | rfl <;>
    · rw [BitVec.toInt_intMin] at hbi
      rw [show (1 : BitVec _).toInt = 1 from rfl, Int.bmod_def]
      simp only [Nat.reduceSub, Nat.reducePow, Nat.reduceMod] at *
      split <;> omega
  have he : a = b - 1 ↔ a.toInt = b.toInt - 1 := by rw [← BitVec.toInt_inj, hsub]
  simp only [hsub, he]
  by_cases h3 : b.toInt - 1 ≤ a.toInt <;> by_cases h4 : a.toInt = b.toInt - 1 <;>
    simp only [h3, h4, ite_true, ite_false] <;> simp <;> omega

/-- `a ≥ b ↔ a > b - 1` for a signed `b ≠ MIN` (`emit_icmp` rule 5, `sge` with odd `b`). -/
theorem condOn_gt_pred_32 (a b : BitVec 32) (hb : b ≠ BitVec.intMin 32) :
    condOn Cond.gt.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .sge a b :=
  condOn_gt_pred (.inl rfl) a b hb

theorem condOn_gt_pred_64 (a b : BitVec 64) (hb : b ≠ BitVec.intMin 64) :
    condOn Cond.gt.bits (cmpFlags a (b - 1)) = Clif.Sem.intcc .sge a b :=
  condOn_gt_pred (.inr rfl) a b hb

private theorem condOn_cmp_zero {n : Nat} (hn : n = 32 ∨ n = 64) (a : BitVec n) :
    condOn Cond.ne.bits (cmpFlags a 0) = (a != 0) ∧ condOn Cond.eq.bits (cmpFlags a 0) = (a == 0) := by
  rw [condOn_spec, condOn_spec]
  simp only [condSpec, cmpFlags_z hn]
  constructor <;> rw [Bool.eq_iff_iff] <;> by_cases h : a = 0#n <;> simp [h]

/-- `cmp r, #0` then `eq`/`ne`: the register is (non)zero. -/
theorem condOn_cmp_zero_32 (a : BitVec 32) :
    condOn Cond.ne.bits (cmpFlags a 0) = (a != 0) ∧ condOn Cond.eq.bits (cmpFlags a 0) = (a == 0) :=
  condOn_cmp_zero (.inl rfl) a

theorem condOn_cmp_zero_64 (a : BitVec 64) :
    condOn Cond.ne.bits (cmpFlags a 0) = (a != 0) ∧ condOn Cond.eq.bits (cmpFlags a 0) = (a == 0) :=
  condOn_cmp_zero (.inr rfl) a

/-- `tst r, #255` then `ne`: the low byte is non-zero (`is_nonzero` at `i8`). -/
theorem condOn_tst255 (a : BitVec 32) :
    condOn Cond.ne.bits (andsFlags (a &&& BitVec.ofNat 32 255)) = (a.setWidth 8 != 0) := by
  rw [condOn_spec]
  have hand : (a &&& BitVec.ofNat 32 255).toNat = a.toNat % 256 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod a.toNat 8
  simp only [condSpec, andsFlags, Arm.make_pstate]
  by_cases h : a &&& BitVec.ofNat 32 255 = 0#32 <;> simp [h] <;> bv_omega

end Backend.Proof

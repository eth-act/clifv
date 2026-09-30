import FV.Opt.Proof.LegalArith

/-!
# Variable-amount `i128` shifts and rotates (`Opt.Legal.Pat.varShiftFull`)

Split from `LegalArith.lean`; the per-width pattern theorems are in `LegalShift8/16/32/64`.

`bv_decide` on the whole 128-bit identity with a 128-bit amount runs out of memory. The proofs
here keep the SAT problems small:

* `ishl`/`ushr`/`sshr`: the source shift by `A mod 128` is a shift by the 7-bit vector
  `A.setWidth 7` (`shiftV_eq`); the 128-bit barrel shifter over 7 amount bits is small.
* `rotl`/`rotr`: the halves of a 128-bit left rotation by `n < 128` are proved bit by bit
  (`rotl_lo`, `rotl_hi`) as 64-bit shift formulas; rewritten with a 64-bit amount
  (`rotl_lo_bv`, `rotl_hi_bv`), the remaining identities are 64-bit ones. A right rotation by
  `n` is the left rotation by `(128 - n) % 128` (`rotateRight_eq`), the amount `rotr`'s
  prefix computes (`rotrAmt`).
-/

namespace Opt.Legal

open Clif

set_option maxHeartbeats 4000000

/-- The source shifts at `i128`, by an amount `n < 128`. -/
def shiftV (op : BinaryOp) (X : BitVec 128) (n : Nat) : BitVec 128 :=
  match op with
  | .ishl => X <<< n
  | .ushr => X >>> n
  | .sshr => X.sshiftRight n
  | .rotl => X.rotateLeft n
  | _ => X.rotateRight n

/-! ## Shifts: a 7-bit amount -/

/-- The source shift (`ishl`/`ushr`/`sshr`) by a 7-bit amount. -/
def shiftVbv (op : BinaryOp) (X : BitVec 128) (K : BitVec 7) : BitVec 128 :=
  match op with
  | .ishl => X <<< K
  | .ushr => X >>> K
  | _ => X.sshiftRight' K

theorem shiftV_eq {op : BinaryOp} (hop : op = .ishl ∨ op = .ushr ∨ op = .sshr) {v : Nat}
    (A : BitVec v) (X : BitVec 128) :
    shiftV op X (A.toNat % 128) = shiftVbv op X (A.setWidth 7) := by
  have hk : (A.setWidth 7).toNat = A.toNat % 128 := by rw [BitVec.toNat_setWidth]
  rcases hop with rfl | rfl | rfl <;>
    simp only [shiftV, shiftVbv, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
      BitVec.sshiftRight', hk]

/-! ## Rotations: halves bit by bit -/

theorem getLsbD_idx {w : Nat} (x : BitVec w) {i j : Nat} (h : i = j) :
    x.getLsbD i = x.getLsbD j := by
  rw [h]

theorem rotl_lo (xl xh : BitVec 64) (n : Nat) (hn : n < 128) :
    ((xh ++ xl).rotateLeft n).extractLsb' 0 64 =
      if n < 64 then xl <<< n ||| xh >>> (64 - n) else xh <<< (n - 64) ||| xl >>> (128 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and, Nat.zero_add, Nat.mod_eq_of_lt (show n < 64 + 64 by omega)]
  by_cases h2 : n < 64
  · simp only [h2, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
    by_cases h1 : i < n
    · simp only [h1, ite_true, show ¬ (64 + 64 - n + i < 64) by omega, ite_false,
        decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
      exact getLsbD_idx _ (by omega)
    · simp only [h1, ite_false, show i < 64 + 64 by omega, show i - n < 64 by omega,
        decide_true, decide_false, Bool.not_false, Bool.true_and, ite_true,
        BitVec.getLsbD_of_ge xh (64 - n + i) (by omega), Bool.or_false]
  · simp only [h2, ite_false, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, show i < n by omega]
    by_cases h3 : i < n - 64
    · simp only [show 64 + 64 - n + i < 64 by omega, ite_true, h3, decide_true, Bool.not_true,
        Bool.false_and, Bool.false_or]
    · simp only [show ¬ (64 + 64 - n + i < 64) by omega, ite_false, h3, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge xl (128 - n + i) (by omega),
        Bool.or_false]
      exact getLsbD_idx _ (by omega)

theorem rotl_hi (xl xh : BitVec 64) (n : Nat) (hn : n < 128) :
    ((xh ++ xl).rotateLeft n).extractLsb' 64 64 =
      if n < 64 then xh <<< n ||| xl >>> (64 - n) else xl <<< (n - 64) ||| xh >>> (128 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and, Nat.mod_eq_of_lt (show n < 64 + 64 by omega)]
  by_cases h2 : n < 64
  · simp only [h2, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, show ¬ (64 + i < n) by omega,
      ite_false, show 64 + i < 64 + 64 by omega]
    by_cases h1 : i < n
    · simp only [h1, show 64 + i - n < 64 by omega, ite_true, decide_true, Bool.not_true,
        Bool.false_and, Bool.false_or]
      exact getLsbD_idx _ (by omega)
    · simp only [h1, show ¬ (64 + i - n < 64) by omega, ite_false, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge xl (64 - n + i) (by omega),
        Bool.or_false]
      exact getLsbD_idx _ (by omega)
  · simp only [h2, ite_false, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
    by_cases h3 : i < n - 64
    · simp only [show 64 + i < n by omega, ite_true, show ¬ (64 + 64 - n + (64 + i) < 64) by omega,
        ite_false, h3, decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
      exact getLsbD_idx _ (by omega)
    · simp only [show ¬ (64 + i < n) by omega, ite_false, show 64 + i < 64 + 64 by omega,
        show 64 + i - n < 64 by omega, ite_true, h3, decide_true, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge xh (128 - n + i) (by omega),
        Bool.or_false]
      exact getLsbD_idx _ (by omega)

/-- A right rotation is a left rotation by the complementary amount. -/
theorem rotateRight_eq (X : BitVec 128) {n : Nat} (hn : n < 128) :
    X.rotateRight n = X.rotateLeft ((128 - n) % 128) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hn, Nat.mod_mod]
  by_cases h0 : n = 0
  · subst h0; simp [hi]
  · rw [Nat.mod_eq_of_lt (show 128 - n < 128 by omega)]
    by_cases h : i < 128 - n
    · rw [if_pos h, if_pos h]; exact getLsbD_idx _ (by omega)
    · rw [if_neg h, if_neg h]

/-! ## Rotations: 64-bit amounts -/

/-- The low half of a left rotation by the 64-bit amount `K < 128`. -/
def rotLo (xl xh K : BitVec 64) : BitVec 64 :=
  if K < 64#64 then xl <<< K ||| xh >>> (64#64 - K) else xh <<< (K - 64#64) ||| xl >>> (128#64 - K)

/-- The high half of a left rotation by the 64-bit amount `K < 128`. -/
def rotHi (xl xh K : BitVec 64) : BitVec 64 :=
  if K < 64#64 then xh <<< K ||| xl >>> (64#64 - K) else xl <<< (K - 64#64) ||| xh >>> (128#64 - K)

theorem toNat_64sub {K : BitVec 64} (h : K.toNat ≤ 64) : (64#64 - K).toNat = 64 - K.toNat := by
  rw [BitVec.toNat_sub]; simp; omega

theorem toNat_sub64 {K : BitVec 64} (h : 64 ≤ K.toNat) : (K - 64#64).toNat = K.toNat - 64 := by
  rw [BitVec.toNat_sub]; simp; omega

theorem toNat_128sub {K : BitVec 64} (h : K.toNat ≤ 128) : (128#64 - K).toNat = 128 - K.toNat := by
  rw [BitVec.toNat_sub]; simp; omega

theorem rotl_lo_bv (xl xh K : BitVec 64) (hK : K.toNat < 128) :
    ((xh ++ xl).rotateLeft K.toNat).extractLsb' 0 64 = rotLo xl xh K := by
  rw [rotl_lo _ _ _ hK, rotLo]
  by_cases h : K.toNat < 64
  · rw [if_pos h, if_pos (by rw [BitVec.lt_def]; simpa using h), BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', toNat_64sub (by omega)]
  · rw [if_neg h, if_neg (by rw [BitVec.lt_def]; simpa using h), BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', toNat_sub64 (by omega), toNat_128sub (by omega)]

theorem rotl_hi_bv (xl xh K : BitVec 64) (hK : K.toNat < 128) :
    ((xh ++ xl).rotateLeft K.toNat).extractLsb' 64 64 = rotHi xl xh K := by
  rw [rotl_hi _ _ _ hK, rotHi]
  by_cases h : K.toNat < 64
  · rw [if_pos h, if_pos (by rw [BitVec.lt_def]; simpa using h), BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', toNat_64sub (by omega)]
  · rw [if_neg h, if_neg (by rw [BitVec.lt_def]; simpa using h), BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', toNat_sub64 (by omega), toNat_128sub (by omega)]

/-- The 64-bit amount of a variable shift of an amount `a` (at most 64 bits): `uextend`, then
`band 127`. -/
def amtK {v : Nat} (a : BitVec v) : BitVec 64 := a.setWidth 64 &&& 127#64

theorem amtK_toNat {v : Nat} (hv : v ≤ 64) (a : BitVec v) : (amtK a).toNat = a.toNat % 128 := by
  have ha : a.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) hv)
  rw [amtK, BitVec.toNat_and, BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha]
  show a.toNat &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- The amount `rotr`'s prefix computes: `0` stays, else `128 - K`. -/
def rotrAmt (K : BitVec 64) : BitVec 64 := if K = 0#64 then K else 128#64 - K

theorem rotrAmt_toNat {K : BitVec 64} (hK : K.toNat < 128) :
    (rotrAmt K).toNat = (128 - K.toNat) % 128 := by
  unfold rotrAmt
  by_cases h : K = 0#64
  · rw [if_pos h, h]; rfl
  · rw [if_neg h, toNat_128sub (by omega)]
    have : K.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    rw [Nat.mod_eq_of_lt (by omega)]

/-! ## The proof steps of a pattern theorem -/

/-- Unfold the variable-shift pattern. -/
macro "vs_unfold" : tactic => `(tactic|
  simp only [Pat.varShiftFull, Pat.amt, Pat.varShift, Pat.cross, List.cons_append,
    List.nil_append, reduceCtorEq, beq_iff_eq, ite_false, ite_true, beq_self_eq_true])

/-- The 64-bit operations of a run, in `bv_decide`'s fragment. -/
macro "vs_sem" : tactic => `(tactic|
  simp only [ishl64, ushr64, sshr64, Sem.binary, Sem.bor, Sem.band, Sem.isub, select_bif,
    Sem.icmp, Sem.intcc, bool8_eq, Sem.uextend])

/-- A variable shift (`ishl`/`ushr`/`sshr`) by the amount `a`: the whole run, the source value
generalised, then the identities with the 7-bit amount. -/
macro "vs_shift " a:term : tactic => `(tactic| (
  rw [shiftV_eq (by simp) $a]
  generalize hX : shiftVbv _ _ (BitVec.setWidth 7 $a) = X
  simp only [shiftVbv] at hX
  vs_unfold
  pat_eval
  vs_sem
  subst_vars
  constructor <;> bv_decide -enums))

/-! ### Rotations: the rotate core on an opaque amount

Evaluated with the amount a free variable `J < 128` (a computed amount — `rotr`'s `select` —
makes `simp` distribute over the selects and run out of memory). -/

/-- The core of a left rotation: amount at `a`, temporaries from `t`. -/
def RotCore (a t : ValueId) : Prop :=
  ∀ (ρ : Regs) (xl xh J : BitVec 64), J.toNat < 128 → ρ 0 = some (V64 xl) →
    ρ 1 = some (V64 xh) → ρ a = some (V64 J) →
    ∃ ρ', runPat ρ (Pat.varShift .rotl a t) = some ρ' ∧
      ρ' 3 = some (V64 (rotLo xl xh J)) ∧ ρ' 4 = some (V64 (rotHi xl xh J))

macro "rot_core" : tactic => `(tactic| (
  intro ρ xl xh J hJ h0 h1 ha
  generalize hLo : rotLo xl xh J = Lo
  generalize hHi : rotHi xl xh J = Hi
  have hJ' : J < 128#64 := by rw [BitVec.lt_def]; simpa using hJ
  simp only [rotLo, rotHi] at hLo hHi
  simp (config := { maxSteps := 4000000 }) [Pat.varShift, Pat.cross, S, K, bin,
    runPat, evalInst, dframe, Frame.getAs, Frame.get, Regs.set, Res.ofOption,
    BinaryOp.isShift, Sem.shift, bind, Res.bind, width_i8, width_i64,
    Regs.setMany_cons, Regs.setMany_nil, h0, h1, ha]
  vs_sem
  subst hLo hHi
  constructor <;> bv_decide -enums))

theorem rotCore_6_7 : RotCore 6 7 := by rot_core
theorem rotCore_7_8 : RotCore 7 8 := by rot_core
theorem rotCore_11_12 : RotCore 11 12 := by rot_core
theorem rotCore_12_13 : RotCore 12 13 := by rot_core

/-- A left rotation by `J`: an amount prefix computing `J` at `a`, then the core. -/
theorem rot_glue {ρ0 : Regs} {pre : List Stmt} {a t : ValueId} (hc : RotCore a t)
    {xl xh J : BitVec 64} (hJ : J.toNat < 128)
    (hpre : ∃ ρ1, runPat ρ0 pre = some ρ1 ∧ ρ1 0 = some (V64 xl) ∧ ρ1 1 = some (V64 xh) ∧
      ρ1 a = some (V64 J)) :
    ∃ ρ, runPat ρ0 (pre ++ Pat.varShift .rotl a t) = some ρ ∧
      Out128 ρ 3 4 ((xh ++ xl).rotateLeft J.toNat) := by
  obtain ⟨ρ1, hp, h0, h1, ha⟩ := hpre
  obtain ⟨ρ, hr, h3, h4⟩ := hc ρ1 xl xh J hJ h0 h1 ha
  refine ⟨ρ, by rw [runPat_append, hp, Option.bind_some, hr], ?_⟩
  rw [Out128, rotl_lo_bv _ _ _ hJ, rotl_hi_bv _ _ _ hJ]
  exact ⟨h3, h4⟩

/-- The source rotations as left rotations by the prefix's amount. -/
theorem shiftV_rotl {v : Nat} (hv : v ≤ 64) (a : BitVec v) (X : BitVec 128) :
    shiftV .rotl X (a.toNat % 128) = X.rotateLeft (amtK a).toNat := by
  rw [amtK_toNat hv]; rfl

theorem shiftV_rotr {v : Nat} (hv : v ≤ 64) (a : BitVec v) (X : BitVec 128) :
    shiftV .rotr X (a.toNat % 128) = X.rotateLeft (rotrAmt (amtK a)).toNat := by
  have hK : (amtK a).toNat < 128 := by rw [amtK_toNat hv]; omega
  rw [rotrAmt_toNat hK, amtK_toNat hv]
  exact rotateRight_eq X (Nat.mod_lt _ (by omega))

theorem amtK_lt {v : Nat} (hv : v ≤ 64) (a : BitVec v) : (amtK a).toNat < 128 := by
  rw [amtK_toNat hv]; omega

theorem rotrAmt_lt {v : Nat} (hv : v ≤ 64) (a : BitVec v) : (rotrAmt (amtK a)).toNat < 128 := by
  rw [rotrAmt_toNat (amtK_lt hv a)]; omega

/-- The amount prefix: run it, then the amount identity. -/
macro "vs_pre" : tactic => `(tactic| (
  simp only [Pat.amt, List.cons_append, List.nil_append]
  pat_eval
  simp only [amtK, rotrAmt, Sem.binary, Sem.band, Sem.isub, select_bif, Sem.icmp, Sem.intcc,
    bool8_eq, Sem.uextend]
  try bv_decide -enums))

end Opt.Legal

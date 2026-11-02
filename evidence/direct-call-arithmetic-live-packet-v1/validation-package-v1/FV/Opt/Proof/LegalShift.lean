import FV.Opt.Proof.LegalArith

/-!
# Variable-amount `i128` shifts and rotates (`Opt.Legal.Pat.varShiftFull`)

Split from `LegalArith.lean`; the per-width pattern theorems are in `LegalShift8/16/32/64`.

A run is split at the amount: the prefix computes the 64-bit amount `J < 128` (`amtK`, for
`rotr` `rotrAmt`; `vs_pre`), the shift core is evaluated with `J` a free variable (`shift_core`,
`RotCore`; a computed amount — `rotr`'s `select` — makes `simp` distribute over the selects and
run out of memory), and the two are glued (`shift_glue`, `rot_glue`). The identities of a core
(`vs_fin`) are kernel-checked: the selects are split, the 64-bit amounts become `Nat`s in
`J.toNat`, the source halves are the 64-bit shift formulas of `shl_lo`, …, `sshr_hi` (shifts;
bit by bit, `LegalArith.lean`) or `rotLo`/`rotHi` (rotations; the halves of the rotation by
`rotl_lo`, `rotl_hi`), and the amounts agree by `omega`. A right rotation by `n` is the left
rotation by `(128 - n) % 128` (`rotateRight_eq`), the amount `rotr`'s prefix computes
(`rotrAmt`).
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

/-! ## Rotations -/

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

/-- The 64-bit operations of a run, unfolded to bit-vector operations. -/
macro "vs_sem" : tactic => `(tactic|
  simp only [ishl64, ushr64, sshr64, Sem.binary, Sem.bor, Sem.band, Sem.isub, select_bif,
    Sem.icmp, Sem.intcc, bool8_eq, Sem.uextend])

/-- The residual identities of a core run: the selects split, the 64-bit amounts as `Nat`s
(`J.toNat` arithmetic), the source halves by `shl_lo`, …, then the amounts by `omega`. -/
macro "vs_fin" : tactic => `(tactic| (
  (try simp only [b8_ne0, Bool.cond_eq_ite])
  (repeat' split) <;>
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
    BitVec.toNat_umod, BitVec.toNat_sub, BitVec.toNat_ofNat, Opt.Proof.KernelBV.reduceToNatAndMask,
    BitVec.ule_eq_decide, BitVec.lt_def, beq_iff_eq, bne_iff_ne, ne_eq, BitVec.toNat_eq,
    decide_eq_true_eq, Bool.not_eq_true, Nat.reducePow, Nat.reduceMod] at * <;>
  simp (disch := omega) only [shl_lo, shl_hi, ushr_lo, ushr_hi, sshr_lo, sshr_hi, ite_eq_left,
    ite_eq_right, Nat.mod_eq_of_lt, BitVec.shiftLeft_zero, BitVec.ushiftRight_zero,
    BitVec.sshiftRight_zero, BitVec.ushiftRight_eq_zero, BitVec.shiftLeft_eq_zero, BitVec.or_zero,
    BitVec.zero_or] <;>
  eq_leaf))

/-- Evaluate the core of a variable shift (amount register `ha`). -/
macro "vs_core_eval " h0:ident h1:ident ha:ident : tactic => `(tactic|
  simp (config := { maxSteps := 4000000 }) [Pat.varShift, Pat.cross, S, K, bin,
    runPat, evalInst, dframe, Frame.getAs, Frame.get, Regs.set, Res.ofOption,
    BinaryOp.isShift, Sem.shift, bind, Res.bind, width_i8, width_i64,
    Regs.setMany_cons, Regs.setMany_nil, Out128, shiftV, $h0:ident, $h1:ident, $ha:ident])

/-- The core of a variable shift (`ishl`/`ushr`/`sshr`) on an opaque amount `J < 128` at `a`. -/
private theorem shift_core (op : BinaryOp) (hop : op = .ishl ∨ op = .ushr ∨ op = .sshr)
    (a t : ValueId) (hat : (a = 6 ∧ t = 7) ∨ (a = 7 ∧ t = 8)) :
    ∀ (ρ : Regs) (xl xh J : BitVec 64), J.toNat < 128 → ρ 0 = some (V64 xl) →
      ρ 1 = some (V64 xh) → ρ a = some (V64 J) →
      ∃ ρ', runPat ρ (Pat.varShift op a t) = some ρ' ∧
        Out128 ρ' 3 4 (shiftV op (xh ++ xl) J.toNat) := by
  intro ρ xl xh J hJ h0 h1 ha
  rcases hat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hop with rfl | rfl | rfl <;>
    (vs_core_eval h0 h1 ha
     vs_sem
     constructor <;> vs_fin)

/-- A variable shift by `J`: an amount prefix computing `J` at `a`, then the core. -/
private theorem shift_glue {ρ0 : Regs} {pre : List Stmt} {op : BinaryOp} {a t : ValueId}
    (hc : ∀ (ρ : Regs) (xl xh J : BitVec 64), J.toNat < 128 → ρ 0 = some (V64 xl) →
      ρ 1 = some (V64 xh) → ρ a = some (V64 J) →
      ∃ ρ', runPat ρ (Pat.varShift op a t) = some ρ' ∧
        Out128 ρ' 3 4 (shiftV op (xh ++ xl) J.toNat))
    {xl xh J : BitVec 64} (hJ : J.toNat < 128)
    (hpre : ∃ ρ1, runPat ρ0 pre = some ρ1 ∧ ρ1 0 = some (V64 xl) ∧ ρ1 1 = some (V64 xh) ∧
      ρ1 a = some (V64 J)) :
    ∃ ρ, runPat ρ0 (pre ++ Pat.varShift op a t) = some ρ ∧
      Out128 ρ 3 4 (shiftV op (xh ++ xl) J.toNat) := by
  obtain ⟨ρ1, hp, h0, h1, ha⟩ := hpre
  obtain ⟨ρ, hr, hout⟩ := hc ρ1 xl xh J hJ h0 h1 ha
  exact ⟨ρ, by rw [runPat_append, hp, Option.bind_some, hr], hout⟩

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
  simp only [rotLo, rotHi] at hLo hHi
  vs_core_eval h0 h1 ha
  vs_sem
  subst hLo hHi
  constructor <;> vs_fin))

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
    bool8_eq, Sem.uextend, BitVec.setWidth_eq, BitVec.zeroExtend_eq_setWidth]
  all_goals (try simp only [b8_ne0])
  all_goals (try simp only [Bool.cond_eq_ite, beq_iff_eq])
  all_goals congr))

/-- The variable-shift patterns (`ishl`/`ushr`/`sshr`) with a 64-bit amount `a`. -/
theorem pat_varShiftW (op : BinaryOp) (hop : op = .ishl ∨ op = .ushr ∨ op = .sshr)
    (xl xh a : BitVec 64) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, V64 a]) (Pat.varShiftFull op .wide) = some ρ ∧
      Out128 ρ 3 4 (shiftV op (xh ++ xl) (a.toNat % 128)) := by
  rw [← amtK_toNat (Nat.le_refl 64) a]
  rcases hop with rfl | rfl | rfl <;>
    exact shift_glue (pre := (Pat.amt .wide false 5).1) (shift_core _ (by simp) 6 7 (.inl ⟨rfl, rfl⟩))
      (amtK_lt (by omega) a) (by vs_pre)

example : ∃ ρ, runPat (canon [V64 1#64, V64 2#64, V64 3#64]) (Pat.varShiftFull .ishl .wide) =
    some ρ ∧ Out128 ρ 3 4 (shiftV .ishl (2#64 ++ 1#64) ((3#64).toNat % 128)) :=
  pat_varShiftW .ishl (.inl rfl) 1#64 2#64 3#64

/-- The variable-shift patterns (`ishl`/`ushr`/`sshr`) with an amount `a` narrower than 64 bits. -/
theorem pat_varShiftN (op : BinaryOp) (hop : op = .ishl ∨ op = .ushr ∨ op = .sshr) (t : Ty)
    (ht : t = .i8 ∨ t = .i16 ∨ t = .i32) (xl xh : BitVec 64) (a : BitVec t.width) :
    ∃ ρ, runPat (canon [V64 xl, V64 xh, ⟨t, a⟩]) (Pat.varShiftFull op .narrow) = some ρ ∧
      Out128 ρ 3 4 (shiftV op (xh ++ xl) (a.toNat % 128)) := by
  rcases ht with rfl | rfl | rfl <;> rw [← amtK_toNat (by simp) a] <;>
  rcases hop with rfl | rfl | rfl <;>
    exact shift_glue (pre := (Pat.amt .narrow false 5).1)
      (shift_core _ (by simp) 7 8 (.inr ⟨rfl, rfl⟩)) (amtK_lt (by simp) a) (by vs_pre)

example : ∃ ρ, runPat (canon [V64 1#64, V64 2#64, ⟨.i8, 3#8⟩]) (Pat.varShiftFull .ushr .narrow) =
    some ρ ∧ Out128 ρ 3 4 (shiftV .ushr (2#64 ++ 1#64) ((3#8).toNat % 128)) :=
  pat_varShiftN .ushr (.inr (.inl rfl)) .i8 (.inl rfl) 1#64 2#64 3#8

/-- A variable shift (`ishl`/`ushr`/`sshr`) by the amount `a` (`pat_varShiftW`; a narrow amount
by `pat_varShiftN`, its type read off the goal). -/
macro "vs_shift " a:term : tactic => `(tactic|
  first
  | exact pat_varShiftW _ (by simp) _ _ $a
  | (refine pat_varShiftN _ ?_ _ ?_ _ _ _ <;> simp))

end Opt.Legal

import FV.Isle.Opt.Helpers
import FV.Clif.Sem

namespace Opt.Proof.DivConst

open Isle.Opt

/-! ## The multiply-and-shift criterion -/

theorem two_pow_pos' (p : Nat) : 0 < 2 ^ p := Nat.two_pow_pos p

/-- The key bound of the criterion: `x * e < (d - x % d) * 2^p` for every `x` up to `nc + d - 1`
when `nc ≡ -1 (mod d)` and `nc * e < 2^p`. -/
theorem key_bound {d e p nc x : Nat} (hd : 2 ≤ d) (he : nc * e < 2 ^ p)
    (hnc : (nc + 1) % d = 0) (hx : x + 1 ≤ nc + d) : x * e < (d - x % d) * 2 ^ p := by
  have hd0 : 0 < d := by omega
  have hr := Nat.mod_lt x hd0
  by_cases hxn : x ≤ nc
  · calc x * e ≤ nc * e := Nat.mul_le_mul_right _ hxn
      _ < 2 ^ p := he
      _ ≤ (d - x % d) * 2 ^ p := Nat.le_mul_of_pos_left _ (by omega)
  · have hk := Nat.div_add_mod (nc + 1) d
    rw [hnc, Nat.add_zero] at hk
    have hk1 : 1 ≤ (nc + 1) / d := by
      rcases Nat.eq_zero_or_pos ((nc + 1) / d) with h | h
      · rw [h, Nat.mul_zero] at hk; omega
      · exact h
    have hdk : d ≤ d * ((nc + 1) / d) := Nat.le_mul_of_pos_right _ hk1
    have hxq : x / d = (nc + 1) / d ∧ x % d = x - (nc + 1) :=
      (Nat.div_mod_unique hd0).2 ⟨by omega, by omega⟩
    rw [hxq.2]
    have hj2 : 2 ≤ d - (x - (nc + 1)) := by omega
    have h1 : x ≤ nc * (d - (x - (nc + 1))) := by
      have := Nat.mul_le_mul_left nc hj2
      omega
    have hx0 : 0 < x := by omega
    have h2 : x * e * nc < x * 2 ^ p := by
      rw [Nat.mul_assoc, Nat.mul_comm e nc]
      exact Nat.mul_lt_mul_of_pos_left he hx0
    have h3 : x * 2 ^ p ≤ nc * (d - (x - (nc + 1))) * 2 ^ p := Nat.mul_le_mul_right _ h1
    apply Nat.lt_of_mul_lt_mul_right (a := nc)
    calc x * e * nc < x * 2 ^ p := h2
      _ ≤ nc * (d - (x - (nc + 1))) * 2 ^ p := h3
      _ = (d - (x - (nc + 1))) * 2 ^ p * nc := by ac_rfl

/-- `M * d = 2^p + e` and the key bound give `x * M / 2^p = x / d`. -/
theorem div_of_key {d M p e x : Nat} (hd : 0 < d) (hM : M * d = 2 ^ p + e)
    (key : x * e < (d - x % d) * 2 ^ p) : x * M / 2 ^ p = x / d := by
  have hdm := Nat.div_add_mod x d
  have hr := Nat.mod_lt x hd
  have hxM : x * M * d = x * 2 ^ p + x * e := by rw [Nat.mul_assoc, hM, Nat.mul_add]
  apply Nat.div_eq_of_lt_le
  · apply Nat.le_of_mul_le_mul_right (c := d) _ hd
    calc x / d * 2 ^ p * d = (d * (x / d)) * 2 ^ p := by ac_rfl
      _ ≤ x * 2 ^ p := Nat.mul_le_mul_right _ (Nat.mul_div_le x d)
      _ ≤ x * 2 ^ p + x * e := Nat.le_add_right _ _
      _ = x * M * d := hxM.symm
  · apply Nat.lt_of_mul_lt_mul_right (a := d)
    have : x + (d - x % d) = (x / d + 1) * d := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (x / d) d]; omega
    calc x * M * d = x * 2 ^ p + x * e := hxM
      _ < x * 2 ^ p + (d - x % d) * 2 ^ p := Nat.add_lt_add_left key _
      _ = (x + (d - x % d)) * 2 ^ p := by rw [Nat.add_mul]
      _ = (x / d + 1) * 2 ^ p * d := by rw [this]; ac_rfl

/-- The criterion (Granlund–Montgomery; Hacker's Delight 10-9): if `M * d = 2^p + e`,
`nc ≡ -1 (mod d)` and `nc * e < 2^p`, then `x * M / 2^p = x / d` for all `x ≤ nc + d - 1`. -/
theorem floor_mul_eq_div {d M p e nc x : Nat} (hd : 2 ≤ d) (hM : M * d = 2 ^ p + e)
    (he : nc * e < 2 ^ p) (hnc : (nc + 1) % d = 0) (hx : x + 1 ≤ nc + d) :
    x * M / 2 ^ p = x / d :=
  div_of_key (by omega) hM (key_bound hd he hnc hx)

/-- The ceiling form used by the signed sequence on negative dividends:
`x / d < x * M / 2^p ≤ x / d + 1` (as `x / d * 2^p < x * M ≤ (x / d + 1) * 2^p`). -/
theorem ceil_of_key {d M p e x : Nat} (hd : 0 < d) (hM : M * d = 2 ^ p + e) (he0 : 0 < e)
    (hx0 : 0 < x) (key : x * e ≤ (d - x % d) * 2 ^ p) :
    x / d * 2 ^ p < x * M ∧ x * M ≤ (x / d + 1) * 2 ^ p := by
  have hdm := Nat.div_add_mod x d
  have hr := Nat.mod_lt x hd
  have hxM : x * M * d = x * 2 ^ p + x * e := by rw [Nat.mul_assoc, hM, Nat.mul_add]
  have hxe : 0 < x * e := Nat.mul_pos hx0 he0
  constructor
  · apply Nat.lt_of_mul_lt_mul_right (a := d)
    calc x / d * 2 ^ p * d = (d * (x / d)) * 2 ^ p := by ac_rfl
      _ ≤ x * 2 ^ p := Nat.mul_le_mul_right _ (Nat.mul_div_le x d)
      _ < x * 2 ^ p + x * e := by omega
      _ = x * M * d := hxM.symm
  · apply Nat.le_of_mul_le_mul_right (c := d) _ hd
    have : x + (d - x % d) = (x / d + 1) * d := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (x / d) d]; omega
    calc x * M * d = x * 2 ^ p + x * e := hxM
      _ ≤ x * 2 ^ p + (d - x % d) * 2 ^ p := Nat.add_le_add_left key _
      _ = (x + (d - x % d)) * 2 ^ p := by rw [Nat.add_mul]
      _ = (x / d + 1) * 2 ^ p * d := by rw [this]; ac_rfl

/-! ## Doubling steps of the long division -/

/-- One doubling step of `P / n`, `P % n`. -/
theorem divmod_double {P n : Nat} (hn : 0 < n) :
    (n ≤ 2 * (P % n) → (2 * P) / n = 2 * (P / n) + 1 ∧ (2 * P) % n = 2 * (P % n) - n) ∧
    (2 * (P % n) < n → (2 * P) / n = 2 * (P / n) ∧ (2 * P) % n = 2 * (P % n)) := by
  have hdm := Nat.div_add_mod P n
  have hr := Nat.mod_lt P hn
  refine ⟨fun h => (Nat.div_mod_unique hn).2 ⟨?_, by omega⟩,
    fun h => (Nat.div_mod_unique hn).2 ⟨?_, h⟩⟩
  · rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]; omega
  · rw [Nat.mul_left_comm]; omega

/-- One doubling step of `(P - 1) / n`, `(P - 1) % n` (`2P - 1 = 2 (P - 1) + 1`). -/
theorem divmod_double1 {P n : Nat} (hn : 0 < n) (hP : 0 < P) :
    (n ≤ 2 * ((P - 1) % n) + 1 →
      (2 * P - 1) / n = 2 * ((P - 1) / n) + 1 ∧ (2 * P - 1) % n = 2 * ((P - 1) % n) + 1 - n) ∧
    (2 * ((P - 1) % n) + 1 < n →
      (2 * P - 1) / n = 2 * ((P - 1) / n) ∧ (2 * P - 1) % n = 2 * ((P - 1) % n) + 1) := by
  have hdm := Nat.div_add_mod (P - 1) n
  have hr := Nat.mod_lt (P - 1) hn
  refine ⟨fun h => (Nat.div_mod_unique hn).2 ⟨?_, by omega⟩,
    fun h => (Nat.div_mod_unique hn).2 ⟨?_, h⟩⟩
  · rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]; omega
  · rw [Nat.mul_left_comm]; omega

/-- `(k * (Q % N) + c) % N = (k * Q + c) % N`. -/
theorem mod_lin (N Q k c : Nat) : (k * (Q % N) + c) % N = (k * Q + c) % N := by
  conv => rhs; rw [← Nat.mod_add_div Q N]
  rw [Nat.mul_add, Nat.add_right_comm, Nat.mul_left_comm, Nat.add_mul_mod_self_left]

/-- The `wrap` of the Rust transcription on a natural number. -/
theorem wrap_nat (w n : Nat) : (((n : Int) % (2 : Int) ^ w).toNat) = n % 2 ^ w := by
  have : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by push_cast; rfl
  rw [this, ← Int.natCast_emod, Int.toNat_natCast]

theorem wrap_eq {w : Nat} {x : Int} (n : Nat) (h : x = n) :
    ((x % (2 : Int) ^ w).toNat) = n % 2 ^ w := by
  rw [h, wrap_nat]

theorem mod_add_one (N Q : Nat) : (Q % N + 1) % N = (Q + 1) % N := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-! ## `magicU` -/

/-- The exit test of the unsigned loop gives the criterion's bound `nc * delta < P`. -/
theorem exitU {N nc delta P Q1 R1 : Nat} (hnc0 : 0 < nc) (hncN : nc < N) (hdel : delta < N)
    (hP : P = nc * Q1 + R1)
    (h : ¬(Q1 % N < delta ∨ (Q1 % N = delta ∧ R1 = 0)) ∨ P = N * N) : nc * delta < P := by
  rcases h with h | h
  · by_cases hQ : Q1 < N
    · rw [Nat.mod_eq_of_lt hQ] at h
      by_cases hq : delta < Q1
      · have := Nat.mul_le_mul_left nc (show delta + 1 ≤ Q1 by omega)
        rw [Nat.mul_succ] at this; omega
      · have hq' : Q1 = delta := by omega
        subst hq'; omega
    · have h1 := Nat.mul_le_mul_left nc (show N ≤ Q1 by omega)
      have h2 := Nat.mul_lt_mul_of_pos_left hdel hnc0
      omega
  · subst h
    exact Nat.mul_lt_mul'' hncN hdel

/-- The continue test of the unsigned loop keeps `P ≤ N * d`. -/
theorem contU {N top nc d delta P Q1 R1 : Nat} (hN : N = 2 * top) (hnc0 : 0 < nc) (hncN : nc < N)
    (hncd : N ≤ nc + d) (hdel : delta ≤ d) (hP : P = nc * Q1 + R1) (hR1 : R1 < nc)
    (hPt : P ≤ N * top) (h : Q1 % N < delta ∨ (Q1 % N = delta ∧ R1 = 0)) : P ≤ N * d := by
  by_cases hQ : Q1 < N
  · rw [Nat.mod_eq_of_lt hQ] at h
    have hle : P ≤ nc * delta := by
      rcases h with h | ⟨h, h'⟩
      · have := Nat.mul_le_mul_left nc (show Q1 + 1 ≤ delta by omega)
        rw [Nat.mul_succ] at this; omega
      · subst h h'; omega
    have := Nat.mul_le_mul (Nat.le_of_lt hncN) hdel
    omega
  · have h1 := Nat.mul_le_mul_left nc (show N ≤ Q1 by omega)
    have h2 : N * nc ≤ N * top := by rw [Nat.mul_comm N nc]; omega
    have h3 := Nat.le_of_mul_le_mul_left h2 (by omega)
    have := Nat.mul_le_mul_left N (show top ≤ d by omega)
    omega

theorem two_pow_succ' (j : Nat) : 2 ^ (j + 1) = 2 * 2 ^ j := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- The loop of `magicU` (Hacker's Delight `magicu`): from a state at `p = j` (the quotients
`2^j / nc` and `(2^j - 1) / d` kept modulo `2^w`, the remainders exact, `add` the overflow flag of
the second quotient) it returns `(M mod 2^w, 2^w ≤ M, p - w)` with `M = (2^p - 1) / d + 1` at a `p`
satisfying the criterion `nc * (M d - 2^p) < 2^p`. -/
theorem loopU {w d nc : Nat} (hw : 1 ≤ w) (hd : 2 ≤ d) (hdw : d < 2 ^ w) (hnc0 : 0 < nc)
    (hncw : nc < 2 ^ w) (hncd : 2 ^ w ≤ nc + d) :
    ∀ (f j : Nat) (add : Bool) (q1 r1 q2 r2 : Nat),
      w - 1 ≤ j → j < 2 * w → 2 * w ≤ j + f →
      q1 = 2 ^ j / nc % 2 ^ w → r1 = 2 ^ j % nc → q2 = (2 ^ j - 1) / d % 2 ^ w →
      r2 = (2 ^ j - 1) % d → add = decide (2 ^ w ≤ (2 ^ j - 1) / d + 1) → 2 ^ j ≤ 2 ^ w * d →
      ∃ p, w ≤ p ∧ p ≤ 2 * w ∧
        Rust.magicU.loop w d (fun x => (x % (2 : Int) ^ w).toNat) nc (2 ^ (w - 1)) f (j : Int) add
            q1 r1 q2 r2 =
          (((2 ^ p - 1) / d + 1) % 2 ^ w, decide (2 ^ w ≤ (2 ^ p - 1) / d + 1), (p : Int) - w) ∧
        nc * (d - 1 - (2 ^ p - 1) % d) < 2 ^ p ∧ 2 ^ p ≤ 2 * 2 ^ w * d := by
  intro f
  induction f with
  | zero => intro j _ _ _ _ _ _ _ h1 _; omega
  | succ f ih =>
    intro j add q1 r1 q2 r2 hj1 hj2 hjf hq1 hr1 hq2 hr2 hadd hPd
    rw [Rust.magicU.loop.eq_2]
    have hP0 : 0 < 2 ^ j := two_pow_pos' j
    have hP2 := two_pow_succ' j
    have htop : 2 ^ w = 2 * 2 ^ (w - 1) := by
      rw [← two_pow_succ']; congr 1; omega
    have hd0 : 0 < d := by omega
    have hR1 : r1 < nc := hr1 ▸ Nat.mod_lt (2 ^ j) hnc0
    have hR2 : r2 < d := hr2 ▸ Nat.mod_lt (2 ^ j - 1) hd0
    have e1 : (((nc : Int) - r1) % 2 ^ w).toNat = nc - r1 := by
      rw [wrap_eq (nc - r1) (by omega), Nat.mod_eq_of_lt (by omega)]
    have e2 : (((r2 : Int) + 1) % 2 ^ w).toNat = r2 + 1 := by
      rw [wrap_eq (r2 + 1) (by omega), Nat.mod_eq_of_lt (by omega)]
    have e3 : (((d : Int) - r2) % 2 ^ w).toNat = d - r2 := by
      rw [wrap_eq (d - r2) (by omega), Nat.mod_eq_of_lt (by omega)]
    have hs1 : (if r1 ≥ (((nc : Int) - r1) % 2 ^ w).toNat then
          ((((2 * (q1 : Int) + 1) % 2 ^ w).toNat, ((2 * (r1 : Int) - nc) % 2 ^ w).toNat))
        else ((((2 * (q1 : Int)) % 2 ^ w).toNat, ((2 * (r1 : Int)) % 2 ^ w).toNat))) =
        (2 ^ (j + 1) / nc % 2 ^ w, 2 ^ (j + 1) % nc) := by
      rw [e1, hP2]
      obtain ⟨hA, hB⟩ := divmod_double (P := 2 ^ j) hnc0
      split
      · obtain ⟨h1, h2⟩ := hA (by omega)
        rw [h1, h2, wrap_eq (2 * q1 + 1) (by omega), wrap_eq (2 * r1 - nc) (by omega),
          Nat.mod_eq_of_lt (show 2 * r1 - nc < 2 ^ w by omega), hq1, mod_lin, ← hr1]
      · obtain ⟨h1, h2⟩ := hB (by omega)
        rw [h1, h2, wrap_eq (2 * q1) (by omega), wrap_eq (2 * r1) (by omega),
          Nat.mod_eq_of_lt (show 2 * r1 < 2 ^ w by omega), hq1, ← hr1]
        have := mod_lin (2 ^ w) (2 ^ j / nc) 2 0
        simpa using this
    have hs2 : (if (((r2 : Int) + 1) % 2 ^ w).toNat ≥ (((d : Int) - r2) % 2 ^ w).toNat then
          (add || decide (q2 ≥ 2 ^ (w - 1) - 1), ((2 * (q2 : Int) + 1) % 2 ^ w).toNat,
            ((2 * (r2 : Int) + 1 - d) % 2 ^ w).toNat)
        else (add || decide (q2 ≥ 2 ^ (w - 1)), ((2 * (q2 : Int)) % 2 ^ w).toNat,
            ((2 * (r2 : Int) + 1) % 2 ^ w).toNat)) =
        (decide (2 ^ w ≤ (2 ^ (j + 1) - 1) / d + 1), (2 ^ (j + 1) - 1) / d % 2 ^ w,
          (2 ^ (j + 1) - 1) % d) := by
      rw [e2, e3, hP2]
      obtain ⟨hA, hB⟩ := divmod_double1 (P := 2 ^ j) hd0 hP0
      have hQ2 := Nat.div_add_mod (2 ^ j - 1) d
      split
      · obtain ⟨h1, h2⟩ := hA (by omega)
        rw [h1, h2, wrap_eq (2 * q2 + 1) (by omega), wrap_eq (2 * r2 + 1 - d) (by omega),
          Nat.mod_eq_of_lt (show 2 * r2 + 1 - d < 2 ^ w by omega), hq2, mod_lin, ← hr2]
        congr 1
        rw [hadd, ← Bool.decide_or, decide_eq_decide]
        by_cases hc : 2 ^ w ≤ (2 ^ j - 1) / d + 1
        · omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · obtain ⟨h1, h2⟩ := hB (by omega)
        rw [h1, h2, wrap_eq (2 * q2) (by omega), wrap_eq (2 * r2 + 1) (by omega),
          Nat.mod_eq_of_lt (show 2 * r2 + 1 < 2 ^ w by omega), ← hr2]
        have := mod_lin (2 ^ w) ((2 ^ j - 1) / d) 2 0
        simp only [Nat.add_zero] at this
        rw [hq2, this]
        congr 1
        rw [hadd, ← Bool.decide_or, decide_eq_decide]
        by_cases hc : 2 ^ w ≤ (2 ^ j - 1) / d + 1
        · omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hs1, hs2]
    dsimp only
    have hR2' := Nat.mod_lt (2 ^ (j + 1) - 1) hd0
    have e4 : (((d : Int) - 1 - ((2 ^ (j + 1) - 1) % d : Nat)) % 2 ^ w).toNat =
        d - 1 - (2 ^ (j + 1) - 1) % d := by
      rw [wrap_eq (d - 1 - (2 ^ (j + 1) - 1) % d) (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e4]
    have hP1 := Nat.div_add_mod (2 ^ (j + 1)) nc
    have hR1' := Nat.mod_lt (2 ^ (j + 1)) hnc0
    split
    · rename_i h
      refine ⟨j + 1, by omega, by omega, ?_, ?_, ?_⟩
      · rw [wrap_eq (((2 ^ (j + 1) - 1) / d % 2 ^ w) + 1) (by omega), mod_add_one]
        congr 2
      · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
          Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
        apply exitU hnc0 hncw (show d - 1 - (2 ^ (j + 1) - 1) % d < 2 ^ w by omega) hP1.symm
        rcases h with h | ⟨h1, h2⟩
        · right
          have : j + 1 = 2 * w := by omega
          rw [this, Nat.two_mul, Nat.pow_add]
        · left
          intro h3
          rcases h3 with h3 | ⟨h3, h4⟩
          · omega
          · rcases h2 with h2 | h2 <;> omega
      · rw [hP2, Nat.mul_assoc]; omega
    · rename_i h
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_false, Bool.and_eq_true,
        decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, not_or, not_and] at h
      have hj' : j + 1 < 2 * w := by
        rcases h with ⟨h, _⟩; omega
      have hcont : 2 ^ (j + 1) ≤ 2 ^ w * d := by
        apply contU htop hnc0 hncw hncd (delta := d - 1 - (2 ^ (j + 1) - 1) % d) (by omega)
          hP1.symm hR1'
        · have : 2 ^ w * 2 ^ (w - 1) = 2 ^ (2 * w - 1) := by
            rw [← Nat.pow_add]; congr 1; omega
          rw [this]; exact Nat.pow_le_pow_right (by omega) (by omega)
        · omega
      have := ih (j + 1) _ _ _ _ _ (by omega) hj' (by omega) rfl rfl rfl rfl rfl hcont
      push_cast at this ⊢
      exact this

theorem two_pow_int (w : Nat) : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by push_cast; rfl

/-- `wrap (-d) = 2^w - d`. -/
theorem wrap_neg {w d : Nat} (hd0 : 0 < d) (hd : d ≤ 2 ^ w) :
    ((-(d : Int)) % (2 : Int) ^ w).toNat = 2 ^ w - d := by
  have h2 := two_pow_int w
  have : -(d : Int) = ((2 ^ w - d : Nat) : Int) + (2 : Int) ^ w * (-1) := by rw [h2]; omega
  rw [this, Int.add_mul_emod_self_left, wrap_nat]
  exact Nat.mod_eq_of_lt (by have := two_pow_pos' w; omega)

/-- A divisor that is not a power of two has no multiply-by-power-of-two magic: the criterion
`x * 2^a / 2^p = x / d` cannot hold for all `x < N`. -/
theorem not_pow_floor {N d a p e : Nat} (hd2 : 2 ≤ d) (hdN : d < N) (hpow : ∀ k, d ≠ 2 ^ k)
    (hM : 2 ^ a * d = 2 ^ p + e) (he : e < d)
    (hcorr : ∀ x < N, x * 2 ^ a / 2 ^ p = x / d) : False := by
  have hap : a ≤ p := by
    apply Nat.le_of_not_lt
    intro h
    have h1 : 2 ^ (p + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 := Nat.mul_le_mul_right d h1
    rw [two_pow_succ', Nat.mul_assoc] at h2
    have h3 := Nat.mul_le_mul_left (2 ^ p) hd2
    have := two_pow_pos' p
    have := Nat.le_mul_of_pos_left d this
    omega
  have hsplit : 2 ^ p = 2 ^ a * 2 ^ (p - a) := by rw [← Nat.pow_add]; congr 1; omega
  have hx : ∀ x < N, x / 2 ^ (p - a) = x / d := by
    intro x hxN
    have := hcorr x hxN
    rwa [hsplit, Nat.mul_comm x, Nat.mul_div_mul_left _ _ (two_pow_pos' a)] at this
  have hdd : d / 2 ^ (p - a) = 1 := by rw [hx d hdN, Nat.div_self (by omega)]
  have hk0 := two_pow_pos' (p - a)
  have hlo : 2 ^ (p - a) ≤ d := by
    apply Nat.le_of_not_lt; intro h; rw [Nat.div_eq_of_lt h] at hdd; omega
  have hlt : 2 ^ (p - a) < N := by omega
  have h1 := hx _ hlt
  rw [Nat.div_self hk0] at h1
  have hhi : d ≤ 2 ^ (p - a) := by
    apply Nat.le_of_not_lt; intro h; rw [Nat.div_eq_of_lt h] at h1; omega
  exact hpow (p - a) (by omega)

/-- `isPow2 d = false` as "not a power of two". -/
theorem not_pow_of_isPow2 {d : Nat} (h : Rust.isPow2 (d : Int) = false) : ∀ k, d ≠ 2 ^ k := by
  rintro k rfl
  simp only [Rust.isPow2, Int.toNat_natCast, Nat.log2_two_pow, beq_self_eq_true, Bool.and_true,
    decide_eq_false_iff_not] at h
  exact h (by exact_mod_cast two_pow_pos' k)

/-- **`magicU` is correct.** For a divisor `2 ≤ d < 2^w` that is not a power of two, `magicU w d`
returns `(m, add, s)` with `m < 2^w`, and the emitted sequence computes `x / d` for every
`x < 2^w`: `umulhi x m >> s` when `add` is false (`s < w`), and
`((x - umulhi x m) >> 1 + umulhi x m) >> (s - 1)` when it is true (`1 ≤ s ≤ w`). -/
theorem magicU_spec {w d : Nat} (hw : 1 ≤ w) (hd : 2 ≤ d) (hdw : d < 2 ^ w)
    (hpow : ∀ k, d ≠ 2 ^ k) :
    ∃ m s : Nat, m < 2 ^ w ∧
      ((Rust.magicU w d = (m, false, (s : Int)) ∧ s < w ∧
          ∀ x < 2 ^ w, x * m / 2 ^ w / 2 ^ s = x / d) ∨
       (Rust.magicU w d = (m, true, (s : Int)) ∧ 1 ≤ s ∧ s ≤ w ∧
          ∀ x < 2 ^ w, ((x - x * m / 2 ^ w) / 2 + x * m / 2 ^ w) / 2 ^ (s - 1) = x / d)) := by
  have hd0 : 0 < d := by omega
  have h2 := two_pow_int w
  have hN0 := two_pow_pos' w
  have htop : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← two_pow_succ']; congr 1; omega
  have hr := Nat.mod_lt (2 ^ w - d) hd0
  obtain ⟨nc, hnc⟩ : ∃ nc, nc = 2 ^ w - 1 - (2 ^ w - d) % d := ⟨_, rfl⟩
  have hnc0 : 0 < nc := by omega
  have hncw : nc < 2 ^ w := by omega
  have hncd : 2 ^ w ≤ nc + d := by omega
  have hncm : (nc + 1) % d = 0 := by
    have := Nat.div_add_mod (2 ^ w - d) d
    have e : nc + 1 = d * ((2 ^ w - d) / d + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [e, Nat.mul_mod_right]
  unfold Rust.magicU
  dsimp only
  have e1 : (((2 : Int) ^ w - 1 - (((2 ^ w - d) % d : Nat) : Int)) % 2 ^ w).toNat = nc := by
    rw [wrap_eq nc (by rw [h2]; omega), Nat.mod_eq_of_lt hncw]
  have e2 : ((((2 ^ (w - 1) : Nat) : Int) - ((2 ^ (w - 1) / nc : Nat) : Int) * (nc : Int)) %
      2 ^ w).toNat = 2 ^ (w - 1) % nc := by
    have := Nat.mod_add_div' (2 ^ (w - 1)) nc
    have hl := Nat.mod_lt (2 ^ (w - 1)) hnc0
    rw [wrap_eq (2 ^ (w - 1) % nc) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have e3 : ((((2 ^ (w - 1) : Nat) : Int) - 1 - (((2 ^ (w - 1) - 1) / d : Nat) : Int) * (d : Int)) %
      2 ^ w).toNat = (2 ^ (w - 1) - 1) % d := by
    have := Nat.mod_add_div' (2 ^ (w - 1) - 1) d
    have hl := Nat.mod_lt (2 ^ (w - 1) - 1) hd0
    have : 1 ≤ 2 ^ (w - 1) := two_pow_pos' _
    rw [wrap_eq ((2 ^ (w - 1) - 1) % d) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have e4 : ((w : Int) - 1) = ((w - 1 : Nat) : Int) := by omega
  rw [wrap_neg hd0 (Nat.le_of_lt hdw), e1, e2, e3, e4]
  have hq1 : 2 ^ (w - 1) / nc < 2 ^ w := by
    have := Nat.div_le_self (2 ^ (w - 1)) nc; omega
  have hq2 : (2 ^ (w - 1) - 1) / d < 2 ^ w := by
    have := Nat.div_le_self (2 ^ (w - 1) - 1) d; omega
  obtain ⟨p, hp1, hp2, hloop, hcrit, hpd⟩ := loopU hw hd hdw hnc0 hncw hncd (2 * w) (w - 1) false
    _ _ _ _ (by omega) (by omega) (by omega) (Nat.mod_eq_of_lt hq1).symm rfl
    (Nat.mod_eq_of_lt hq2).symm rfl
    (by
      have := Nat.div_le_self (2 ^ (w - 1) - 1) d
      exact (decide_eq_false (by omega)).symm)
    (by have := Nat.mul_le_mul_left (2 ^ w) (show 1 ≤ d by omega); omega)
  rw [hloop]
  -- the magic number `M = (2^p - 1) / d + 1`
  have hP0 := two_pow_pos' p
  have hQ := Nat.div_add_mod (2 ^ p - 1) d
  have hR := Nat.mod_lt (2 ^ p - 1) hd0
  have hMd : ((2 ^ p - 1) / d + 1) * d = 2 ^ p + (d - 1 - (2 ^ p - 1) % d) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  have hcorr : ∀ x < 2 ^ w, x * ((2 ^ p - 1) / d + 1) / 2 ^ p = x / d := fun x hx =>
    floor_mul_eq_div hd hMd hcrit hncm (by omega)
  have hMle : (2 ^ p - 1) / d + 1 ≤ 2 * 2 ^ w := by
    have : (2 ^ p - 1) / d < 2 * 2 ^ w := (Nat.div_lt_iff_lt_mul hd0).2 (by omega)
    omega
  have hMN : (2 ^ p - 1) / d + 1 ≠ 2 ^ w := by
    intro h
    exact not_pow_floor hd hdw hpow (h ▸ hMd) (by omega) (h ▸ hcorr)
  have hM2N : (2 ^ p - 1) / d + 1 ≠ 2 ^ (w + 1) := by
    intro h
    exact not_pow_floor (N := 2 ^ w) hd hdw hpow (h ▸ hMd) (by omega) (h ▸ hcorr)
  have h2N : 2 ^ (w + 1) = 2 * 2 ^ w := two_pow_succ' w
  by_cases hadd : 2 ^ w ≤ (2 ^ p - 1) / d + 1
  · -- `add`: `M = 2^w + m`
    have hM : (2 ^ p - 1) / d + 1 = 2 ^ w + ((2 ^ p - 1) / d + 1) % 2 ^ w := by
      rw [Nat.mod_eq_sub_mod hadd, Nat.mod_eq_of_lt (by omega)]; omega
    have hpw : w + 1 ≤ p := by
      apply Nat.le_of_not_lt; intro h
      have : 2 ^ p ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 := Nat.mul_le_mul_right d (show 2 ^ w + 1 ≤ (2 ^ p - 1) / d + 1 by omega)
      rw [Nat.add_mul, Nat.one_mul] at h3
      have h4 := Nat.mul_le_mul_left (2 ^ w) hd
      omega
    refine ⟨((2 ^ p - 1) / d + 1) % 2 ^ w, p - w, Nat.mod_lt _ hN0, .inr ⟨?_, by omega, by omega, ?_⟩⟩
    · simp only [decide_eq_true hadd]; congr 2; omega
    · intro x hx
      have hm := Nat.mod_lt ((2 ^ p - 1) / d + 1) hN0
      generalize ((2 ^ p - 1) / d + 1) % 2 ^ w = m at hM hm
      have hq0 : x * m / 2 ^ w ≤ x := by
        apply Nat.div_le_of_le_mul
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hm)
      have e5 : (x - x * m / 2 ^ w) / 2 + x * m / 2 ^ w = (x + x * m / 2 ^ w) / 2 := by omega
      have e6 : x + x * m / 2 ^ w = x * ((2 ^ p - 1) / d + 1) / 2 ^ w := by
        rw [hM, Nat.mul_add, Nat.mul_comm x (2 ^ w), Nat.add_comm (2 ^ w * x),
          Nat.add_mul_div_left _ _ hN0, Nat.add_comm]
      rw [e5, e6, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← two_pow_succ',
        ← Nat.pow_add, show w + (p - w - 1 + 1) = p by omega]
      exact hcorr x hx
  · -- no `add`: `M = m < 2^w`
    have hMl : (2 ^ p - 1) / d + 1 < 2 ^ w := by omega
    have hp2w : p < 2 * w := by
      apply Nat.lt_of_le_of_ne hp2; intro h
      have h3 := Nat.mul_lt_mul'' hMl hdw
      rw [hMd, h, Nat.two_mul, Nat.pow_add] at h3
      omega
    refine ⟨((2 ^ p - 1) / d + 1) % 2 ^ w, p - w, Nat.mod_lt _ hN0, .inl ⟨?_, by omega, ?_⟩⟩
    · simp only [decide_eq_false hadd]; congr 2; omega
    · intro x hx
      rw [Nat.mod_eq_of_lt hMl, Nat.div_div_eq_div_mul, ← Nat.pow_add,
        show w + (p - w) = p by omega]
      exact hcorr x hx

/-! ## `magicS` -/

/-- A divisor of a power of two is a power of two. -/
theorem dvd_two_pow {a : Nat} : ∀ p, a ∣ 2 ^ p → ∃ k, a = 2 ^ k
  | 0, h => ⟨0, Nat.dvd_one.mp h⟩
  | p + 1, h => by
    by_cases ha : a % 2 = 0
    · obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := ⟨a / 2, by omega⟩
      rw [two_pow_succ'] at h
      obtain ⟨k, rfl⟩ := dvd_two_pow p (Nat.dvd_of_mul_dvd_mul_left (by omega) h)
      exact ⟨k + 1, (two_pow_succ' k).symm⟩
    · obtain ⟨c, hc⟩ := h
      rw [two_pow_succ'] at hc
      have hc2 : c % 2 = 0 := by
        have h1 : (a * c) % 2 = 0 := by rw [← hc, Nat.mul_mod_right]
        rw [Nat.mul_mod, show a % 2 = 1 by omega, Nat.one_mul, Nat.mod_mod] at h1
        exact h1
      obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
      rw [Nat.mul_left_comm] at hc
      exact dvd_two_pow p ⟨c', by omega⟩

theorem two_pow_mod_ne {ad : Nat} (hpow : ∀ k, ad ≠ 2 ^ k) (k : Nat) : 2 ^ k % ad ≠ 0 :=
  fun h => let ⟨j, hj⟩ := dvd_two_pow k (Nat.dvd_of_mod_eq_zero h); hpow j hj

/-- One step of the signed loop's long divisions (no wrapping: the values stay small). -/
theorem stepS {w P n q r : Nat} (hn : 0 < n) (hq : q = P / n) (hr : r = P % n)
    (hqw : 2 * q + 1 < 2 ^ w) (hnw : 2 * n ≤ 2 ^ w) :
    (if 2 * r ≥ n then
        (((((2 * q : Nat) : Int) + 1) % (2 : Int) ^ w).toNat,
          ((((2 * r : Nat) : Int) - n) % (2 : Int) ^ w).toNat)
      else (2 * q, 2 * r)) = ((2 * P) / n, (2 * P) % n) := by
  obtain ⟨hA, hB⟩ := divmod_double (P := P) hn
  have hrl : r < n := hr ▸ Nat.mod_lt P hn
  split
  · obtain ⟨h1, h2⟩ := hA (by omega)
    rw [h1, h2, wrap_eq (2 * q + 1) (by omega), wrap_eq (2 * r - n) (by omega),
      Nat.mod_eq_of_lt hqw, Nat.mod_eq_of_lt (by omega), hq, hr]
  · obtain ⟨h1, h2⟩ := hB (by omega)
    rw [h1, h2, hq, hr]

theorem exitS {nc delta P Q1 R1 : Nat} (hnc0 : 0 < nc) (hP : P = nc * Q1 + R1)
    (h : ¬(Q1 < delta ∨ (Q1 = delta ∧ R1 = 0))) : nc * delta < P := by
  by_cases hq : delta < Q1
  · have := Nat.mul_le_mul_left nc (show delta + 1 ≤ Q1 by omega)
    rw [Nat.mul_succ] at this; omega
  · have hq' : Q1 = delta := by omega
    subst hq'; omega

theorem contS {nc delta P Q1 R1 : Nat} (hP : P = nc * Q1 + R1) (hR1 : R1 < nc)
    (h : Q1 < delta ∨ (Q1 = delta ∧ R1 = 0)) : P ≤ nc * delta := by
  rcases h with h | ⟨h, h'⟩
  · have := Nat.mul_le_mul_left nc (show Q1 + 1 ≤ delta by omega)
    rw [Nat.mul_succ] at this; omega
  · subst h h'; omega

/-- The loop of `magicS` (Hacker's Delight `magic`): from a state at `p = j` with
`2^j ≤ anc * (ad - 1)` (no quotient overflows) it returns `(2^p / ad, p)` at a `p > j` with
`anc * (ad - 2^p mod ad) < 2^p`, before its fuel runs out. -/
theorem loopS {w ad anc : Nat} (hw : 2 ≤ w) (had : 2 ≤ ad) (hadw : ad < 2 ^ (w - 1))
    (hanc0 : 0 < anc) (hancw : anc ≤ 2 ^ (w - 1)) (hpow : ∀ k, 2 ^ k % ad ≠ 0) :
    ∀ (f j q1 r1 q2 r2 : Nat), 2 * w - 2 ≤ j + f →
      q1 = 2 ^ j / anc → r1 = 2 ^ j % anc → q2 = 2 ^ j / ad → r2 = 2 ^ j % ad →
      2 ^ j ≤ anc * (ad - 1) →
      ∃ p, j < p ∧
        Rust.magicS.loop (fun x => (x % (2 : Int) ^ w).toNat) ad anc f (j : Int) q1 r1 q2 r2 =
          (2 ^ p / ad, (p : Int)) ∧
        anc * (ad - 2 ^ p % ad) < 2 ^ p ∧ 2 ^ p ≤ 2 * (anc * (ad - 1)) := by
  have htop : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← two_pow_succ']; congr 1; omega
  have hbig : anc * (ad - 1) < 2 ^ (2 * w - 2) := by
    have : 2 ^ (2 * w - 2) = 2 ^ (w - 1) * 2 ^ (w - 1) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]
    exact Nat.mul_lt_mul_of_le_of_lt hancw (by omega) (two_pow_pos' _)
  intro f
  induction f with
  | zero =>
    intro j _ _ _ _ hf _ _ _ _ hj
    have : 2 ^ (2 * w - 2) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  | succ f ih =>
    intro j q1 r1 q2 r2 hjf hq1 hr1 hq2 hr2 hPa
    rw [Rust.magicS.loop.eq_2]
    have hP2 := two_pow_succ' j
    have hQ1 : q1 ≤ ad - 1 := hq1 ▸ Nat.div_le_of_le_mul hPa
    have hQ2 : q2 < anc := by
      rw [hq2]; apply (Nat.div_lt_iff_lt_mul (by omega)).2
      have := Nat.mul_sub_one anc ad
      have := Nat.le_mul_of_pos_left anc (show 0 < ad by omega)
      rw [Nat.mul_comm ad anc] at this
      omega
    have hR1 : r1 < anc := hr1 ▸ Nat.mod_lt _ hanc0
    have hR2 : r2 < ad := hr2 ▸ Nat.mod_lt _ (by omega)
    have ew1 : ((2 * (q1 : Int)) % 2 ^ w).toNat = 2 * q1 := by
      rw [wrap_eq (2 * q1) (by omega), Nat.mod_eq_of_lt (by omega)]
    have ew2 : ((2 * (r1 : Int)) % 2 ^ w).toNat = 2 * r1 := by
      rw [wrap_eq (2 * r1) (by omega), Nat.mod_eq_of_lt (by omega)]
    have ew3 : ((2 * (q2 : Int)) % 2 ^ w).toNat = 2 * q2 := by
      rw [wrap_eq (2 * q2) (by omega), Nat.mod_eq_of_lt (by omega)]
    have ew4 : ((2 * (r2 : Int)) % 2 ^ w).toNat = 2 * r2 := by
      rw [wrap_eq (2 * r2) (by omega), Nat.mod_eq_of_lt (by omega)]
    have hs1 := stepS (w := w) hanc0 hq1 hr1 (by omega) (by omega)
    have hs2 := stepS (w := w) (show 0 < ad by omega) hq2 hr2 (by omega) (by omega)
    rw [← hP2] at hs1 hs2
    rw [ew1, ew2, ew3, ew4, hs1]
    dsimp only
    rw [hs2]
    dsimp only
    have hR2' := Nat.mod_lt (2 ^ (j + 1)) (show 0 < ad by omega)
    have hR2n := hpow (j + 1)
    have ed : (((ad : Int) - ((2 ^ (j + 1) % ad : Nat) : Int)) % 2 ^ w).toNat =
        ad - 2 ^ (j + 1) % ad := by
      rw [wrap_eq (ad - 2 ^ (j + 1) % ad) (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [ed]
    have hP1 := Nat.div_add_mod (2 ^ (j + 1)) anc
    have hR1' := Nat.mod_lt (2 ^ (j + 1)) hanc0
    split
    · rename_i h
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
        Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      refine ⟨j + 1, by omega, by push_cast; rfl, ?_, by omega⟩
      apply exitS hanc0 hP1.symm
      intro h3
      rcases h3 with h3 | ⟨h3, h4⟩
      · exact h.1 h3
      · rcases h.2 with h2 | h2 <;> omega
    · rename_i h
      simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true, beq_iff_eq] at h
      have h1 := contS hP1.symm hR1' h
      have h2 := Nat.mul_le_mul_left anc (show ad - 2 ^ (j + 1) % ad ≤ ad - 1 by omega)
      obtain ⟨p, hp, hl, hc, hb⟩ := ih (j + 1) _ _ _ _ (by omega) rfl rfl rfl rfl (by omega)
      refine ⟨p, by omega, ?_, hc, hb⟩
      push_cast at hl
      exact hl

/-- The core of the signed sequence: for `M * ad = 2^p + e` with the criterion's bounds (strict
on `y ≥ 0`, non-strict on `y < 0`), `q = y * M / 2^p` (floor) corrected by `+1` when negative
is the truncated quotient `y / ad`. -/
theorem signed_core {ad M p e : Nat} (y : Int) (had : 0 < ad) (hM : M * ad = 2 ^ p + e)
    (he0 : 0 < e)
    (hpos : ∀ n : Nat, y = n → n * e < (ad - n % ad) * 2 ^ p)
    (hneg : ∀ z : Nat, y = -(z : Int) → 0 < z → z * e ≤ (ad - z % ad) * 2 ^ p) :
    y * M / 2 ^ p + (if y * M / 2 ^ p < 0 then 1 else 0) = y.tdiv ad := by
  have h2 := two_pow_int p
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · have h := div_of_key had hM (hpos n rfl)
    have e1 : (n : Int) * M / 2 ^ p = ((n * M / 2 ^ p : Nat) : Int) := by
      rw [h2, Int.natCast_ediv, Int.natCast_mul]
    rw [e1, h, Int.tdiv_eq_ediv_of_nonneg (a := (n : Int)) (by omega), ← Int.natCast_ediv]
    have : ¬ (((n / ad : Nat) : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp only [this, ite_false, Int.add_zero]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨h1, h2'⟩ := ceil_of_key had hM he0 hn (hneg n rfl hn)
      rw [Nat.add_mul, Nat.one_mul] at h2'
      rw [Int.neg_tdiv, ← Int.ofNat_tdiv]
      generalize n / ad = B at h1 h2' ⊢
      have hP0 := two_pow_pos' p
      have hb : (0 : Int) < 2 ^ p := by rw [h2]; exact_mod_cast hP0
      have h1i : (B : Int) * 2 ^ p < (n : Int) * M := by rw [h2]; exact_mod_cast h1
      have h2i : (n : Int) * M ≤ (B : Int) * 2 ^ p + 2 ^ p := by rw [h2]; exact_mod_cast h2'
      have hq : -(n : Int) * M / 2 ^ p = -(B : Int) - 1 := by
        refine ((Int.ediv_emod_unique (r := (B : Int) * 2 ^ p + 2 ^ p - n * M) hb).2
          ⟨?_, by omega, by omega⟩).1
        rw [Int.mul_sub, Int.mul_neg, Int.mul_one, Int.mul_comm ((2 : Int) ^ p) B, Int.neg_mul]
        omega
      rw [hq]
      have : -(B : Int) - 1 < 0 := by omega
      simp only [this, ite_true]
      omega

/-- The value of `magicS w d`: `(toInt (M or 2^w - M), p - w)` with `M = 2^p / |d| + 1`, at a `p`
satisfying the criterion for `anc ≡ -1 (mod |d|)` (`anc` covers the dividends `≤ 2^(w-1)` when
`d < 0`, `< 2^(w-1)` when `d > 0`, and `2^(w-1)` too unless `2^(w-1) ≡ -1 (mod d)`). -/
theorem magicS_eq {w : Nat} {d : Int} (hw : 3 ≤ w) (hd0 : d ≠ 0) (hdlo : -2 ^ (w - 1) ≤ d)
    (hdhi : d < 2 ^ (w - 1)) (hpow : ∀ k, d.natAbs ≠ 2 ^ k) :
    ∃ p anc : Nat, w ≤ p ∧ p + 2 ≤ 2 * w ∧
      Rust.magicS w d = ((BitVec.ofNat w (if d < 0 then 2 ^ w - (2 ^ p / d.natAbs + 1)
        else 2 ^ p / d.natAbs + 1)).toInt, ((p - w : Nat) : Int)) ∧
      anc * (d.natAbs - 2 ^ p % d.natAbs) < 2 ^ p ∧ (anc + 1) % d.natAbs = 0 ∧
      anc ≤ 2 ^ (w - 1) ∧ 2 ^ p ≤ 2 * (anc * (d.natAbs - 1)) ∧
      (d < 0 → 2 ^ (w - 1) + 1 ≤ anc + d.natAbs) ∧
      (0 < d → 2 ^ (w - 1) ≤ anc + d.natAbs ∧
        (2 ^ (w - 1) + 1 ≤ anc + d.natAbs ∨ (2 ^ (w - 1) + 1) % d.natAbs = 0)) ∧
      2 ^ p / d.natAbs + 1 < 2 ^ w := by
  obtain ⟨ad, had⟩ : ∃ ad, ad = d.natAbs := ⟨_, rfl⟩
  have hadI : (ad : Int) = if d < 0 then -d else d := by
    rw [had]; split
    · exact Int.ofNat_natAbs_of_nonpos (by omega)
    · exact Int.natAbs_of_nonneg (by omega)
  rw [← had] at hpow ⊢
  have h2 := two_pow_int w
  have h2' := two_pow_int (w - 1)
  have htop : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← two_pow_succ']; congr 1; omega
  have htop2 : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by rw [← two_pow_succ']; congr 1; omega
  have hadw : ad < 2 ^ (w - 1) := by
    have := hpow (w - 1)
    have : (ad : Int) ≤ 2 ^ (w - 1) := by split at hadI <;> omega
    omega
  have had3 : 3 ≤ ad := by
    have := hpow 0; have := hpow 1
    have : ad ≠ 0 := by intro h; rw [h] at hadI; split at hadI <;> omega
    simp at *; omega
  obtain ⟨t, ht, htn, htp⟩ : ∃ t, 2 ^ (w - 1) + (d % 2 ^ w).toNat / 2 ^ (w - 1) = t ∧
      (d < 0 → t = 2 ^ (w - 1) + 1) ∧ (0 < d → t = 2 ^ (w - 1)) := by
    refine ⟨_, rfl, fun hn => ?_, fun hp => ?_⟩
    · have e : d % 2 ^ w = d + 2 ^ w := by
        rw [← Int.add_mul_emod_self_left d (2 ^ w) 1, Int.mul_one]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [e, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    · rw [Int.emod_eq_of_lt (by omega) (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have ht1 : 2 ^ (w - 1) ≤ t ∧ t ≤ 2 ^ (w - 1) + 1 := by
    by_cases h : d < 0
    · have := htn h; omega
    · have := htp (by omega); omega
  have htd := Nat.div_add_mod t ad
  have htr := Nat.mod_lt t (show 0 < ad by omega)
  have htq : 1 ≤ t / ad := Nat.div_pos (by omega) (by omega)
  have hadq := Nat.le_mul_of_pos_right ad htq
  obtain ⟨anc, hanc⟩ : ∃ anc, anc = t - 1 - t % ad := ⟨_, rfl⟩
  have hanc1 : ad - 1 ≤ anc := by omega
  have hanc2 : t - ad ≤ anc := by omega
  have hanc0 : 0 < anc := by omega
  have hancw : anc ≤ 2 ^ (w - 1) := by omega
  have hancm : (anc + 1) % ad = 0 := by
    rw [show anc + 1 = ad * (t / ad) by omega, Nat.mul_mod_right]
  have hinit : 2 ^ (w - 1) ≤ anc * (ad - 1) := by
    have := Nat.mul_le_mul_left anc (show 2 ≤ ad - 1 by omega)
    omega
  unfold Rust.magicS
  dsimp only
  rw [← had]
  have e1 : ((ad : Int) % 2 ^ w).toNat = ad := by
    rw [wrap_nat, Nat.mod_eq_of_lt (by omega)]
  have e2 : ((((2 ^ (w - 1) + (d % 2 ^ w).toNat / 2 ^ (w - 1) : Nat) : Int) - 1 -
      (((2 ^ (w - 1) + (d % 2 ^ w).toNat / 2 ^ (w - 1)) % ad : Nat) : Int)) % 2 ^ w).toNat = anc := by
    rw [ht, wrap_eq anc (by omega), Nat.mod_eq_of_lt (by omega)]
  have e3 : ((((2 ^ (w - 1) : Nat) : Int) - ((2 ^ (w - 1) / anc : Nat) : Int) * (anc : Int)) %
      2 ^ w).toNat = 2 ^ (w - 1) % anc := by
    have := Nat.mod_add_div' (2 ^ (w - 1)) anc
    have hl := Nat.mod_lt (2 ^ (w - 1)) hanc0
    rw [wrap_eq (2 ^ (w - 1) % anc) (by omega), Nat.mod_eq_of_lt (by omega)]
  have e4 : ((((2 ^ (w - 1) : Nat) : Int) - ((2 ^ (w - 1) / ad : Nat) : Int) * (ad : Int)) %
      2 ^ w).toNat = 2 ^ (w - 1) % ad := by
    have := Nat.mod_add_div' (2 ^ (w - 1)) ad
    have hl := Nat.mod_lt (2 ^ (w - 1)) (show 0 < ad by omega)
    rw [wrap_eq (2 ^ (w - 1) % ad) (by omega), Nat.mod_eq_of_lt (by omega)]
  have e5 : ((w : Int) - 1) = ((w - 1 : Nat) : Int) := by omega
  rw [e1, e2, e3, e4, e5]
  obtain ⟨p, hp, hloop, hcrit, hpb⟩ := loopS (w := w) (by omega) (by omega) hadw hanc0 hancw
    (two_pow_mod_ne hpow) (2 * w) (w - 1) _ _ _ _ (by omega) rfl rfl rfl rfl hinit
  rw [hloop]
  dsimp only
  have hP0 := two_pow_pos' p
  have hpw : p + 2 ≤ 2 * w := by
    have h3 : 2 * (anc * (ad - 1)) < 2 ^ (2 * w - 1) := by
      have : 2 ^ (2 * w - 1) = 2 * (2 ^ (w - 1) * 2 ^ (w - 1)) := by
        rw [← Nat.pow_add, ← two_pow_succ']; congr 1; omega
      rw [this]
      have := Nat.mul_lt_mul_of_le_of_lt hancw (show ad - 1 < 2 ^ (w - 1) by omega) (two_pow_pos' _)
      omega
    have : p < 2 * w - 1 := (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).1 (by omega)
    omega
  have hMw : 2 ^ p / ad + 1 < 2 ^ w := by
    have h4 : 2 ^ p ≤ ad * (2 ^ w - 2) := by
      have ha := Nat.mul_le_mul_right (ad - 1) (show 2 * anc ≤ 2 ^ w by omega)
      rw [Nat.mul_assoc, Nat.mul_sub_one (2 ^ w) ad] at ha
      rw [Nat.mul_sub, Nat.mul_comm ad (2 ^ w)]
      omega
    have := Nat.div_le_of_le_mul h4
    generalize 2 ^ p / ad = Q at this ⊢
    omega
  refine ⟨p, anc, by omega, hpw, ?_, hcrit, hancm, hancw, hpb, fun hn => ?_, fun hpos => ?_, hMw⟩
  · rw [wrap_neg (d := 2 ^ p / ad + 1) (Nat.succ_pos _) (Nat.le_of_lt hMw),
      wrap_eq (2 ^ p / ad + 1) (by omega),
      Nat.mod_eq_of_lt hMw]
    congr 1; omega
  · have := htn hn; omega
  · have := htp hpos
    refine ⟨by omega, ?_⟩
    by_cases h : t % ad + 2 ≤ ad
    · left; omega
    · right
      rw [show 2 ^ (w - 1) + 1 = ad * (t / ad + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
        Nat.mul_mod_right]

/-- The dividend `2^k` when `2^k ≡ -1 (mod ad)`: `2^k * e ≤ 2^p` (the negative dividend
`-2^(w-1)` of a positive divisor, beyond the criterion's range). -/
theorem special_bound {k ad M p e : Nat} (hM : M * ad = 2 ^ p + e) (he : e < ad)
    (ht : (2 ^ k + 1) % ad = 0) (hkp : k ≤ p) : 2 ^ k * e ≤ 2 ^ p := by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero ht
  have hp : 2 ^ p = 2 ^ k * 2 ^ (p - k) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : 2 ^ (p - k) * (ad * c) = 2 ^ p + 2 ^ (p - k) := by
    rw [← hc, Nat.mul_add, Nat.mul_one, hp, Nat.mul_comm (2 ^ (p - k))]
  have h2 : ad * M + 2 ^ (p - k) = ad * (2 ^ (p - k) * c) + e := by
    rw [Nat.mul_left_comm, h1, Nat.mul_comm ad M, hM]; omega
  have h3 := congrArg (· % ad) h2
  simp only [Nat.mul_add_mod] at h3
  rw [Nat.mod_eq_of_lt he] at h3
  have h4 : e ≤ 2 ^ (p - k) := h3 ▸ Nat.mod_le _ _
  rw [hp]
  exact Nat.mul_le_mul_left _ h4

theorem ediv_two_pow_lo {y M : Int} {A B : Int} (hA : 0 < A) (hB : 0 < B) (hy : -A ≤ y)
    (hM0 : 0 ≤ M) (hMB : M ≤ B) : -A ≤ y * M / B := by
  apply Int.le_ediv_of_mul_le hB
  have h1 : 0 ≤ (y + A) * M := Int.mul_nonneg (by omega) hM0
  have h2 : 0 ≤ A * (B - M) := Int.mul_nonneg (by omega) (by omega)
  rw [Int.add_mul] at h1; rw [Int.mul_sub] at h2
  rw [Int.neg_mul]
  omega

theorem ediv_two_pow_hi {y M : Int} {A B : Int} (hA : 0 < A) (hB : 0 < B) (hy : y ≤ A)
    (hM0 : 0 ≤ M) (hMB : M < B) : y * M / B < A := by
  apply Int.ediv_lt_of_lt_mul hB
  have h1 : 0 ≤ (A - y) * M := Int.mul_nonneg (by omega) hM0
  have h2 : A * 1 ≤ A * (B - M) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  rw [Int.sub_mul] at h1; rw [Int.mul_sub, Int.mul_one] at h2
  omega

/-- **`magicS` is correct.** For a divisor `-2^(w-1) ≤ d < 2^(w-1)` whose absolute value is not a
power of two (`d ∉ {0, ±1, ±2, …}`), `magicS w d = (m, s)` with `m` a signed `w`-bit value and
`s < w`, and for every signed `w`-bit `x` the emitted sequence — `q1 = smulhi x m`, the add/sub
fix-up `q2`, `q3 = q2 >>ₛ s`, `q3 + (q3 >>> (w - 1))` — computes the truncated quotient
`x / d`; `q2` stays in the signed range (no wrap-around in the fix-up). -/
theorem magicS_spec {w : Nat} {d : Int} (hw : 3 ≤ w) (hd0 : d ≠ 0) (hdlo : -2 ^ (w - 1) ≤ d)
    (hdhi : d < 2 ^ (w - 1)) (hpow : ∀ k, d.natAbs ≠ 2 ^ k) :
    ∃ (m : Int) (s : Nat), Rust.magicS w d = (m, (s : Int)) ∧ -2 ^ (w - 1) ≤ m ∧
      m < 2 ^ (w - 1) ∧ s < w ∧
      ∀ x : Int, -2 ^ (w - 1) ≤ x → x < 2 ^ (w - 1) →
        -2 ^ (w - 1) ≤ (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) ∧
        (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) < 2 ^ (w - 1) ∧
        (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) / 2 ^ s +
          (if (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) / 2 ^ s < 0
            then 1 else 0) = x.tdiv d := by
  obtain ⟨p, anc, hp, hpw, heq, hcrit, hancm, hancw, hpb, hneg, hposf, hMw⟩ :=
    magicS_eq hw hd0 hdlo hdhi hpow
  obtain ⟨ad, had⟩ : ∃ ad, ad = d.natAbs := ⟨_, rfl⟩
  rw [← had] at heq hcrit hancm hpb hneg hposf hMw hpow
  have hadI : (ad : Int) = if d < 0 then -d else d := by
    rw [had]; split
    · exact Int.ofNat_natAbs_of_nonpos (by omega)
    · exact Int.natAbs_of_nonneg (by omega)
  have had0 : 0 < ad := by
    have : ad ≠ 0 := by intro h; rw [h] at hadI; split at hadI <;> omega
    omega
  have h2w := two_pow_int w
  have h2w1 := two_pow_int (w - 1)
  have htop : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← two_pow_succ']; congr 1; omega
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ p / ad + 1 := ⟨_, rfl⟩
  rw [← hM] at heq hMw
  have hR := Nat.mod_lt (2 ^ p) had0
  have hRn := two_pow_mod_ne hpow p
  have hMd : M * ad = 2 ^ p + (ad - 2 ^ p % ad) := by
    have := Nat.div_add_mod (2 ^ p) ad
    rw [hM]
    generalize 2 ^ p / ad = Q at this ⊢
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm Q ad]; omega
  refine ⟨_, p - w, heq, ?_⟩
  rw [BitVec.toInt_ofNat', Int.bmod_def]
  -- the multiplier `m` per case; `q2 = y * M / 2^w` with `y = ±x`
  have hMI : (1 : Int) ≤ M ∧ (M : Int) < 2 ^ w := by
    have : 1 ≤ M := by rw [hM]; exact Nat.succ_le_succ (Nat.zero_le _)
    constructor
    · omega
    · rw [h2w]; exact_mod_cast hMw
  have hhalf : ((2 ^ w : Nat) : Int) + 1 = 2 * ((2 ^ (w - 1) : Nat) : Int) + 1 := by
    rw [htop]; push_cast; rfl
  have key : ∀ y : Int, (d < 0 → y ≤ 2 ^ (w - 1)) → (0 < d → y < 2 ^ (w - 1)) →
      -2 ^ (w - 1) ≤ y → (y < 0 → -y ≤ 2 ^ (w - 1)) →
      y * M / 2 ^ w / 2 ^ (p - w) + (if y * M / 2 ^ w / 2 ^ (p - w) < 0 then 1 else 0) =
        y.tdiv ad := by
    intro y hy1 hy2 hy3 hy4
    have e1 : y * M / 2 ^ w / 2 ^ (p - w) = y * M / 2 ^ p := by
      rw [Int.ediv_ediv, ← Int.pow_add, show w + (p - w) = p by omega]
      have : ¬ ((2 : Int) ^ w < 0 ∧ ¬(2 : Int) ^ (p - w) ∣ y * ↑M / 2 ^ w) := by
        rw [h2w]; omega
      simp only [this, ite_false, Int.sub_zero]
    rw [e1]
    apply signed_core y had0 hMd (by omega)
    · intro n hn
      apply key_bound (by omega) hcrit hancm
      by_cases hd : d < 0
      · have := hneg hd; omega
      · have := hposf (by omega); omega
    · intro z hz hz0
      by_cases hz1 : z + 1 ≤ anc + ad
      · exact Nat.le_of_lt (key_bound (by omega) hcrit hancm hz1)
      · have hd : 0 < d := by
          apply Int.lt_of_not_ge; intro hd
          have := hneg (by omega); omega
        obtain ⟨h1, h2⟩ := hposf hd
        have hz2 : z = 2 ^ (w - 1) := by omega
        rcases h2 with h2 | h2
        · omega
        · have := special_bound hMd (by omega) h2 (by omega)
          rw [hz2]
          calc 2 ^ (w - 1) * (ad - 2 ^ p % ad) ≤ 2 ^ p := this
            _ ≤ (ad - 2 ^ (w - 1) % ad) * 2 ^ p := Nat.le_mul_of_pos_left _ (by
                have := Nat.mod_lt (2 ^ (w - 1)) had0; omega)
  have hrange : ∀ y : Int, -2 ^ (w - 1) ≤ y → y ≤ 2 ^ (w - 1) →
      -2 ^ (w - 1) ≤ y * M / 2 ^ w ∧ y * M / 2 ^ w < 2 ^ (w - 1) := by
    intro y h1 h2
    exact ⟨ediv_two_pow_lo (by rw [h2w1]; omega) (by rw [h2w]; omega) h1 (by omega) (by omega),
      ediv_two_pow_hi (by rw [h2w1]; omega) (by rw [h2w]; omega) h2 (by omega) hMI.2⟩
  by_cases hd : d < 0
  · -- `mul = 2^w - M`
    have hn : (((2 ^ w - M : Nat) : Int) % ((2 ^ w : Nat) : Int)) = ((2 ^ w - M : Nat) : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    simp only [hd, ite_true, hn]
    have hdI : d = -(ad : Int) := by rw [hadI]; simp [hd]
    by_cases hc : ((2 ^ w - M : Nat) : Int) < (((2 ^ w : Nat) : Int) + 1) / 2
    · -- `m = 2^w - M > 0`: `q2 = x * m / 2^w - x = -x * M / 2^w`
      simp only [hc, ite_true]
      refine ⟨by omega, by omega, by omega, fun x hx1 hx2 => ?_⟩
      have hm0 : (0 : Int) < ((2 ^ w - M : Nat) : Int) := by omega
      have hpos : ¬ (0 < d) := by omega
      simp only [hpos, false_and, ite_false, hd, hm0, and_self, ite_true]
      have e : x * ((2 ^ w - M : Nat) : Int) / 2 ^ w - x = -x * M / 2 ^ w := by
        have : x * ((2 ^ w - M : Nat) : Int) = -x * M + x * 2 ^ w := by
          rw [Int.natCast_sub (by omega), ← h2w, Int.mul_sub, Int.neg_mul]; omega
        rw [this, Int.add_mul_ediv_right _ _ (by rw [h2w]; omega)]; omega
      rw [e, hdI, Int.tdiv_neg, ← Int.neg_tdiv]
      obtain ⟨r1, r2⟩ := hrange (-x) (by omega) (by omega)
      exact ⟨r1, r2, key (-x) (fun _ => by omega) (fun h => by omega) (by omega) (fun _ => by omega)⟩
    · -- `m = -M ≤ 0`: no fix-up, `q2 = x * (-M) / 2^w`
      simp only [hc, ite_false]
      have em : ((2 ^ w - M : Nat) : Int) - ((2 ^ w : Nat) : Int) = -(M : Int) := by
        rw [Int.natCast_sub (by omega)]; omega
      rw [em]
      refine ⟨by omega, by omega, by omega, fun x hx1 hx2 => ?_⟩
      have hpos : ¬ (0 < d) := by omega
      have hm : ¬ (0 < -(M : Int)) := by omega
      simp only [hpos, false_and, ite_false, hm, and_false]
      rw [Int.mul_neg, ← Int.neg_mul, hdI, Int.tdiv_neg, ← Int.neg_tdiv]
      obtain ⟨r1, r2⟩ := hrange (-x) (by omega) (by omega)
      exact ⟨r1, r2, key (-x) (fun _ => by omega) (fun h => by omega) (by omega) (fun _ => by omega)⟩
  · have hdp : 0 < d := by omega
    have hn : ((M : Int) % ((2 ^ w : Nat) : Int)) = (M : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    simp only [hd, ite_false, hn]
    have hdI : d = (ad : Int) := by rw [hadI]; simp [hd]
    by_cases hc : (M : Int) < (((2 ^ w : Nat) : Int) + 1) / 2
    · -- `m = M > 0`: no fix-up
      simp only [hc, ite_true]
      refine ⟨by omega, by omega, by omega, fun x hx1 hx2 => ?_⟩
      have hm : ¬ ((M : Int) < 0) := by omega
      simp only [hdp, hm, and_false, ite_false, hd, false_and]
      rw [hdI]
      obtain ⟨r1, r2⟩ := hrange x (by omega) (by omega)
      exact ⟨r1, r2, key x (fun h => by omega) (fun _ => by omega) (by omega) (fun _ => by omega)⟩
    · -- `m = M - 2^w < 0`: `q2 = x * m / 2^w + x = x * M / 2^w`
      simp only [hc, ite_false]
      refine ⟨by omega, by omega, by omega, fun x hx1 hx2 => ?_⟩
      have hm : (M : Int) - ((2 ^ w : Nat) : Int) < 0 := by omega
      simp only [hdp, hm, and_self, ite_true]
      have e : x * ((M : Int) - ((2 ^ w : Nat) : Int)) / 2 ^ w + x = x * M / 2 ^ w := by
        have : x * ((M : Int) - ((2 ^ w : Nat) : Int)) = x * M + (-x) * 2 ^ w := by
          rw [Int.mul_sub, ← h2w, Int.neg_mul]; omega
        rw [this, Int.add_mul_ediv_right _ _ (by rw [h2w]; omega)]; omega
      rw [e, hdI]
      obtain ⟨r1, r2⟩ := hrange x (by omega) (by omega)
      exact ⟨r1, r2, key x (fun h => by omega) (fun _ => by omega) (by omega) (fun _ => by omega)⟩

/-! ## Bit-vector forms of the emitted sequences -/

open Clif

theorem umulhi_toNat {w : Nat} (x y : BitVec w) :
    (Sem.umulhi x y).toNat = x.toNat * y.toNat / 2 ^ w := by
  unfold Sem.umulhi
  have hx := x.isLt
  have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ (w + w) := by rw [Nat.pow_add]; exact Nat.mul_lt_mul'' hx hy
  have hw : 2 ^ w ≤ 2 ^ (w + w) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx hw), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy hw),
    Nat.mod_eq_of_lt hxy, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w)).2
  rwa [← Nat.pow_add]

theorem udiv_magic_noadd {w : Nat} (x b : BitVec w) (m s : Nat) (hm : m < 2 ^ w)
    (h : ∀ X < 2 ^ w, X * m / 2 ^ w / 2 ^ s = X / b.toNat) :
    Sem.umulhi x (BitVec.ofNat w m) >>> s = x / b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, umulhi_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hm, BitVec.toNat_udiv]
  exact h _ x.isLt

theorem udiv_magic_add {w : Nat} (x b : BitVec w) (m s : Nat) (hm : m < 2 ^ w)
    (h : ∀ X < 2 ^ w, ((X - X * m / 2 ^ w) / 2 + X * m / 2 ^ w) / 2 ^ (s - 1) = X / b.toNat) :
    ((x - Sem.umulhi x (BitVec.ofNat w m)) >>> 1 + Sem.umulhi x (BitVec.ofNat w m)) >>> (s - 1) =
      x / b := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hq0 : x.toNat * m / 2 ^ w ≤ x.toNat :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hm))
  have hle : Sem.umulhi x (BitVec.ofNat w m) ≤ x := by
    rw [BitVec.le_def, umulhi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]; exact hq0
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub_of_le hle, umulhi_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.pow_one, Nat.mod_eq_of_lt (by omega),
    BitVec.toNat_udiv]
  exact h _ hx

theorem urem_of_udiv {w : Nat} (x b : BitVec w) : x - x / b * b = x % b := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (x / b * b).toNat = x.toNat / b.toNat * b.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.isLt)
  have hle : x / b * b ≤ x := by rw [BitVec.le_def, h1]; exact Nat.div_mul_le_self _ _
  rw [BitVec.toNat_sub_of_le hle, h1, BitVec.toNat_umod, Nat.mod_eq_sub, Nat.mul_comm]

/-- The immediates of `iconst_u`/`iconst_s` (`asI64`, then truncated to the type). -/
theorem divc_ofInt_asI64 {w : Nat} (hw : w ≤ 64) (x : Int) :
    BitVec.ofInt w (Rust.asI64 x) = BitVec.ofInt w x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, Rust.asI64, BitVec.toInt_ofInt]
  have hd : ((2 ^ w : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) :=
    Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow 2 hw)
  rw [← Int.emod_emod_of_dvd _ hd, Int.bmod_emod, Int.emod_emod_of_dvd _ hd]

end Opt.Proof.DivConst

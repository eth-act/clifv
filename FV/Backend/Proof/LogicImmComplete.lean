import FV.Backend.Proof.IselCovSem

/-!
# Form coverage (V3): every logical immediate `ImmLogic.ofNat?` accepts is encoded

`LogicImmComplete`: for every value `ImmLogic.ofNat?` accepts and every logical op the emitter
expands, `logicImmOk` holds (`bitmaskEnc?` finds an encoding and `DecodeBitMasks` decodes it
back to the operand, also for the inverted value of `orn`/`bic`/`eon`).

Route. `ofNat?` accepts a 64-bit pattern `v` iff for some element size `e ∈ {2, …, 64}` the
pattern is `64/e` copies of its low element `x` and `x` has exactly two circular bit transitions
(`isRotatedRun`). Such an element is `rorN e (2^c - 1) r` with `0 < c < e`, `r < e`
(`eq_rorN`), and `v` is the replication `pat e c r` (`eq_repl`). What `logicImmOk` checks of `v`
is then decided by the kernel once per triple (`tripleOk`, 5334 triples, chunked by `c`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof

namespace LogicImm

/-! ## The finite decision over `(e, c, r)` -/

/-- `n` copies of the `e`-bit element `x`. -/
def repl (e x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => x + 2 ^ e * repl e x n

/-- The 64-bit pattern whose `e`-bit elements are `c` ones rotated right by `r`. -/
def pat (e c r : Nat) : Nat := repl e (rorN e (2 ^ c - 1) r) (64 / e)

/-- What `logicImmOk` checks, for the pattern `pat e c r` taken at 64 bits, its complement at
64 bits, and (when the pattern is a 32-bit value replicated) the 32-bit value and its
complement. -/
def tripleOk (e c r : Nat) : Bool :=
  let p := pat e c r
  bitmaskOk 64 true p (BitVec.ofNat 64 p) &&
  bitmaskOk 64 true (2 ^ 64 - 1 - p) (~~~(BitVec.ofNat 64 p)) &&
  (p / 2 ^ 32 != p % 2 ^ 32 ||
    (bitmaskOk 32 false (p % 2 ^ 32) (BitVec.ofNat 32 p) &&
     bitmaskOk 32 false (2 ^ 32 - 1 - p % 2 ^ 32) (~~~(BitVec.ofNat 32 p))))

/-- `f i` for every `i < n`. -/
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow f n && f n

theorem allBelow_spec {f : Nat → Bool} : ∀ {n}, allBelow f n = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    rw [allBelow, Bool.and_eq_true] at h
    by_cases hin : i < n
    · exact allBelow_spec h.1 i hin
    · rw [show i = n by omega]; exact h.2

/-- `tripleOk e c r` for every rotation `r < e`. -/
def runsOk (e c : Nat) : Bool := (List.range e).all fun r => tripleOk e c r

/-- `runsOk e c` for every run length `0 < c` in `[lo, lo + n)`. -/
def okBelow (e lo n : Nat) : Bool := allBelow (fun j => lo + j == 0 || runsOk e (lo + j)) n

theorem okBelow_spec {e lo n : Nat} (h : okBelow e lo n = true) {c r : Nat} (hlo : lo ≤ c)
    (hn : c < lo + n) (hc : 0 < c) (hr : r < e) : tripleOk e c r = true := by
  have := allBelow_spec h (c - lo) (by omega)
  rw [show lo + (c - lo) = c by omega, Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h0 | h1
  · omega
  · exact List.all_eq_true.1 h1 r (List.mem_range.2 hr)

-- Kernel decisions, one per element size up to 16 and per 8 run lengths above (a single
-- decision over a whole element size grows superlinearly in time and memory).
theorem ok2 : okBelow 2 0 2 = true := by decide +kernel
theorem ok4 : okBelow 4 0 4 = true := by decide +kernel
theorem ok8 : okBelow 8 0 8 = true := by decide +kernel
theorem ok16 : okBelow 16 0 16 = true := by decide +kernel
theorem ok32_0 : okBelow 32 0 8 = true := by decide +kernel
theorem ok32_1 : okBelow 32 8 8 = true := by decide +kernel
theorem ok32_2 : okBelow 32 16 8 = true := by decide +kernel
theorem ok32_3 : okBelow 32 24 8 = true := by decide +kernel
theorem ok64_0 : okBelow 64 0 8 = true := by decide +kernel
theorem ok64_1 : okBelow 64 8 8 = true := by decide +kernel
theorem ok64_2 : okBelow 64 16 8 = true := by decide +kernel
theorem ok64_3 : okBelow 64 24 8 = true := by decide +kernel
theorem ok64_4 : okBelow 64 32 8 = true := by decide +kernel
theorem ok64_5 : okBelow 64 40 8 = true := by decide +kernel
theorem ok64_6 : okBelow 64 48 8 = true := by decide +kernel
theorem ok64_7 : okBelow 64 56 8 = true := by decide +kernel

/-- **The finite decision**: `tripleOk` for every element size, run length and rotation. -/
theorem tripleOk_all {e c r : Nat} (he : e ∈ [2, 4, 8, 16, 32, 64]) (hc : 0 < c) (hce : c < e)
    (hr : r < e) : tripleOk e c r = true := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact okBelow_spec ok2 (Nat.zero_le c) hce hc hr
  · exact okBelow_spec ok4 (Nat.zero_le c) hce hc hr
  · exact okBelow_spec ok8 (Nat.zero_le c) hce hc hr
  · exact okBelow_spec ok16 (Nat.zero_le c) hce hc hr
  · rcases (by omega : c < 8 ∨ 8 ≤ c ∧ c < 16 ∨ 16 ≤ c ∧ c < 24 ∨ 24 ≤ c) with
      h | h | h | h
    · exact okBelow_spec ok32_0 (Nat.zero_le c) h hc hr
    · exact okBelow_spec ok32_1 h.1 h.2 hc hr
    · exact okBelow_spec ok32_2 h.1 h.2 hc hr
    · exact okBelow_spec ok32_3 h hce hc hr
  · rcases (by omega : c < 8 ∨ 8 ≤ c ∧ c < 16 ∨ 16 ≤ c ∧ c < 24 ∨ 24 ≤ c ∧ c < 32 ∨
        32 ≤ c ∧ c < 40 ∨ 40 ≤ c ∧ c < 48 ∨ 48 ≤ c ∧ c < 56 ∨ 56 ≤ c) with
      h | h | h | h | h | h | h | h
    · exact okBelow_spec ok64_0 (Nat.zero_le c) h hc hr
    · exact okBelow_spec ok64_1 h.1 h.2 hc hr
    · exact okBelow_spec ok64_2 h.1 h.2 hc hr
    · exact okBelow_spec ok64_3 h.1 h.2 hc hr
    · exact okBelow_spec ok64_4 h.1 h.2 hc hr
    · exact okBelow_spec ok64_5 h.1 h.2 hc hr
    · exact okBelow_spec ok64_6 h.1 h.2 hc hr
    · exact okBelow_spec ok64_7 h hce hc hr

/-! ## Counting transitions -/

/-- The number of `i < n` with `p i`. -/
def cnt (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt p n + (if p n then 1 else 0)

theorem foldl_cnt (p : Nat → Bool) (n k : Nat) :
    (List.range n).foldl (fun c i => if p i then c + 1 else c) k = k + cnt p n := by
  induction n generalizing k with
  | zero => simp [cnt]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    cases h : p n <;> simp [cnt, h] <;> omega

theorem cnt_zero {p : Nat → Bool} : ∀ {n}, cnt p n = 0 → ∀ i < n, p i = false
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    cases hp : p n <;> simp [cnt, hp] at h
    by_cases hin : i < n
    · exact cnt_zero h i hin
    · rw [show i = n by omega]; exact hp

theorem cnt_one {p : Nat → Bool} :
    ∀ {n}, cnt p n = 1 → ∃ a < n, p a = true ∧ ∀ i < n, p i = true → i = a
  | 0, h => by simp [cnt] at h
  | n + 1, h => by
    cases hp : p n <;> simp [cnt, hp] at h
    · obtain ⟨a, ha, hpa, hu⟩ := cnt_one h
      refine ⟨a, by omega, hpa, fun i hi hpi => ?_⟩
      by_cases hin : i < n
      · exact hu i hin hpi
      · rw [show i = n by omega, hp] at hpi; cases hpi
    · refine ⟨n, by omega, hp, fun i hi hpi => ?_⟩
      by_cases hin : i < n
      · rw [cnt_zero h i hin] at hpi; cases hpi
      · omega

theorem cnt_two {p : Nat → Bool} : ∀ {n}, cnt p n = 2 →
    ∃ a b, a < b ∧ b < n ∧ p a = true ∧ p b = true ∧ ∀ i < n, p i = true → i = a ∨ i = b
  | 0, h => by simp [cnt] at h
  | n + 1, h => by
    cases hp : p n <;> simp [cnt, hp] at h
    · obtain ⟨a, b, hab, hb, hpa, hpb, hu⟩ := cnt_two h
      refine ⟨a, b, hab, by omega, hpa, hpb, fun i hi hpi => ?_⟩
      by_cases hin : i < n
      · exact hu i hin hpi
      · rw [show i = n by omega, hp] at hpi; cases hpi
    · obtain ⟨a, ha, hpa, hu⟩ := cnt_one h
      refine ⟨a, n, ha, by omega, hpa, hp, fun i hi hpi => ?_⟩
      by_cases hin : i < n
      · exact Or.inl (hu i hin hpi)
      · exact Or.inr (by omega)

/-! ## Rotated runs -/

theorem mod_lt_two {n e : Nat} (h : n < 2 * e) : n % e = if n < e then n else n - e := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem testBit_rotr1 {e x i : Nat} (he : 0 < e) (hx : x < 2 ^ e) (hi : i < e) :
    (rotr1 e x).testBit i = x.testBit ((i + 1) % e) := by
  have h2 : x / 2 < 2 ^ (e - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel he]; exact hx
  unfold rotr1
  rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ h2]
  by_cases h : i < e - 1
  · simp only [h, ↓reduceIte]
    rw [Nat.testBit_div_two, Nat.mod_eq_of_lt (by omega)]
  · simp only [h, ↓reduceIte]
    rw [show i - (e - 1) = 0 by omega, show (i + 1) % e = 0 by
      rw [show i + 1 = e by omega, Nat.mod_self]]
    simp [Nat.testBit_zero]

/-- Two circular transitions (at `a < a'`) make a rotated run. -/
theorem run_of_two {b : Nat → Bool} {e a a' : Nat} (haa : a < a') (ha' : a' < e)
    (ht : ∀ i < e, (b i != b ((i + 1) % e)) = true ↔ i = a ∨ i = a') :
    ∃ c r, 0 < c ∧ c < e ∧ r < e ∧ ∀ i < e, b i = decide ((i + r) % e < c) := by
  have step : ∀ i, i + 1 < e → i ≠ a → i ≠ a' → b i = b (i + 1) := by
    intro i hi h1 h2
    have : ¬(b i != b ((i + 1) % e)) = true := fun h => by have := (ht i (by omega)).1 h; omega
    rw [Nat.mod_eq_of_lt hi] at this
    simpa using this
  have low : ∀ j ≤ a, b j = b 0 := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih => rw [← step j (by omega) (by omega) (by omega), ih (by omega)]
  have mid : ∀ k, a + 1 + k ≤ a' → b (a + 1 + k) = b (a + 1) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← ih (by omega), show a + 1 + (k + 1) = a + 1 + k + 1 by omega,
        step (a + 1 + k) (by omega) (by omega) (by omega)]
  have high : ∀ k, a' < e - 1 - k → b (e - 1 - k) = b 0 := by
    intro k hk
    induction k with
    | zero =>
      have : ¬(b (e - 1) != b ((e - 1 + 1) % e)) = true := fun h => by
        have := (ht (e - 1) (by omega)).1 h; omega
      rw [show e - 1 + 1 = e by omega, Nat.mod_self] at this
      simpa using this
    | succ k ih =>
      rw [step (e - 1 - (k + 1)) (by omega) (by omega) (by omega),
        show e - 1 - (k + 1) + 1 = e - 1 - k by omega, ih (by omega)]
  have flip : b (a + 1) = !b 0 := by
    have := (ht a (by omega)).2 (Or.inl rfl)
    rw [Nat.mod_eq_of_lt (by omega), low a (Nat.le_refl a)] at this
    revert this; cases b (a + 1) <;> cases b 0 <;> simp
  have hb : ∀ j < e, b j = if a < j ∧ j ≤ a' then !b 0 else b 0 := by
    intro j hj
    split
    · rw [← flip, show j = a + 1 + (j - a - 1) by omega, mid _ (by omega)]
    · by_cases h1 : j ≤ a
      · exact low j h1
      · rw [show j = e - 1 - (e - 1 - j) by omega, high _ (by omega)]
  cases h0 : b 0
  · refine ⟨a' - a, e - a - 1, by omega, by omega, by omega, fun i hi => ?_⟩
    rw [hb i hi, h0, mod_lt_two (by omega)]
    by_cases h1 : a < i ∧ i ≤ a' <;> by_cases h2 : i + (e - a - 1) < e <;> simp [h1, h2] <;>
      omega
  · refine ⟨e - (a' - a), e - a' - 1, by omega, by omega, by omega, fun i hi => ?_⟩
    rw [hb i hi, h0, mod_lt_two (by omega)]
    by_cases h1 : a < i ∧ i ≤ a' <;> by_cases h2 : i + (e - a' - 1) < e <;> simp [h1, h2] <;>
      omega

theorem testBit_rorN {e c r i : Nat} (hc : c ≤ e) (hr : r < e) (hi : i < e) :
    (rorN e (2 ^ c - 1) r).testBit i = decide ((i + r) % e < c) := by
  unfold rorN
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  rw [mod_lt_two (by omega)]
  simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  split <;> constructor <;> intro <;> omega

theorem rorN_lt {e c r : Nat} (hc : c ≤ e) : rorN e (2 ^ c - 1) r < 2 ^ e := by
  have h1 : 2 ^ c - 1 < 2 ^ e :=
    Nat.sub_one_lt_of_le (Nat.two_pow_pos c) (Nat.pow_le_pow_right (by decide) hc)
  refine Nat.or_lt_two_pow ?_ (Nat.mod_lt _ (Nat.two_pow_pos e))
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h1

/-- An element `isRotatedRun` accepts is `c` ones rotated right by `r`. -/
theorem eq_rorN {e x : Nat} (he : 0 < e) (hx : x < 2 ^ e) (h : isRotatedRun e x = true) :
    ∃ c r, 0 < c ∧ c < e ∧ r < e ∧ x = rorN e (2 ^ c - 1) r := by
  unfold isRotatedRun at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hcnt : cnt (fun i => (x ^^^ rotr1 e x).testBit i) e = 2 := by
    have := foldl_cnt (fun i => (x ^^^ rotr1 e x).testBit i) e 0
    rw [Nat.zero_add] at this
    rw [← this]; exact h.2
  obtain ⟨a, a', haa, ha', hpa, hpb, hu⟩ := cnt_two hcnt
  have ht : ∀ i < e, (x.testBit i != x.testBit ((i + 1) % e)) = true ↔ i = a ∨ i = a' := by
    intro i hi
    have : (x ^^^ rotr1 e x).testBit i = (x.testBit i != x.testBit ((i + 1) % e)) := by
      rw [Nat.testBit_xor, testBit_rotr1 he hx hi]
    rw [← this]
    exact ⟨hu i hi, by rintro (rfl | rfl) <;> assumption⟩
  obtain ⟨c, r, hc0, hce, hre, hb⟩ := run_of_two haa ha' ht
  refine ⟨c, r, hc0, hce, hre, Nat.eq_of_testBit_eq fun i => ?_⟩
  by_cases hi : i < e
  · rw [hb i hi, testBit_rorN (by omega) hre hi]
  · have hle : 2 ^ e ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hle),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rorN_lt (by omega)) hle)]

/-! ## Replicated elements -/

/-- A value below `2 ^ (e * n)` whose `n` base-`2^e` digits are all `x` is `repl e x n`. -/
theorem eq_repl {e x : Nat} : ∀ {n v : Nat}, v < 2 ^ (e * n) →
    (∀ k < n, v / 2 ^ (k * e) % 2 ^ e = x) → v = repl e x n
  | 0, v, hv, _ => by simp at hv; simp [repl, hv]
  | n + 1, v, hv, hd => by
    have h0 := hd 0 (by omega)
    simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one] at h0
    have ih : v / 2 ^ e = repl e x n := by
      refine eq_repl ?_ fun k hk => ?_
      · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos e), ← Nat.pow_add, ← Nat.mul_succ]
        exact hv
      · rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show e + k * e = (k + 1) * e by
          rw [Nat.succ_mul, Nat.add_comm]]
        exact hd (k + 1) (by omega)
    rw [repl, ← ih, ← h0, Nat.mod_add_div]

/-- A 64-bit pattern `ImmLogic.ofNat?` accepts is a replicated rotated run. -/
theorem pat_of_accept {v : Nat} (hv : v < 2 ^ 64)
    (h : ([2, 4, 8, 16, 32, 64].any fun e =>
      (List.range (64 / e)).all (fun k => (v / 2 ^ (k * e)) % 2 ^ e == v % 2 ^ e) &&
        isRotatedRun e (v % 2 ^ e)) = true) :
    ∃ e c r, e ∈ [2, 4, 8, 16, 32, 64] ∧ 0 < c ∧ c < e ∧ r < e ∧ v = pat e c r := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have he0 : 0 < e ∧ e * (64 / e) = 64 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨c, r, hc0, hce, hre, hx⟩ := eq_rorN he0.1 (Nat.mod_lt _ (Nat.two_pow_pos e)) h.2
  refine ⟨e, c, r, he, hc0, hce, hre, ?_⟩
  unfold pat
  rw [← hx]
  exact eq_repl (by rw [he0.2]; exact hv) fun k hk =>
    beq_iff_eq.1 (h.1 k (List.mem_range.2 hk))

theorem bitmaskOk_congr {M : Nat} {is64 : Bool} {a a' : Nat} {b b' : BitVec M}
    (h : bitmaskOk M is64 a b = true) (ha : a' = a) (hb : b' = b) :
    bitmaskOk M is64 a' b' = true := ha ▸ hb ▸ h

theorem ofNat_congr {w a b : Nat} (h : a % 2 ^ w = b % 2 ^ w) :
    BitVec.ofNat w a = BitVec.ofNat w b :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, h])

end LogicImm

open LogicImm in
/-- **`LogicImmComplete`**: the emitter encodes every logical immediate `ImmLogic.ofNat?`
accepts, for every logical op it expands. -/
theorem logicImmComplete : LogicImmComplete := by
  intro i sz op h hop
  obtain ⟨value, isz⟩ := i
  have hm := Nat.mod_lt (mask64 value) (Nat.two_pow_pos 32)
  cases sz <;> dsimp only [ImmLogic.ofNat?] at h <;> split at h <;> try cases h
  all_goals rename_i hok
  · -- 32 bits: the low 32 bits, replicated, form the pattern
    obtain ⟨e, c, r, he, hc, hce, hr, hp⟩ := pat_of_accept (by
      simp only [Nat.reducePow] at hm ⊢; omega) hok
    have ht := tripleOk_all he hc hce hr
    dsimp only [tripleOk] at ht
    generalize pat e c r = p at ht hp
    simp only [mask64, Nat.reducePow] at hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at ht
    obtain ⟨hC, hD⟩ := ht.2.resolve_left (by simp only [Nat.reducePow]; omega)
    cases op <;> simp only [logicOpOk, Bool.false_eq_true] at hop <;>
      dsimp only [logicImmOk, ImmLogic.invert, mask64] <;>
      first
      | exact bitmaskOk_congr hC (by (try simp only [Nat.reducePow]); omega)
          (ofNat_congr (by (try simp only [Nat.reducePow]); omega))
      | exact bitmaskOk_congr hD (by (try simp only [Nat.reducePow]); omega)
          (congrArg (~~~ ·) (ofNat_congr (by (try simp only [Nat.reducePow]); omega)))
  · -- 64 bits
    obtain ⟨e, c, r, he, hc, hce, hr, hp⟩ :=
      pat_of_accept (Nat.mod_lt _ (Nat.two_pow_pos 64)) hok
    have ht := tripleOk_all he hc hce hr
    dsimp only [tripleOk] at ht
    generalize pat e c r = p at ht hp
    simp only [Nat.reducePow] at hp
    simp only [Bool.and_eq_true] at ht
    obtain ⟨⟨hA, hB⟩, -⟩ := ht
    cases op <;> simp only [logicOpOk, Bool.false_eq_true] at hop <;>
      dsimp only [logicImmOk, ImmLogic.invert, mask64] <;>
      first
      | exact bitmaskOk_congr hA (by (try simp only [Nat.reducePow]); omega)
          (ofNat_congr (by (try simp only [Nat.reducePow]); omega))
      | exact bitmaskOk_congr hB (by (try simp only [Nat.reducePow]); omega)
          (congrArg (~~~ ·) (ofNat_congr (by (try simp only [Nat.reducePow]); omega)))

end Backend.Proof.Cov

import FV.Backend.Proof.IselEmitCtor
import FV.Backend.Proof.LogicImmComplete

/-!
# Emission conditions of the ISLE lowering (V6c): the model

`emModel`: the `CovModel` of the driver's semantics for the emission analysis (`aextE`,
`actorE`, `apreE`, V3's oracle `aOracle`), with state invariant `EmSince s0` (every instruction
emitted since `s0` has the emission conditions and no branch targets). Its fields:
* `extE_sound`: `imm12_from_u64`/`u8_from_u64` give their leaves, the other extractors V3's
  `ext_sound`;
* `ctorE_sound`: `actorE` describes the result (`actorE_sound`, from `externCtor_res`; V3's
  `ctor_sound` for the rest) and `EmSince s0` is kept (`externCtor_em`, `emChk_sound`);
* `oracleE_sound`: `operand_size` keeps the state (V3's `oracle_sound`, `os_run`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Immediates -/

theorem imm12_lt {x : Nat} {i : Imm12} (h : Imm12.ofNat? x = some i) : i.bits < 4096 := by
  unfold Imm12.ofNat? at h
  dsimp only at h
  split at h
  · cases h; dsimp only; omega
  · split at h
    · cases h
      rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      dsimp only
      omega
    · cases h

theorem mwc_bounds {x : Nat} {m : MoveWideConst} (h : MoveWideConst.ofNat? x = some m) :
    m.bits < 2 ^ 16 ∧ m.shift < 4 ∧ (x < 2 ^ 32 → m.shift < 2) := by
  unfold MoveWideConst.ofNat? mask64 at h
  dsimp only at h
  have hm : x % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  simp only [Nat.reducePow] at h hm ⊢
  split at h
  · cases h; refine ⟨by assumption, by dsimp only; omega, fun _ => by dsimp only; omega⟩
  rename_i h0
  split at h
  · cases h
    rename_i h1
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    exact ⟨by dsimp only; omega, by dsimp only; omega, fun _ => by dsimp only; omega⟩
  rename_i h1
  split at h
  · cases h
    rename_i h2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2
    refine ⟨by dsimp only; omega, by dsimp only; omega, fun hx => ?_⟩
    exfalso
    omega
  rename_i h2
  split at h
  · cases h
    rename_i h3
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2 h3
    refine ⟨by dsimp only; omega, by dsimp only; omega, fun hx => ?_⟩
    exfalso
    omega
  · cases h

/-! ## Type bounds -/

theorem foldl_max_ge (g : CTy → Nat) : ∀ (l : List CTy) (m : Nat),
    m ≤ l.foldl (fun m t => max m (g t)) m
  | [], _ => Nat.le_refl _
  | t :: l, m => Nat.le_trans (Nat.le_max_left m (g t)) (foldl_max_ge g l (max m (g t)))

theorem foldl_max_mem (g : CTy → Nat) : ∀ (l : List CTy) (m : Nat) (t : CTy), t ∈ l →
    g t ≤ l.foldl (fun m t => max m (g t)) m
  | [], _, _, h => by cases h
  | a :: l, m, t, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right m (g t)) (foldl_max_ge g l _)
    · exact foldl_max_mem g l _ t h

/-- `tyB` bounds `g` of every type the abstract value names. -/
theorem tyB_ge {a : AW} {g : CTy → Nat} {b : Nat} (h : tyB a g = some b) {ty : CTy}
    (hv : γ f ctx a (.ty ty)) : g ty ≤ b := by
  cases a with
  | ty ts =>
    simp only [tyB, Option.some.injEq] at h
    subst h
    obtain ⟨t, ht, he⟩ := hv
    cases he
    exact foldl_max_mem g ts 0 _ ht
  | _ => simp [tyB] at h

theorem shB_lt {ty : CTy} {x : Nat} (h : Nat.land x (ty.bits - 1) < 64) :
    Nat.land x (ty.bits - 1) < shB ty := by
  have : Nat.land x (ty.bits - 1) ≤ ty.bits - 1 := Nat.and_le_right
  unfold shB
  omega

theorem sh_lt {ty : CTy} {s : Nat} (h : s ≤ 63) :
    Nat.land s (ty.bits - 1) < shB ty ∧ Nat.land s (ty.bits - 1) < 64 := by
  have h1 : Nat.land s (ty.bits - 1) ≤ s := Nat.and_le_left
  exact ⟨shB_lt (by omega), by omega⟩

theorem mwc_lt_mwB {ty : CTy} {x : Nat} {m : MoveWideConst} (h : MoveWideConst.ofNat? x = some m)
    (hx : ty.bits < 64 → x < 2 ^ ty.bits) : m.shift < mwB ty := by
  obtain ⟨-, h4, h2⟩ := mwc_bounds h
  unfold mwB
  split
  · rename_i hb
    refine h2 (Nat.lt_of_lt_of_le (hx (by omega)) ?_)
    exact Nat.pow_le_pow_right (by decide) hb
  · exact h4

/-! ## Conditions -/

theorem cond_mem_condsOk {c : Cond} (h : c ≠ .al ∧ c ≠ .nv) :
    γ f ctx condsOk (.data tyCond c.idx []) := by
  refine γAny_iff.mpr ⟨.data tyCond c.idx [], ?_, [], rfl, trivial⟩
  refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · cases c <;> simp [Cond.all]
  · obtain ⟨h1, h2⟩ := h
    cases c <;> simp_all

theorem invert_ne' {c : Cond} (h : c ≠ .al ∧ c ≠ .nv) : c.invert ≠ .al ∧ c.invert ≠ .nv := by
  cases c <;> simp_all [Cond.invert]

/-! ## Constructors -/

theorem apre_of_apreE {id : TermId} {as : List AW} (h : apreE id as = true) : apre id as = true := by
  simp only [apreE, Bool.and_eq_true] at h
  exact h.1

theorem resE_of {id : TermId} {vs : List V} {v : V}
    (h : (∃ q, tyPred id = some q) ∨ ResE id vs v) (hp : tyPred id = none) : ResE id vs v := by
  rcases h with ⟨q, hq⟩ | h
  · rw [hp] at hq; cases hq
  · exact h

set_option maxHeartbeats 4000000 in
/-- **`actorE` describes the result** of an extern constructor (V3's `actor` where it falls
back). -/
theorem actorE_sound {id : TermId} {as : List AW} {vs : List V} {v : V} (hvs : Holds2 f ctx as vs)
    (h3 : γ f ctx (actor id as) v) (hres : (∃ q, tyPred id = some q) ∨ ResE id vs v) :
    γ f ctx (actorE id as) v := by
  unfold actorE
  by_cases h1 : (id == TId.imm_shift_from_imm64) = true
  · simp only [h1, ↓reduceIte]
    obtain rfl := eq_of_beq h1
    obtain ⟨ty, n, rfl, rfl, hlt⟩ := (resE_of hres rfl).shImm rfl
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    dsimp only
    split
    · rename_i bd hb
      exact ⟨_, rfl, Nat.lt_of_lt_of_le (shB_lt hlt) (tyB_ge hb ha)⟩
    · exact ⟨_, rfl, hlt⟩
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (id == TId.imm_shift_from_u8) = true
  · simp only [h2, ↓reduceIte]
    obtain rfl := eq_of_beq h2
    obtain ⟨n, rfl, rfl, hlt⟩ := (resE_of hres rfl).shU8 rfl
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    split
    · rename_i b heq
      cases heq
      obtain ⟨i, he, h0, hb⟩ := (ha : NumOk .int b (.int n))
      cases he
      exact ⟨_, rfl, by omega⟩
    · exact ⟨_, rfl, by omega⟩
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  by_cases h3' : (id == TId.u8_into_uimm5) = true
  · simp only [h3', ↓reduceIte]
    obtain rfl := eq_of_beq h3'
    obtain ⟨n, rfl, hlt⟩ := (resE_of hres rfl).uimm5 rfl
    exact ⟨_, rfl, by omega⟩
  simp only [h3', Bool.false_eq_true, ↓reduceIte]
  by_cases h4 : (id == TId.u8_into_imm12) = true
  · simp only [h4, ↓reduceIte]
    obtain rfl := eq_of_beq h4
    obtain ⟨n, i, rfl, hi⟩ := (resE_of hres rfl).imm12 rfl
    exact ⟨_, rfl, imm12_lt hi⟩
  simp only [h4, Bool.false_eq_true, ↓reduceIte]
  by_cases h5 : (id == TId.move_wide_const_from_u64 || id == TId.move_wide_const_from_inverted_u64) = true
  · simp only [h5, ↓reduceIte]
    have hid : id = TId.move_wide_const_from_u64 ∨ id = TId.move_wide_const_from_inverted_u64 := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using h5
    have hp : tyPred id = none := by rcases hid with rfl | rfl <;> rfl
    obtain ⟨ty, n, x, m, rfl, rfl, hm, hx⟩ := (resE_of hres hp).mwc hid
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    have hb := mwc_bounds hm
    dsimp only
    split
    · rename_i bd hbd
      exact ⟨_, rfl, hb.1, Nat.lt_of_lt_of_le (mwc_lt_mwB hm hx) (tyB_ge hbd ha)⟩
    · exact ⟨_, rfl, hb.1, hb.2.1⟩
  simp only [h5, Bool.false_eq_true, ↓reduceIte]
  by_cases h6 : (id == TId.lshl_from_imm64 || id == TId.ashr_from_u64) = true
  · simp only [h6, ↓reduceIte]
    have hid : id = TId.lshl_from_imm64 ∨ id = TId.ashr_from_u64 := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using h6
    have hp : tyPred id = none := by rcases hid with rfl | rfl <;> rfl
    obtain ⟨ty, n, s, o, rfl, rfl, hs, ho⟩ := (resE_of hres hp).sh hid
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    have hb := sh_lt (ty := ty) hs
    dsimp only
    split
    · rename_i bd hbd
      exact ⟨_, rfl, Nat.lt_of_lt_of_le hb.1 (tyB_ge hbd ha), ho⟩
    · exact ⟨_, rfl, hb.2, ho⟩
  simp only [h6, Bool.false_eq_true, ↓reduceIte]
  by_cases h7 : (id == TId.a64_extr_imm) = true
  · simp only [h7, ↓reduceIte]
    obtain rfl := eq_of_beq h7
    obtain ⟨ty, s, o, rfl, rfl, ho⟩ := (resE_of hres rfl).extr rfl
    obtain ⟨a, b, rfl, -, hb⟩ := holds2_two hvs
    split
    · rename_i x bd heq
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨s', he, hlt⟩ := (hb : NumOk .immShift bd (.op (.immShift s)))
      cases he
      exact ⟨_, rfl, hlt, ho⟩
    · exact h3
  simp only [h7, Bool.false_eq_true, ↓reduceIte]
  by_cases h8 : (id == TId.bfm_immr || id == TId.bfm_imms) = true
  · simp only [h8, ↓reduceIte]
    have hid : id = TId.bfm_immr ∨ id = TId.bfm_imms := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using h8
    have hp : tyPred id = none := by rcases hid with rfl | rfl <;> rfl
    obtain ⟨ty, rest, n, rfl, rfl, hn⟩ := (resE_of hres hp).bfm hid
    obtain ⟨a, bs, rfl, ha, -⟩ := γL_cons hvs
    dsimp only
    split
    · rename_i bd hbd
      exact ⟨_, rfl, Nat.lt_of_lt_of_le hn (tyB_ge hbd ha)⟩
    · exact h3
  simp only [h8, Bool.false_eq_true, ↓reduceIte]
  by_cases h9 : (id == TId.negate_imm_shift) = true
  · simp only [h9, ↓reduceIte]
    obtain rfl := eq_of_beq h9
    obtain ⟨ty, x, n, rfl, rfl, hn⟩ := (resE_of hres rfl).neg rfl
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    dsimp only
    split
    · rename_i bd hbd
      exact ⟨_, rfl, Nat.lt_of_lt_of_le hn (tyB_ge hbd ha)⟩
    · exact h3
  simp only [h9, Bool.false_eq_true, ↓reduceIte]
  by_cases h10 : (id == TId.rotr_opposite_amount) = true
  · simp only [h10, ↓reduceIte]
    obtain rfl := eq_of_beq h10
    obtain ⟨ty, x, n, rfl, rfl, hn⟩ := (resE_of hres rfl).rotr rfl
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    dsimp only
    split
    · rename_i bd hbd
      exact ⟨_, rfl, Nat.lt_of_lt_of_le hn (tyB_ge hbd ha)⟩
    · exact ⟨_, rfl, by omega⟩
  simp only [h10, Bool.false_eq_true, ↓reduceIte]
  by_cases h11 : (id == TId.test_and_compare_bit_const) = true
  · simp only [h11, ↓reduceIte]
    obtain rfl := eq_of_beq h11
    obtain ⟨ty, x, n, rfl, rfl, hn, hn64⟩ := (resE_of hres rfl).tbit rfl
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    dsimp only
    split
    · rename_i bd hbd
      have := tyB_ge hbd ha
      exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, by omega, by omega⟩
  simp only [h11, Bool.false_eq_true, ↓reduceIte]
  by_cases h12 : (id == TId.ty_bits) = true
  · simp only [h12, ↓reduceIte]
    obtain rfl := eq_of_beq h12
    obtain ⟨ty, rfl, rfl⟩ := (resE_of hres rfl).bits rfl
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    dsimp only
    split
    · rename_i bd hbd
      have := tyB_ge hbd ha
      exact ⟨_, rfl, by omega, by omega⟩
    · exact h3
  simp only [h12, Bool.false_eq_true, ↓reduceIte]
  by_cases h13 : (id == TId.shift_masked_imm) = true
  · simp only [h13, ↓reduceIte]
    obtain rfl := eq_of_beq h13
    obtain ⟨ty, x, n, rfl, rfl, hn⟩ := (resE_of hres rfl).smask rfl
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    dsimp only
    split
    · rename_i bd hbd
      have := tyB_ge hbd ha
      exact ⟨_, rfl, by omega, by omega⟩
    · exact h3
  simp only [h13, Bool.false_eq_true, ↓reduceIte]
  by_cases h14 : (id == TId.imm_size_from_type) = true
  · simp only [h14, ↓reduceIte]
    obtain rfl := eq_of_beq h14
    rcases (resE_of hres rfl).isize rfl with rfl | rfl
    · exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, by omega, by omega⟩
  simp only [h14, Bool.false_eq_true, ↓reduceIte]
  by_cases h15 : (id == TId.cond_code) = true
  · simp only [h15, ↓reduceIte]
    obtain rfl := eq_of_beq h15
    obtain ⟨c, rfl, hc⟩ := (resE_of hres rfl).cc rfl
    exact cond_mem_condsOk hc
  simp only [h15, Bool.false_eq_true, ↓reduceIte]
  by_cases h16 : (id == TId.invert_cond) = true
  · simp only [h16, ↓reduceIte]
    obtain rfl := eq_of_beq h16
    obtain ⟨x, c, rfl, hc, rfl⟩ := (resE_of hres rfl).inv rfl
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    dsimp only
    split
    · rename_i hca
      exact cond_mem_condsOk (invert_ne' (condA_sound hca ha hc))
    · exact h3
  simp only [h16, Bool.false_eq_true, ↓reduceIte]
  by_cases h17 : (id == TId.gen_call_info) = true
  · simp only [h17, ↓reduceIte]
    obtain rfl := eq_of_beq h17
    obtain ⟨n, us, ds, rfl⟩ := (resE_of hres rfl).call rfl
    exact ⟨_, rfl, fun r hr => by cases hr⟩
  simp only [h17, Bool.false_eq_true, ↓reduceIte]
  by_cases h18 : (id == TId.gen_call_ind_info) = true
  · simp only [h18, ↓reduceIte]
    obtain rfl := eq_of_beq h18
    obtain ⟨x, r, rest, us, ds, rfl, rfl⟩ := (resE_of hres rfl).callInd rfl
    split
    · rename_i a0 ra a2 a3 a4
      obtain ⟨_, _, he, -, hl⟩ := γL_cons hvs
      cases he
      obtain ⟨_, _, he, hr, -⟩ := γL_cons hl
      cases he
      split
      · rename_i hv
        obtain ⟨n, rfl⟩ := isV_sound hv hr
        exact ⟨_, rfl, fun r' hr' => by cases hr'; exact ⟨n, rfl⟩⟩
      · exact h3
    · exact h3
  simp only [h18, Bool.false_eq_true, ↓reduceIte]
  by_cases h19 : (id == TId.u8_into_u32 || id == TId.u8_into_u64 || id == TId.u16_into_u64 ||
      id == TId.u32_into_u64 || id == TId.i32_into_i64) = true
  · simp only [h19, ↓reduceIte]
    have hid : id = TId.u8_into_u32 ∨ id = TId.u8_into_u64 ∨ id = TId.u16_into_u64 ∨
        id = TId.u32_into_u64 ∨ id = TId.i32_into_i64 := by
      simp only [Bool.or_eq_true, beq_iff_eq] at h19
      rcases h19 with (((h | h) | h) | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr h)))
    have hp : tyPred id = none := by
      rcases hid with rfl | rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨n, rfl, rfl⟩ := (resE_of hres hp).cast hid
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    split
    · rename_i b heq
      cases heq
      exact ha
    · exact h3
  simp only [h19, Bool.false_eq_true, ↓reduceIte]
  exact h3

/-- The instructions a constructor call with `apreE` emits have the emission conditions and no
branch targets. -/
theorem emE_ok {id : TermId} {as : List AW} {vs : List V} (hvs : Holds2 f ctx as vs)
    (hpre : apreE id as = true) {m : MInst} (h : EmE id vs m) : m.emitOk = true ∧ m.targets = [] := by
  rcases h with h | ⟨rfl, i, rfl, hi⟩
  · exact h
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    simp only [apreE, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hpre
    obtain ⟨h1, h2⟩ := emChk_sound hpre.2 ha hi
    exact ⟨h1, h2 rfl⟩

/-- **Constructors** (V6c): `actorE` describes the result, `EmSince s0` is kept. -/
theorem ctorE_sound (hctx : CtxInv f ctx) (s0 : LState) (as : List AW) (vs : List V) (term : Term)
    (v : V) (st st' : LState) (hvs : Holds2 f ctx as vs) (hIs : EmSince s0 st)
    (hpre : apreE term.id as = true) (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γ f ctx (actorE term.id as) v ∧ EmSince s0 st' := by
  have h3 := (ctor_sound logicImmComplete hctx st as vs term v st st' hvs ⟨[], by simp, by simp⟩
    (apre_of_apreE hpre) h).1
  refine ⟨actorE_sound hvs h3 (externCtor_res ctx term vs st v st' h), ?_⟩
  obtain ⟨ms0, h0, h1⟩ := hIs
  obtain ⟨ms, h2, h4⟩ := externCtor_em ctx term vs st v st' h
  refine ⟨ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact h1 m hm
  · exact emE_ok hvs hpre (h4 m hm)

/-! ## Extractors -/

/-- **Extractors** (V6c): `aextE` describes the outputs. -/
theorem extE_sound (hctx : CtxInv f ctx) (hcl : Clean ctx) (a : AW) (term : Term) (v : V)
    (st : LState) (fs : List V) (hv : γ f ctx a v) (h : (sem ctx).extract term v st = .ok fs) :
    HoldsP f ctx (aextE term.id a) fs := by
  unfold aextE
  split
  · rename_i hid
    have hid := eq_of_beq hid
    have hp : tyPred term.id = none := by rw [hid]; rfl
    obtain ⟨n, i, rfl, hi⟩ := (externExtract_ext ctx term v st hp fs h).imm12 hid
    exact holdsP_single ⟨i, rfl, imm12_lt hi⟩
  split
  · rename_i hid
    have hid := eq_of_beq hid
    have hp : tyPred term.id = none := by rw [hid]; rfl
    obtain ⟨i, rfl, h0, h1⟩ := (externExtract_ext ctx term v st hp fs h).u8 hid
    exact holdsP_single ⟨i, rfl, h0, h1⟩
  · exact ext_sound hctx hcl a term v st fs hv h

end Backend.Proof.Cov

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-- **The `operand_size` oracle** (V6c): it keeps the lowering state. -/
theorem oracleE_sound (s0 : LState) (cfg : Config) (hc : cfg.checkOverlap = false) (n : Nat)
    (ty : TypeId) (t : TermId) (as : List AW) (vs : List V) (a : AW) (s : LState)
    (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId)
    (ha : aOracle t as = some a) (hvs : Holds2 f ctx as vs) (hIs : EmSince s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    EmSince s0 s' ∧ ∀ v, r = some v → γ f ctx a v := by
  have hγ := (oracle_sound s cfg hc n ty t as vs a s tr r s' tr' ha hvs ⟨[], by simp, by simp⟩ h).2
  have ht : t = 305 := by
    unfold aOracle at ha
    split at ha
    · exact eq_of_beq ‹_›
    · cases ha
  subst ht
  have hs := (os_run hc h).1
  simp only at hs
  subst hs
  exact ⟨hIs, hγ⟩

/-- **The emission model** of the driver's semantics: state invariant `EmSince s0`. -/
def emModel (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (s0 : LState) :
    CovModel aextE actorE apreE aOracle program f ctx where
  Is := EmSince s0
  ext := fun a term v st fs hv h => extE_sound hctx hcl a term v st fs hv h
  ctor := fun as vs term v st st' hvs hIs hpre h =>
    ctorE_sound hctx s0 as vs term v st st' hvs hIs hpre h
  oracle := oracleE_sound s0

@[simp] theorem emModel_Is (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (s0 : LState) :
    (emModel hctx hcl s0).Is = EmSince s0 := rfl

end Backend.Proof.Driver

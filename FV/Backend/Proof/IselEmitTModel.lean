module

public import FV.Backend.Proof.IselEmitTChk
public import FV.Backend.Proof.IselEmitModel
public import FV.Backend.Proof.IselCovTModel

@[expose] public section

/-!
# Emission conditions of the typed ISLE lowering (S11): the model

`emModelT`: the `CovModel` of the driver's semantics for the typed emission analysis (`aextET`,
`actorET`, `apreET`, the typed oracle `aOracle`) over a float-capable context (`CtxInvT`) whose
statements belong to the instruction families (`FamCover`), with state invariant `EmSince s0`.
`IselEmitModel` over `AT`: the facts about the extern helpers' results are context-independent
(`Cov.externCtor_res`, `Cov.externCtor_em`, `Cov.externExtract_ext`); where the transfer functions
fall back, the typed `ctor_sound`/`ext_sound`/`oracle_sound`.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (NumOk Clean CovSince foldl_max_mem shB_lt sh_lt mwc_lt_mwB mwc_bounds
  imm12_lt invert_ne' resE_of ResE EmE externCtor_res externCtor_em externExtract_ext os_run
  shB mwB logicImmComplete)

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Type bounds -/

/-- `tyB` bounds `g` of every type the abstract value names. -/
theorem tyB_ge {a : AT} {g : CTy → Nat} {b : Nat} (h : tyB a g = some b) {ty : CTy}
    (hv : γ f ctx a (.ty ty)) : g ty ≤ b := by
  cases a with
  | ty ts =>
    simp only [tyB, Option.some.injEq] at h
    subst h
    obtain ⟨t, ht, he⟩ := hv
    cases he
    exact foldl_max_mem g ts 0 _ ht
  | _ => simp [tyB] at h

/-! ## Conditions -/

theorem cond_mem_condsOk {c : Cond} (h : c ≠ .al ∧ c ≠ .nv) :
    γ f ctx condsOk (.data tyCond c.idx []) := by
  refine γAny_iff.mpr ⟨.data tyCond c.idx [], ?_, [], rfl, trivial⟩
  refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · cases c <;> simp [Cond.all]
  · obtain ⟨h1, h2⟩ := h
    cases c <;> simp_all


/-! ## Constructors -/

theorem apre_of_apreET {id : TermId} {as : List AT} (h : apreET id as = true) : apre id as = true := by
  simp only [apreET, Bool.and_eq_true] at h
  exact h.1

set_option maxHeartbeats 4000000 in
/-- **`actorET` describes the result** of an extern constructor (V3's `actor` where it falls
back). -/
theorem actorET_sound {id : TermId} {as : List AT} {vs : List V} {v : V} (hvs : Holds2 f ctx as vs)
    (h3 : γ f ctx (actor id as) v) (hres : (∃ q, tyPred id = some q) ∨ ResE id vs v) :
    γ f ctx (actorET id as) v := by
  unfold actorET
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

/-- The instructions a constructor call with `apreET` emits have the emission conditions and no
branch targets. -/
theorem emE_ok {id : TermId} {as : List AT} {vs : List V} (hvs : Holds2 f ctx as vs)
    (hpre : apreET id as = true) {m : MInst} (h : EmE id vs m) : m.emitOk = true ∧ m.targets = [] := by
  rcases h with h | ⟨rfl, i, rfl, hi⟩
  · exact h
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    simp only [apreET, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hpre
    obtain ⟨h1, h2⟩ := emChk_sound hpre.2 ha hi
    exact ⟨h1, h2 rfl⟩

/-- **Constructors** (V6c): `actorET` describes the result, `EmSince s0` is kept. -/
theorem ctorET_sound (hctx : CtxInvT f ctx) (s0 : LState) (as : List AT) (vs : List V) (term : Term)
    (v : V) (st st' : LState) (hvs : Holds2 f ctx as vs) (hIs : EmSince s0 st)
    (hpre : apreET term.id as = true) (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γ f ctx (actorET term.id as) v ∧ EmSince s0 st' := by
  have h3 := (ctor_sound logicImmComplete hctx st as vs term v st st' hvs ⟨[], by simp, by simp⟩
    (apre_of_apreET hpre) h).1
  refine ⟨actorET_sound hvs h3 (externCtor_res ctx term vs st v st' h), ?_⟩
  obtain ⟨ms0, h0, h1⟩ := hIs
  obtain ⟨ms, h2, h4⟩ := externCtor_em ctx term vs st v st' h
  refine ⟨ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact h1 m hm
  · exact emE_ok hvs hpre (h4 m hm)

/-! ## Extractors -/

/-- **Extractors** (V6c): `aextET` describes the outputs. -/
theorem extET_sound (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (a : AT) (term : Term) (v : V)
    (st : LState) (fs : List V) (hv : γ f ctx a v) (h : (sem ctx).extract term v st = .ok fs) :
    HoldsP f ctx (aextET term.id a) fs := by
  unfold aextET
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
  · exact ext_sound hctx hcl hfam a term v st fs hv h


/-- **The `operand_size` oracle** (V6c): it keeps the lowering state. -/
theorem oracleET_sound (s0 : LState) (cfg : Config) (hc : cfg.checkOverlap = false) (n : Nat)
    (ty : TypeId) (t : TermId) (as : List AT) (vs : List V) (a : AT) (s : LState)
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

/-- **The typed emission model** of the driver's semantics: state invariant `EmSince s0`. -/
def emModelT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (s0 : LState) :
    CovModel aextET actorET apreET aOracle program f ctx where
  Is := EmSince s0
  ext := fun a term v st fs hv h => extET_sound hctx hcl hfam a term v st fs hv h
  ctor := fun as vs term v st st' hvs hIs hpre h =>
    ctorET_sound hctx s0 as vs term v st st' hvs hIs hpre h
  oracle := oracleET_sound s0

@[simp] theorem emModelT_Is (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx)
    (s0 : LState) : (emModelT hctx hcl hfam s0).Is = EmSince s0 := rfl

end Backend.Proof.CovT

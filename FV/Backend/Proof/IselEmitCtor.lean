import FV.Backend.Proof.IselEmitChk
import FV.Backend.Proof.IselEmitDefs
import FV.Backend.Proof.IselCovModel

/-!
# Emission conditions of the ISLE lowering (V6c): the extern helpers

* `externCtor_em`: every extern constructor emits only instructions with the emission conditions
  and no branch targets (`load_constant_full`'s `movz`/`movn`/`movk`s: `loadConstantFull_em`;
  `gen_call_args`' stores; `gen_return`'s `rets`), except `emit`'s instruction.
* `externCtor_res`: what the extern constructors `actorE` describes precisely return (`ResE`).
* `externExtract_ext`: what `imm12_from_u64` and `u8_from_u64` return (`ExtE`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-! ## The state invariant -/

theorem emSince_self (s : LState) : EmSince s s := ⟨[], by simp, by simp⟩

theorem emSince_push {s0 s : LState} {m : MInst} (h : EmSince s0 s) (hm : m.emitOk = true)
    (ht : m.targets = []) : EmSince s0 (s.emit m) := by
  obtain ⟨ms, h1, h2⟩ := h
  refine ⟨ms ++ [m], by simp [LState.emit, h1], fun m' hm' => ?_⟩
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact h2 m' hm'
  · simp only [List.mem_singleton] at hm'; subst hm'; exact ⟨hm, ht⟩

theorem emSince_comp {s0 s1 s2 : LState} (h1 : EmSince s0 s1) (h2 : EmSince s1 s2) :
    EmSince s0 s2 := by
  obtain ⟨ms1, e1, h1⟩ := h1
  obtain ⟨ms2, e2, h2⟩ := h2
  refine ⟨ms1 ++ ms2, by rw [e2, e1]; simp, fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact h1 m hm
  · exact h2 m hm

/-! ## `load_constant_full` -/

theorem size_slices (s : OperandSize) {sh : Nat} (h : sh < s.bits / 16) :
    sh < (if s.is64 then 4 else 2) := by
  cases s <;> simp [OperandSize.bits, OperandSize.is64] at h ⊢ <;> omega

theorem size_slices_pos (s : OperandSize) : 0 < s.bits / 16 := by
  cases s <;> decide

theorem findD_lt {n : Nat} (hn : 0 < n) (p : Nat → Bool) : ((List.range n).find? p).getD 0 < n := by
  cases h : (List.range n).find? p with
  | none => exact hn
  | some x => exact List.mem_range.mp (List.mem_of_find?_eq_some h)

theorem cand_lt {c : Prop} [Decidable c] {n : Nat} (hn : 0 < n) {a b : Nat} {p q : Nat → Bool}
    {o1 o2 : MoveWideOp} :
    (if c then (a, o1, ((List.range n).find? p).getD 0)
      else (b, o2, ((List.range n).find? q).getD 0)).2.2 < n := by
  split
  · exact findD_lt hn p
  · exact findD_lt hn q

theorem emSince_movWide {s0 s : LState} (h : EmSince s0 s) (op : MoveWideOp) (rd : Reg) (b sh : Nat)
    (sz : OperandSize) (hb : b < 2 ^ 16) (hsh : sh < sz.bits / 16) :
    EmSince s0 (s.emit (.movWide op rd ⟨b, sh⟩ sz)) := by
  refine emSince_push h ?_ rfl
  have := size_slices sz hsh
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨hb, this⟩

theorem emSince_movK {s0 s : LState} (h : EmSince s0 s) (rd rn : Reg) (b sh : Nat)
    (sz : OperandSize) (hb : b < 2 ^ 16) (hsh : sh < sz.bits / 16) :
    EmSince s0 (s.emit (.movK rd rn ⟨b, sh⟩ sz)) := by
  refine emSince_push h ?_ rfl
  have := size_slices sz hsh
  simp only [MInst.emitOk, immOkB, MInst.noAlways, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨hb, this⟩

theorem mw_bits_lt (op : MoveWideOp) (x : Nat) :
    (match op with | .movZ => x % 2 ^ 16 | .movN => 2 ^ 16 - 1 - x % 2 ^ 16) < 2 ^ 16 := by
  cases op <;> simp only <;> omega

/-- **`load_constant_full`** emits `movz`/`movn` and `movk`s with in-range immediates. -/
theorem loadConstantFull_em (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat)
    (st : LState) : EmSince st (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine foldl_inv (fun x : Reg × LState × Nat => EmSince st x.2.1) _ _ _ ?_ ?_
  · exact emSince_movWide (emSince_self st) _ _ _ _ _ (mw_bits_lt _ _)
      (cand_lt (size_slices_pos _))
  · intro sh hsh x hx
    refine ite_inv (I := fun x : Reg × LState × Nat => EmSince st x.2.1) (fun _ => hx) fun _ => ?_
    refine ite_inv (I := fun x : Reg × LState × Nat => EmSince st x.2.1) (fun _ => ?_) fun _ => hx
    exact emSince_movK hx _ _ _ _ _ (Nat.mod_lt _ (by decide)) (List.mem_range.mp hsh)

/-! ## Emission of the extern constructors -/

/-- An instruction an extern constructor may emit: one with the emission conditions and no
branch targets, or `emit`'s instruction. -/
def EmE (id : TermId) (args : List V) (m : MInst) : Prop :=
  (m.emitOk = true ∧ m.targets = []) ∨ (id = TId.emit ∧ ∃ i, args = [i] ∧ MInst.ofV i = some m)

/-- The emitted instructions of every successful result meet `EmE`. -/
def EmP (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') →
    ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmE id args m

theorem emE_of_since {id : TermId} {args : List V} {st st' : LState} (h : EmSince st st') :
    ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmE id args m :=
  let ⟨ms, h1, h2⟩ := h
  ⟨ms, h1, fun m hm => .inl (h2 m hm)⟩

theorem callArgs_em (st : LState)
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags))) :
    EmSince st (l.foldl F (#[], st)).2 := by
  refine foldl_inv (fun a : Array (Reg × Reg) × LState => EmSince st a.2) F l (#[], st)
    (emSince_self st) ?_
  intro b _ a ha
  rw [hF]
  split
  · exact ha
  · exact emSince_push ha rfl rfl

/-- **Every extern constructor** emits only instructions with the emission conditions and no
branch targets, and `emit`'s instruction. -/
theorem externCtor_em (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    EmP st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h; exact ⟨[], by simp, by simp⟩
    · cases h
  · apply externCtor_split _ (EmP st)
    all_goals
      intros
      unfold EmP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | (refine ⟨[], ?_, fun _ h => by cases h⟩; simp [LState.fresh]; done)
      | (apply emit_one; exact .inr ⟨rfl, _, rfl, ‹_›⟩)
      | (apply emit_one; exact .inl ⟨rfl, rfl⟩)
      | exact emE_of_since (callArgs_em st _ _ (fun _ _ => rfl))
      | exact emE_of_since (loadConstantFull_em _ _ _ _ st)
      | exact ⟨[], (callOutput_fold st _ _ (fun _ _ => rfl)).1.trans (by simp), by simp⟩

/-! ## Results of the extern constructors -/

theorem land_lt_max (a b : Nat) : Nat.land a (b - 1) < max b 1 := by
  have : Nat.land a (b - 1) ≤ b - 1 := Nat.and_le_right
  omega

/-- `bfm_immr`'s amount, `b ≥ a`. -/
theorem immr_lt1 {x y w : Nat} (_ : Nat.land x (w - 1) ≤ Nat.land y (w - 1)) :
    Nat.land y (w - 1) - Nat.land x (w - 1) < max w 1 := by
  have : Nat.land y (w - 1) ≤ w - 1 := Nat.and_le_right
  omega

/-- `bfm_immr`'s amount, `b < a`. -/
theorem immr_lt2 {x y w : Nat} (h : ¬Nat.land x (w - 1) ≤ Nat.land y (w - 1)) :
    w - (Nat.land x (w - 1) - Nat.land y (w - 1)) < max w 1 := by
  have : Nat.land x (w - 1) ≤ w - 1 := Nat.and_le_right
  omega

theorem bfmImms_lt (ty : CTy) (a : Int) :
    ty.laneBits - 1 - Nat.land (u64 a % 256) (ty.laneBits - 1) < max ty.laneBits 1 := by
  omega

theorem shiftImm?_le {n s : Nat} (h : shiftImm? n = some s) : s ≤ 63 := by
  unfold shiftImm? at h
  split at h
  · cases h; assumption
  · cases h

theorem filter_range_lt {p : Nat → Bool} {b : Nat} (h : (List.range 64).filter p = [b]) : b < 64 := by
  have : b ∈ (List.range 64).filter p := by rw [h]; exact List.mem_singleton_self _
  exact List.mem_range.mp (List.mem_filter.mp this).1

theorem condOfIntCC_ne {k : Nat} {c : Cond} (h : condOfIntCC k = some c) : c ≠ .al ∧ c ≠ .nv := by
  unfold condOfIntCC at h
  split at h <;> cases h <;> decide

theorem condCode_ne {o : Option Nat} {c : Cond} (h : (o >>= condOfIntCC) = some c) :
    c ≠ .al ∧ c ≠ .nv := by
  cases o with
  | none => cases h
  | some k => exact condOfIntCC_ne h

theorem rotr_lt {a b : Nat} (h : a - b < 64) : a - b < min (a + 1) 64 := by omega

theorem mwc_lt {ty : CTy} {x : Nat} (h : ty.bits < 64) :
    (if ty.bits < 64 then x % 2 ^ ty.bits else x) < 2 ^ ty.bits := by
  simp only [h, ↓reduceIte]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- What the extern constructors `actorE` describes precisely return. -/
structure ResE (id : TermId) (args : List V) (v : V) : Prop where
  shImm : id = TId.imm_shift_from_imm64 → ∃ ty n, args = [.ty ty, .int n] ∧
    v = .op (.immShift (Nat.land (u64 n) (ty.bits - 1))) ∧ Nat.land (u64 n) (ty.bits - 1) < 64
  shU8 : id = TId.imm_shift_from_u8 → ∃ n : Int, args = [.int n] ∧ v = .op (.immShift n.toNat) ∧
    n < 64
  uimm5 : id = TId.u8_into_uimm5 → ∃ n : Int, v = .op (.uimm5 n.toNat) ∧ n < 32
  imm12 : id = TId.u8_into_imm12 → ∃ (n : Int) (i : Imm12), v = .op (.imm12 i) ∧
    Imm12.ofNat? n.toNat = some i
  mwc : id = TId.move_wide_const_from_u64 ∨ id = TId.move_wide_const_from_inverted_u64 →
    ∃ ty n x m, args = [.ty ty, .int n] ∧ v = .op (.moveWideConst m) ∧
      MoveWideConst.ofNat? x = some m ∧ (ty.bits < 64 → x < 2 ^ ty.bits)
  sh : id = TId.lshl_from_imm64 ∨ id = TId.ashr_from_u64 →
    ∃ ty n s o, args = [.ty ty, .int n] ∧ v = .op (.shiftOpAndAmt ⟨o, Nat.land s (ty.bits - 1)⟩) ∧
      s ≤ 63 ∧ o ≠ .ror
  extr : id = TId.a64_extr_imm → ∃ ty s o, args = [.ty ty, .op (.immShift s)] ∧
    v = .op (.shiftOpAndAmt ⟨o, s⟩) ∧ o ≠ .ror
  bfm : id = TId.bfm_immr ∨ id = TId.bfm_imms →
    ∃ ty rest n, args = .ty ty :: rest ∧ v = .op (.uimm6 n) ∧ n < max ty.laneBits 1
  neg : id = TId.negate_imm_shift → ∃ ty x n, args = [.ty ty, x] ∧ v = .op (.immShift n) ∧
    n < max ty.bits 1
  rotr : id = TId.rotr_opposite_amount → ∃ ty x n, args = [.ty ty, x] ∧ v = .op (.immShift n) ∧
    n < min (ty.bits + 1) 64
  tbit : id = TId.test_and_compare_bit_const → ∃ (ty : CTy) (x : V) (b : Nat), args = [.ty ty, x] ∧
    v = .int b ∧ b < ty.bits ∧ b < 64
  bits : id = TId.ty_bits → ∃ ty, args = [.ty ty] ∧ v = .int ty.bits
  smask : id = TId.shift_masked_imm → ∃ (ty : CTy) (x : V) (b : Nat), args = [.ty ty, x] ∧ v = .int b ∧
    b < max ty.laneBits 1
  isize : id = TId.imm_size_from_type → v = .int 32 ∨ v = .int 64
  cc : id = TId.cond_code → ∃ c : Cond, v = .data tyCond c.idx [] ∧ c ≠ .al ∧ c ≠ .nv
  inv : id = TId.invert_cond → ∃ x c, args = [x] ∧ x.cond? = some c ∧
    v = .data tyCond c.invert.idx []
  call : id = TId.gen_call_info → ∃ n us ds, v = .op (.callInfo ⟨.sym n, us, ds⟩)
  callInd : id = TId.gen_call_ind_info → ∃ x r rest us ds, args = x :: .reg r :: rest ∧
    v = .op (.callInfo ⟨.reg r, us, ds⟩)
  cast : id = TId.u8_into_u32 ∨ id = TId.u8_into_u64 ∨ id = TId.u16_into_u64 ∨
    id = TId.u32_into_u64 ∨ id = TId.i32_into_i64 → ∃ a, args = [.int a] ∧ v = .int a

/-- `ResE` of every successful result past the type predicates. -/
def ResP (id : TermId) (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') → (∃ q, tyPred id = some q) ∨ ResE id args v

set_option maxHeartbeats 8000000 in
/-- **The results of the extern constructors** `actorE` describes precisely. -/
theorem externCtor_res (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    ResP t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' _
    exact .inl ⟨_, ‹_›⟩
  · apply externCtor_split _ ResP
    all_goals
      intros
      unfold ResP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals try (rename_i heq; simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
                   obtain ⟨_, _, rfl⟩ := heq)
    all_goals refine .inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (intro hx; exfalso; revert hx; decide)
      | skip
    all_goals intro _
    all_goals first
      | exact ⟨_, _, rfl, rfl, ‹_›⟩
      | exact ⟨_, rfl, rfl, ‹_›⟩
      | exact ⟨_, rfl, ‹_›⟩
      | exact ⟨_, _, rfl, ‹_›⟩
      | exact ⟨_, _, _, _, rfl, rfl, ‹_›, mwc_lt⟩
      | exact ⟨_, _, _, _, rfl, rfl, shiftImm?_le ‹_›, by decide⟩
      | exact ⟨_, _, _, rfl, rfl, by decide⟩
      | exact ⟨_, _, _, rfl, rfl, immr_lt1 ‹_›⟩
      | exact ⟨_, _, _, rfl, rfl, immr_lt2 ‹_›⟩
      | exact ⟨_, _, _, rfl, rfl, bfmImms_lt _ _⟩
      | exact ⟨_, _, _, rfl, rfl, land_lt_max _ _⟩
      | exact ⟨_, _, _, rfl, rfl, rotr_lt ‹_›⟩
      | exact ⟨_, _, _, rfl, rfl, ‹_›, filter_range_lt ‹_›⟩
      | exact ⟨_, rfl, rfl⟩
      | exact .inl rfl
      | exact .inr rfl
      | exact ⟨_, rfl, condCode_ne ‹_›⟩
      | exact ⟨_, _, rfl, ‹_›, rfl⟩
      | exact ⟨_, _, _, rfl⟩
      | exact ⟨_, _, _, _, _, rfl, rfl⟩

/-! ## Extractors -/

/-- What `imm12_from_u64` and `u8_from_u64` return. -/
structure ExtE (id : TermId) (fs : List V) : Prop where
  imm12 : id = TId.imm12_from_u64 → ∃ (n : Int) (i : Imm12), fs = [.op (.imm12 i)] ∧
    Imm12.ofNat? (u64 n) = some i
  u8 : id = TId.u8_from_u64 → ∃ i : Int, fs = [.int i] ∧ 0 ≤ i ∧ i < 256

/-- `ExtE` of every successful result. -/
def ExtEP (id : TermId) (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs → ExtE id fs

set_option maxHeartbeats 4000000 in
theorem externExtract_ext (ctx : Ctx) (t : Term) (v : V) (st : LState) (hp : tyPred t.id = none) :
    ExtEP t.id (externExtract ctx t v st) := by
  unfold externExtract
  rw [hp]
  apply externExtract_split _ (fun id _ r => ExtEP id r)
  all_goals
    intros
    unfold ExtEP
    intro fs h
    try dsimp only at h
    repeat' (split at h)
    all_goals try (cases h; done)
  all_goals cases h
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | (intro hx; exfalso; revert hx; decide)
    | skip
  all_goals intro _
  all_goals first
    | exact ⟨_, _, rfl, ‹_›⟩
    | exact ⟨_, rfl, ‹_›⟩

end Backend.Proof.Cov

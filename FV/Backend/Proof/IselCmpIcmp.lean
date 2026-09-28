import FV.Backend.Proof.IselCmpCond

/-!
# Condition producers: `cond_result_invert`, `is_nonzero`, `emit_icmp`, `is_nonzero_cmp`

`CondCode F isem ctx st st' c T`: the code appended between `st` and `st'` (fresh defs), run
from any vreg file holding a frame, leaves a condition `c` (`CondShape`, vregs below `st'`)
whose truth (`CondSem`) is every `b` with `T fr b`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- **Semantic contract of a condition producer.** -/
def CondCode (F : BitVec 64 → Prop) (isem : Sem) (ctx : Ctx) (st st' : LState) (c : V)
    (T : Clif.Frame → Bool → Prop) : Prop :=
  ∃ ms, Frag st st' ms ∧ CondShape c (· < st'.nextVreg) ∧
    ∀ (fr : Clif.Frame) (ρ : Nat → CV) (b : Bool), ValsHeld fr ρ → DFGCons ctx fr → T fr b →
      UsesLo st.nextVreg fr ms ∧ CondShape c (fun u => st.nextVreg ≤ u ∨ (fr.regs u).isSome) ∧
      ∀ w, Runs F isem ms ρ w (fun ρ' _ => CondSem ρ' c b)

theorem CondCode.flag {F : BitVec 64 → Prop} {isem : Sem} {ctx : Ctx} {st st' : LState}
    {ms : List MInst} {T : Clif.Frame → Bool → Prop} {mi : V} {m : MInst} {cond : Cond}
    (hf : Frag st st' ms) (hofv : MInst.ofV mi = some m) (hc : cond ≠ .al ∧ cond ≠ .nv)
    (hd : vdefs m = []) (hu : ∀ u ∈ vuseNums m, u < st'.nextVreg)
    (hsem : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (b : Bool), ValsHeld fr ρ → DFGCons ctx fr →
      T fr b → UsesLo st.nextVreg fr ms ∧
        (∀ u ∈ vuseNums m, st.nextVreg ≤ u ∨ (fr.regs u).isSome) ∧
        ∀ w, Runs F isem ms ρ w (fun ρ' _ => ∃ ps, SetsFlags m ρ' ps ∧ condOn cond.bits ps = b)) :
    CondCode F isem ctx st st' (.data 123 2 [.data 47 1 [mi], .data 96 cond.idx []]) T := by
  refine ⟨ms, hf, .inr (.inr ⟨mi, m, cond, rfl, hofv, hc.1, hc.2, hd, hu⟩), fun fr ρ b hh hdf hT => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsem fr ρ b hh hdf hT
  refine ⟨h1, .inr (.inr ⟨mi, m, cond, rfl, hofv, hc.1, hc.2, hd, h2⟩), fun w => (h3 w).imp ?_⟩
  rintro ρ' _ _ ⟨ps, hps, hb⟩
  exact .inr (.inr ⟨mi, m, cond, ps, rfl, hofv, hps, hb⟩)

theorem CondCode.notZero {F : BitVec 64 → Prop} {isem : Sem} {ctx : Ctx} {st st' : LState}
    {ms : List MInst} {T : Clif.Frame → Bool → Prop} {k i : Nat} {sz : OperandSize}
    (hi : OperandSize.ofIdx? i = some sz) (hf : Frag st st' ms) (hk : k < st'.nextVreg)
    (hsem : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (b : Bool), ValsHeld fr ρ → DFGCons ctx fr →
      T fr b → UsesLo st.nextVreg fr ms ∧ (st.nextVreg ≤ k ∨ (fr.regs k).isSome) ∧
        ∀ w, Runs F isem ms ρ w (fun ρ' _ => (opnd sz (ρ' k) != 0) = b)) :
    CondCode F isem ctx st st' (.data 123 1 [.reg (.vreg k .int), .data 93 i []]) T := by
  refine ⟨ms, hf, .inr (.inl ⟨k, i, sz, rfl, hi, hk⟩), fun fr ρ b hh hdf hT => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsem fr ρ b hh hdf hT
  exact ⟨h1, .inr (.inl ⟨k, i, sz, rfl, hi, h2⟩),
    fun w => (h3 w).imp fun ρ' _ _ hb => .inr (.inl ⟨k, i, sz, rfl, hi, hb⟩)⟩

/-! ## `cond_result_invert` -/

/-- Negation of a condition, on shapes and truth. -/
def CondInv (c c' : V) : Prop :=
  (∀ P, CondShape c P → CondShape c' P) ∧ ∀ ρ b, CondSem ρ c b → CondSem ρ c' (!b)

theorem CondCode.inv {F : BitVec 64 → Prop} {isem : Sem} {ctx : Ctx} {st st' : LState} {c c' : V}
    {T : Clif.Frame → Bool → Prop} (h : CondCode F isem ctx st st' c T) (hi : CondInv c c') :
    CondCode F isem ctx st st' c' (fun fr b => T fr (!b)) := by
  obtain ⟨ms, hf, hs, hr⟩ := h
  refine ⟨ms, hf, hi.1 _ hs, fun fr ρ b hh hd hT => ?_⟩
  obtain ⟨hu, hs', hrun⟩ := hr fr ρ (!b) hh hd hT
  refine ⟨hu, hi.1 _ hs', fun w => (hrun w).imp fun ρ' _ _ h => ?_⟩
  simpa using hi.2 ρ' (!b) h

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

theorem invert_ne {c : Cond} (h : c ≠ .al ∧ c ≠ .nv) : c.invert ≠ .al ∧ c.invert ≠ .nv := by
  cases c <;> simp_all [Cond.invert]

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`cond_result_invert`** (no code): `Zero` ↔ `NotZero`, `Cond` with the inverted
condition. -/
theorem cri_ok {n : Nat} (hn : 40 ≤ n) {c : V} {P : Nat → Prop} (hsh : CondShape c P)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 123 649 [c] s v s') :
    s'.1 = s.1 ∧ CondInv c v := by
  rcases hsh with ⟨k, i, sz, rfl, hi, -⟩ | ⟨k, i, sz, rfl, hi, -⟩ | ⟨mi, m, cond, rfl, hm0, hal, hnv, -⟩ <;>
  isel_split' hp hc h 649 <;>
  (try (isel_refute hp at hm; done)) <;>
  isel_inv' hp [] at hm he
  · refine ⟨fun P h => ?_, fun ρ b h => ?_⟩
    · rcases h with ⟨k', i', sz', e, h1, h2⟩ | ⟨_, _, _, e, _⟩ | ⟨_, _, _, e, _⟩ <;> simp at e
      obtain ⟨rfl, rfl⟩ := e
      exact .inr (.inl ⟨_, _, _, rfl, h1, h2⟩)
    · rcases h with ⟨k', i', sz', e, h1, h2⟩ | ⟨_, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ <;> simp at e
      obtain ⟨rfl, rfl⟩ := e
      refine .inr (.inl ⟨_, _, _, rfl, h1, ?_⟩)
      rw [← h2]; simp [bne]
  · refine ⟨fun P h => ?_, fun ρ b h => ?_⟩
    · rcases h with ⟨_, _, _, e, _⟩ | ⟨k', i', sz', e, h1, h2⟩ | ⟨_, _, _, e, _⟩ <;> simp at e
      obtain ⟨rfl, rfl⟩ := e
      exact .inl ⟨_, _, _, rfl, h1, h2⟩
    · rcases h with ⟨_, _, _, e, _⟩ | ⟨k', i', sz', e, h1, h2⟩ | ⟨_, _, _, _, e, _⟩ <;> simp at e
      obtain ⟨rfl, rfl⟩ := e
      refine .inl ⟨_, _, _, rfl, h1, ?_⟩
      rw [← h2]; simp [bne]
  · rename_i w hw
    rw [V.cond?_data, cond_ofIdx_idx] at hw
    cases hw
    refine ⟨fun P h => ?_, fun ρ b h => ?_⟩
    · rcases h with ⟨_, _, _, e, _⟩ | ⟨_, _, _, e, _⟩ | ⟨mi', m', cond', e, h1, h2, h3, h4, h5⟩ <;>
        simp at e
      obtain ⟨rfl, e2⟩ := e
      rw [← cond_idx_inj e2] at h2 h3
      exact .inr (.inr ⟨_, m', cond.invert, rfl, h1, (invert_ne ⟨h2, h3⟩).1, (invert_ne ⟨h2, h3⟩).2, h4, h5⟩)
    · rcases h with ⟨_, _, _, e, _⟩ | ⟨_, _, _, e, _⟩ | ⟨mi', m', cond', ps, e, h1, h2, h3⟩ <;>
        simp at e
      obtain ⟨rfl, e2⟩ := e
      rw [← cond_idx_inj e2] at h3
      refine .inr (.inr ⟨mi, m', cond.invert, ps, rfl, h1, h2, ?_⟩)
      rw [condOn_invert _ ⟨hal, hnv⟩, h3]


/-! ## `tst_imm`, `is_nonzero` -/

theorem ctor_put_in_regs_iff (ctx : Ctx) (st : LState) (x : Nat) (v : V) (st' : LState) :
    externCtor ctx T.put_in_regs [.value x] st = .ok (v, st') ↔
      ∃ r, ctx.valueReg? x = some r ∧ v = .regs [r] ∧ st' = st := by
  have : externCtor ctx T.put_in_regs [.value x] st = match ctx.valueReg? x with
      | some r => .ok (.regs [r], st)
      | none => .unmodeled s!"put_in_regs v{x}" := rfl
  rw [this]
  cases ctx.valueReg? x <;> simp [eq_comm]

theorem ofV_tst (rd rn : Reg) (imm : ImmLogic) :
    MInst.ofV (.data 58 5 [.data 59 5 [], .data 93 0 [], .reg rd, .reg rn, .op (.immLogic imm)]) =
      some (.aluRRImmLogic .andS .size32 rd rn imm) := rfl

theorem vuseNums_tst (x : Nat) (imm : ImmLogic) :
    vuseNums (.aluRRImmLogic .andS .size32 .xzr (.vreg x .int) imm) = [x] := rfl

theorem immLogic_255 : ImmLogic.ofNat? 255 .size32 = some ⟨255, .size32⟩ := by decide

theorem setsFlags_tst255 (x : Nat) (ρ : Nat → CV) :
    SetsFlags (.aluRRImmLogic .andS .size32 .xzr (.vreg x .int) ⟨255, .size32⟩) ρ
      (andsFlags (opnd .size32 (ρ x) &&& BitVec.ofNat OperandSize.size32.bits 255)) := by
  refine ⟨_, rfl, rfl, fun w => ?_⟩
  simp only [ispec, immLogic_255, ↓reduceIte, defOut]
  rfl

theorem vholds_ty {ctx : Ctx} {fr : Clif.Frame} (hd : DFGCons ctx fr) {x : Nat} {t : CTy} {v : Clif.Val}
    (ht : ctx.valueType? x = some t) (hv : fr.regs x = some v) : CTy.ofClif v.ty = t :=
  hd.2 x t v ht hv

theorem opnd64_vholds {b : BitVec 64} {a : CV} (h : VHolds ⟨.i64, b⟩ a) : opnd .size64 a = b := by
  simp only [VHolds] at h; simp only [opnd, lo64, OperandSize.bits]
  rw [← h]; simp [BitVec.setWidth_setWidth_of_le]; rfl

theorem truthy_setWidth32 {w : Nat} (hw : w ≤ 32) (b : BitVec w) :
    (b.setWidth 32 != 0) = Clif.Sem.truthy b := by
  have h1 : b.setWidth 32 = 0 ↔ b = 0 := by
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) hw))] at this
      simpa using this
    · rintro rfl; simp
  simp only [Clif.Sem.truthy, bne]
  congr 1
  exact Bool.eq_iff_iff.mpr (by simpa using h1)

theorem truthy_i8 (b : BitVec 8) (a : CV) (h : VHolds ⟨.i8, b⟩ a) :
    condOn Cond.ne.bits (andsFlags (opnd .size32 a &&& BitVec.ofNat OperandSize.size32.bits 255)) =
      Clif.Sem.truthy b := by
  show condOn Cond.ne.bits (andsFlags (((lo64 a).setWidth 32 : BitVec 32) &&& BitVec.ofNat 32 255)) = _
  rw [condOn_tst255]
  simp only [VHolds, Clif.Ty.width] at h
  simp only [Clif.Sem.truthy, ← h, lo64]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide)]

theorem ctor_u64_into_imm_logic_255 (ctx : Ctx) (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.u64_into_imm_logic [.ty (.int 32), .int 255] st = .ok (v, st') ↔
      v = .op (.immLogic ⟨255, .size32⟩) ∧ st' = st := by
  have : externCtor ctx T.u64_into_imm_logic [.ty (.int 32), .int 255] st =
    .ok (.op (.immLogic ⟨255, .size32⟩), st) := rfl
  rw [this]; simp [eq_comm]

set_option maxHeartbeats 2000000 in
include hp hc in
theorem tst_imm_ok {n : Nat} (hn : 40 ≤ n) {t : CTy} {a b : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 47 424 [.ty t, a, b] s v s') :
    s'.1 = s.1 ∧ ∃ sv, ((t.bits ≤ 32 ∧ sv = .data 93 0 []) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ sv = .data 93 1 [])) ∧
      v = .data 47 1 [.data 58 5 [.data 59 5 [], sv, .reg .xzr, a, b]] := by
  isel_split' hp hc h 424
  isel_inv' hp [] at hm he
  isel_call hp hc [operand_size_ok]
  exact ⟨‹_›, ‹_›⟩

set_option maxHeartbeats 4000000 in
include hp hc in
theorem is_nonzero_ok {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {f : Clif.Function}
    (hctx : CtxInv f ctx) {n : Nat} (hn : 100 ≤ n) {x : Nat} {s s' : LState × Array RuleId} {c : V}
    (hvb : ValsBelow ctx s.1) (h : ApplyInternal p (sem ctx) cfg n 123 651 [.value x] s c s') :
    CondCode F isem ctx s.1 s'.1 c (fun fr b => ∃ v, fr.regs x = some v ∧ b = Clif.Sem.truthy v.bits) := by
  isel_split' hp hc h 651
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [ctor_u64_into_imm_logic_255, ctor_put_in_regs_iff, Int.toNat_one,
    Int.toNat_zero, List.getElem?_cons_succ, List.getElem?_nil] at hm
  all_goals try (isel_opcode_absurd hctx; done)
  all_goals isel_call hp hc [tst_imm_ok, zext32_ok]
  · -- I8: `tst x, #255` then `ne`
    have hT : ctx.valueType? x = some (.int 8) := ‹_›
    have hx : ctx.valueReg? x = some _ := ‹_›
    have hrx := hctx.valueReg x _ hx; subst hrx
    rcases ‹(CTy.int 32).bits ≤ 32 ∧ _ ∨ _› with ⟨-, rfl⟩ | ⟨h, -⟩
    · refine CondCode.flag (ms := []) (cond := .ne) (Frag.nil _) (ofV_tst _ _ _) (by decide) rfl ?_ ?_
      · intro u hu; rw [vuseNums_tst, List.mem_singleton] at hu; subst hu; exact vreg_lt hvb hx
      · rintro fr ρ b hh hdf ⟨v, hv, rfl⟩
        refine ⟨UsesLo.nil _ _, fun u hu => ?_, fun w => Runs.nil ⟨_, setsFlags_tst255 x ρ, ?_⟩⟩
        · rw [vuseNums_tst, List.mem_singleton] at hu; subst hu; exact .inr (by simp [hv])
        · have ht := vholds_ty hdf hT hv
          obtain ⟨vty, vb⟩ := v
          cases vty <;> simp [CTy.ofClif] at ht
          exact truthy_i8 vb _ (hh x _ hv)
    · simp [CTy.bits] at h
  · -- I64: `NotZero x, 64`
    have hT : ctx.valueType? x = some (.int 64) := ‹_›
    have hx : ctx.valueReg? x = some _ := ‹_›
    have hrx := hctx.valueReg x _ hx; subst hrx
    refine CondCode.notZero (ms := []) (i := 1) (sz := .size64) rfl (Frag.nil _) (vreg_lt hvb hx) ?_
    rintro fr ρ b hh hdf ⟨v, hv, rfl⟩
    refine ⟨UsesLo.nil _ _, .inr (by simp [hv]), fun w => Runs.nil ?_⟩
    have ht := vholds_ty hdf hT hv
    obtain ⟨vty, vb⟩ := v
    cases vty <;> simp [CTy.ofClif] at ht
    rw [opnd64_vholds (hh x _ hv)]; rfl
  · -- fits_in_32: `NotZero (zext32 x), 32`
    have hT : ctx.valueType? x = some _ := ‹_›
    have hb := ‹CTy.bits _ ≤ 32›
    have hz : ExtOut ctx x false 32 [.int 32, .int 64] _ _ _ := ‹_›
    obtain ⟨k, ms, rfl, hf, hk, hkx, hrun⟩ := ExtOut.sem hR hctx hvb (.inl rfl)
      (by simp) (fun _ => by simp) hz
    refine CondCode.notZero (i := 0) (sz := .size32) rfl hf hk ?_
    rintro fr ρ b hh hdf ⟨v, hv, rfl⟩
    obtain ⟨hu, hr⟩ := hrun fr ρ v (hh x v hv) hdf hv
    refine ⟨hu, ?_, fun w => (hr w).imp fun ρ' _ _ ⟨h1, h2⟩ => ?_⟩
    · rcases hkx with h | rfl
      · exact .inl h
      · exact .inr (by simp [hv])
    · have ht := vholds_ty hdf hT hv
      have hw : v.ty.width ≤ 32 := by rw [← ofClif_bits, ht]; exact hb
      rw [opnd32_setWidth, ← BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
      have := h2 hw
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [show (ρ' k).setWidth 64 = lo64 (ρ' k) from rfl, this]
      exact truthy_setWidth32 hw _


end

end Backend.Proof


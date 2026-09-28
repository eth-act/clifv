import FV.Backend.Proof.IselCmpVec
import FV.Backend.Proof.IselTermsImm

/-!
# Family C: division and remainder (`udiv`/`sdiv`/`urem`/`srem`)
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ctor_trap_divz_iff (ctx : Ctx) (st st' : LState) (v : V) :
    externCtor ctx T.trap_code_division_by_zero [] st = .ok (v, st') ↔
      v = .op (.trapCode .intDivz) ∧ st' = st := by
  have e : externCtor ctx T.trap_code_division_by_zero [] st = .ok (.op (.trapCode .intDivz), st) := rfl
  rw [e]; simp [eq_comm]

theorem ctor_trap_ovf_iff (ctx : Ctx) (st st' : LState) (v : V) :
    externCtor ctx T.trap_code_integer_overflow [] st = .ok (v, st') ↔
      v = .op (.trapCode .intOvf) ∧ st' = st := by
  have e : externCtor ctx T.trap_code_integer_overflow [] st = .ok (.op (.trapCode .intOvf), st) := rfl
  rw [e]; simp [eq_comm]

theorem ctor_cond_br_zero_iff (ctx : Ctx) (st st' : LState) (r s v : V) :
    externCtor ctx T.cond_br_zero [r, s] st = .ok (v, st') ↔
      v = .data tyCondBrKind VIdx.CondBrKind.Zero [r, s] ∧ st' = st := by
  have e : externCtor ctx T.cond_br_zero [r, s] st =
    .ok (.data tyCondBrKind VIdx.CondBrKind.Zero [r, s], st) := rfl
  rw [e]; simp [eq_comm]

theorem ofV_trapIf_zero (r : Reg) {i : Nat} {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz)
    (c : Clif.TrapCode) :
    MInst.ofV (.data 58 120 [.data tyCondBrKind VIdx.CondBrKind.Zero [.reg r, .data 93 i []],
      .op (.trapCode c)]) = some (.trapIf (.zero r sz) c) := by
  match i, hi with
  | 0, hi => cases hi; rfl
  | 1, hi => cases hi; rfl

theorem ext_nonzero_u64_iff (ctx : Ctx) (st : LState) (i : Int) (fs : List V) :
    externExtract ctx T.nonzero_u64_from_imm64 (.int i) st = .ok fs ↔ i ≠ 0 ∧ fs = [.int (u64 i)] := by
  have e : externExtract ctx T.nonzero_u64_from_imm64 (.int i) st =
    (if i == 0 then .fail else .ok [.int (u64 i)]) := rfl
  rw [e]
  cases hb : (i == 0)
  · have hi : i ≠ 0 := by simpa using hb
    simp only [Bool.false_eq_true, ↓reduceIte, ExtResult.ok.injEq]
    exact ⟨fun h => ⟨hi, h.symm⟩, fun h => h.2.symm⟩
  · have hi : i = 0 := by simpa using hb
    refine ⟨fun h => ?_, fun h => absurd hi h.1⟩
    simp at h

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`trap_if_zero_divisor`** (rule 3838): `trapIf (zero r sz) int_divz`, returns `r`. -/
theorem trap_if_zero_divisor_ok {n : Nat} (hn : 40 ≤ n) {r : Reg} {i : Nat} {sz : OperandSize}
    (hi : OperandSize.ofIdx? i = some sz) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 559 [.reg r, .data 93 i []] s v s') :
    v = .reg r ∧ s'.1 = s.1.emit (.trapIf (.zero r sz) .intDivz) := by
  isel_split' hp hc h 559
  all_goals isel_inv' hp [ctor_trap_divz_iff, ctor_cond_br_zero_iff] at hm he
  obtain ⟨h1⟩ : Nonempty (MInst.ofV _ = some _) := ⟨‹_›⟩
  rw [ofV_trapIf_zero r hi] at h1
  cases h1
  first | exact ⟨rfl, rfl⟩ | rfl

include hp hc in
/-- `imm_ok` on an `ApplyInternal` hypothesis. -/
theorem imm_ok_ai {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {e : Nat} (he : e = 0 ∨ e = 1) {i : Int} {n : Nat}
    (hn : 60 ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 553 [.ty (.int w), .data 122 e [], .int i] s v s') :
    ImmOut F isem w e (u64 i) s.1 s'.1 v := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 39 := ⟨n - 39, by omega⟩
  exact imm_ok hp ctx hc hR hw he (st := s.1) (tr := s.2) (n := n') h

theorem ExtOut.isReg {ctx : Ctx} {x : Nat} {sg : Bool} {toB : Nat} {pass : List CTy} {s s' : LState}
    {v : V} (h : ExtOut ctx x sg toB pass s s' v) : ∃ r, v = .reg r := by
  obtain ⟨t, -, rx, -, ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩⟩ := h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`put_nonzero_in_reg`** (`lower.isle:1097–1110`): a nonzero `iconst` divisor as an
immediate (`imm`, no check), or the divisor in a register (64-bit: as is; narrower: extended to
32 bits) followed by `trapIf (zero r) int_divz`. `e`: `ImmExtend` (0 sign, 1 zero). -/
theorem put_nonzero_in_reg_ok {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem)
    {f : Clif.Function} (hctx : CtxInv f ctx) {n : Nat} (hn : 100 ≤ n) {y e w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (he : e = 0 ∨ e = 1) {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 698 [.value y, .data 125 e [], .ty (.int w)] s v s') :
    (∃ j info ity imm, ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
        info.clif = some (.iconst ity imm) ∧ eTy ity = true ∧ imm64OfIconst ity imm ≠ 0 ∧
        ImmOut F isem w e (u64 (imm64OfIconst ity imm)) s.1 s'.1 v) ∨
    (w = 64 ∧ ∃ ry, ctx.valueReg? y = some ry ∧ v = .reg ry ∧
        s'.1 = s.1.emit (.trapIf (.zero ry .size64) .intDivz)) ∨
    (w ≤ 32 ∧ ∃ r s2, ExtOut ctx y (e == 0) 32 [.int 32, .int 64] s.1 s2 (.reg r) ∧ v = .reg r ∧
        s'.1 = s2.emit (.trapIf (.zero r .size32) .intDivz)) := by
  rcases hw with rfl | rfl | rfl | rfl <;> rcases he with rfl | rfl <;>
  isel_split' hp hc h 698 <;>
  (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  all_goals try (obtain ⟨hx⟩ : Nonempty (CTy.int _ = CTy.int 64) := ⟨‹_›⟩; cases hx; done)
  all_goals try (have hx : (CTy.int 64).bits ≤ 32 := by assumption
                 exact absurd hx (by decide))
  -- `iconst` divisor: `imm`
  all_goals try (
    obtain ⟨hnz⟩ : Nonempty (externExtract ctx T.nonzero_u64_from_imm64 _ _ = _) := ⟨‹_›⟩
    obtain ⟨hj⟩ : Nonempty (ctx.defInst? y = some _) := ⟨‹_›⟩
    obtain ⟨hi⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
    obtain ⟨hd⟩ : Nonempty (V.data 152 35 _ = _) := ⟨‹_›⟩
    obtain ⟨h553⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 553 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨ity, imm, rfl, hety, hcl⟩ := iconst_data_inv hctx hj hi hd
    rw [ext_nonzero_u64_iff] at hnz
    obtain ⟨hne, hfs⟩ := hnz
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    have hI := imm_ok_ai hp hc hR (by decide) (by decide) (by omega) h553
    rw [u64_ofNat (u64_lt' _)] at hI
    exact .inl ⟨_, hj, _, hi, _, _, hcl, hety, hne, hI⟩)
  all_goals
    obtain ⟨h559⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 559 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨h305⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 93 305 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨hs5, hsz⟩ := operand_size_ok hp hc (by omega) h305
    rcases hsz with ⟨hb, rfl⟩ | ⟨hb, -, rfl⟩ <;> (try (exact absurd hb (by decide)))
  -- 64-bit divisor register
  all_goals try (
    obtain ⟨hr, hs'⟩ := trap_if_zero_divisor_ok hp hc (h := h559) (hn := by omega) (hi := rfl)
    subst hr
    simp only at hs' hs5
    rw [hs5] at hs'
    exact .inr (.inl ⟨_, by assumption, rfl, hs'⟩))
  -- 64-bit divisor register
  -- narrower divisor: extended to 32 bits
  all_goals
    first
      | obtain ⟨h55⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 555 _ _ _ _) := ⟨‹_›⟩
        have hE := sext32_ok hp hc (hn := by omega) h55
      | obtain ⟨h55⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 556 _ _ _ _) := ⟨‹_›⟩
        have hE := zext32_ok hp hc (hn := by omega) h55
    obtain ⟨r, rfl⟩ := hE.isReg
    obtain ⟨hr, hs'⟩ := trap_if_zero_divisor_ok hp hc (h := h559) (hn := by omega) (hi := rfl)
    subst hr
    simp only at hs'
    rw [hs5] at hs'
    exact .inr (.inr ⟨r, _, hE, rfl, hs'⟩)
end

/-! ## Division operands and the zero check -/

/-- The register value `a` is `b` as a division operand: extended to 32 bits (`sg`: signed) when
`b` is at most 32 bits wide, the low 64 bits otherwise. -/
def DivOpnd (sg : Bool) {n : Nat} (b : BitVec n) (a : CV) : Prop :=
  if n ≤ 32 then (lo64 a).setWidth 32 = (if sg then b.signExtend 32 else b.setWidth 32)
  else lo64 a = b.setWidth 64

/-- The code halts at a trap instruction with code `c`. -/
def TrapRun (isem : Sem) (ms : List MInst) (ρ : Nat → CV) (w : Arm.ArmState) (c : Clif.TrapCode) :
    Prop :=
  ∃ k i ops ρ₁ w₁ outs w₂, seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧
    trapCode? i = some c

theorem ext32_eq_zero {n : Nat} (hn : n ≤ 32) (sg : Bool) (b : BitVec n) :
    ((if sg then b.signExtend 32 else b.setWidth 32) = 0#32) ↔ b = 0#n := by
  cases sg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) hn))] at this
      simpa using this
    · rintro rfl; simp
  · simp only [↓reduceIte]
    constructor
    · intro h
      apply BitVec.eq_of_toInt_eq
      have := congrArg BitVec.toInt h
      rw [BitVec.toInt_signExtend_of_le hn] at this
      simpa using this
    · rintro rfl
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_signExtend_of_le hn]; simp

theorem setWidth64_eq_zero {n : Nat} (hn : n ≤ 64) (b : BitVec n) : b.setWidth 64 = 0#64 ↔ b = 0#n := by
  constructor
  · intro h'
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] at this
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) hn))] at this
    simpa using this
  · rintro rfl; simp

theorem DivOpnd.zero_iff {sg : Bool} {n : Nat} (hn : n ≤ 64) {b : BitVec n} {a : CV}
    (h : DivOpnd sg b a) (w : Arm.ArmState) (r : Reg) :
    condBrHolds (.zero r (szOf n)) [a] w = (b == 0#n) := by
  unfold DivOpnd at h
  unfold szOf
  have e32 : (OperandSize.size32 == OperandSize.size64) = false := rfl
  have e64 : (OperandSize.size64 == OperandSize.size64) = true := rfl
  by_cases h32 : n ≤ 32
  · simp only [h32, ↓reduceIte] at h ⊢
    simp only [condBrHolds, OperandSize.is64, e32, Bool.false_eq_true, ↓reduceIte]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h]
    exact ext32_eq_zero h32 sg b
  · simp only [h32, ↓reduceIte] at h ⊢
    simp only [condBrHolds, OperandSize.is64, e64, ↓reduceIte]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h]
    exact setWidth64_eq_zero hn b

theorem operands_trapIf_zero (k : Nat) (sz : OperandSize) (c : Clif.TrapCode) :
    (MInst.trapIf (.zero (.vreg k .int) sz) c).operands = .ok #[⟨k, .int, .use, .early, .reg⟩] := rfl

theorem vdefs_trapIf_zero (k : Nat) (sz : OperandSize) (c : Clif.TrapCode) :
    vdefs (MInst.trapIf (.zero (.vreg k .int) sz) c) = [] := rfl

theorem vuseNums_trapIf_zero (k : Nat) (sz : OperandSize) (c : Clif.TrapCode) :
    vuseNums (MInst.trapIf (.zero (.vreg k .int) sz) c) = [k] := rfl

theorem runs_trapIf_zero_fall {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) (k : Nat)
    (sz : OperandSize) (c : Clif.TrapCode) (ρ : Nat → CV) (w : Arm.ArmState)
    (h : condBrHolds (.zero (.vreg k .int) sz) [ρ k] w = false) :
    Runs F isem [.trapIf (.zero (.vreg k .int) sz) c] ρ w (fun ρ' _ => ρ' = ρ) := by
  refine Runs.one hR (operands_trapIf_zero k sz c) (outs := []) (w' := w) ?_ rfl (SameWorldNF.refl F w)
    fun _ _ => vdefUpd_nil _ _
  show some ([], w, if condBrHolds (.zero (.vreg k .int) sz) [ρ k] w then Ctl.halt else Ctl.next) = _
  rw [h]; rfl

theorem trapRun_trapIf_zero {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) (k : Nat)
    (sz : OperandSize) (c : Clif.TrapCode) (ρ : Nat → CV) (w : Arm.ArmState)
    (h : condBrHolds (.zero (.vreg k .int) sz) [ρ k] w = true) :
    TrapRun isem [.trapIf (.zero (.vreg k .int) sz) c] ρ w c := by
  have hs : ispec (.trapIf (.zero (.vreg k .int) sz) c) [ρ k] w = some ([], w, .halt) := by
    show some ([], w, if condBrHolds (.zero (.vreg k .int) sz) [ρ k] w then Ctl.halt else Ctl.next) = _
    rw [h]; rfl
  obtain ⟨w'', hr⟩ := seqRun_one_halt (F := F) hR (operands_trapIf_zero k sz c) (ρ := ρ) hs rfl
  exact ⟨_, _, _, _, _, _, _, hr, rfl⟩

theorem TrapRun.prefix {F : BitVec 64 → Prop} {isem : Sem} {ms1 ms2 : List MInst} {ρ : Nat → CV}
    {w : Arm.ArmState} {c : Clif.TrapCode} {P : (Nat → CV) → Arm.ArmState → Prop}
    (h1 : Runs F isem ms1 ρ w P) (h2 : ∀ ρ1 w1, P ρ1 w1 → TrapRun isem ms2 ρ1 w1 c) :
    TrapRun isem (ms1 ++ ms2) ρ w c := by
  obtain ⟨ρ1, w1, hr1, -, hp1⟩ := h1
  obtain ⟨k, i, ops, ρ₁, w₁, outs, w₂, hr2, hc⟩ := h2 ρ1 w1 hp1
  exact ⟨_, i, ops, ρ₁, w₁, outs, w₂, seqRun_append_fall_stop isem hr1 hr2, hc⟩

theorem TrapRun.append {isem : Sem} {ms1 ms2 : List MInst} {ρ : Nat → CV}
    {w : Arm.ArmState} {c : Clif.TrapCode} (h : TrapRun isem ms1 ρ w c) :
    TrapRun isem (ms1 ++ ms2) ρ w c := by
  obtain ⟨k, i, ops, ρ₁, w₁, outs, w₂, hr, hc⟩ := h
  exact ⟨k, i, ops, ρ₁, w₁, outs, w₂, seqRun_append_stop isem hr, hc⟩

/-! ## An `iconst` divisor as an immediate -/

theorem sextFrom_toInt {w : Nat} (hw : 0 < w) (b : BitVec w) : sextFrom w (b.toNat : Int) = b.toInt := by
  unfold sextFrom
  have hlt := b.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  have h2 : (2:Int) ^ w = ((2 ^ w : Nat) : Int) := by norm_cast
  have h3 : (2:Int) ^ (w - 1) * 2 = ((2 ^ w : Nat) : Int) := by
    rw [← h2, ← Int.pow_succ]; congr 1; omega
  simp only [show w ≠ 0 by omega, ↓reduceIte]
  rw [h2]
  have hm : (b.toNat : Int) % ((2 ^ w : Nat) : Int) = b.toNat := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rw [hm]
  split <;> split <;> omega
theorem ofNat_u64_mod32 (i : Int) : BitVec.ofNat 32 (u64 i % 2 ^ 32) = BitVec.ofInt 32 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt, u64]
  omega

theorem imm_divOpnd {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) {e : Nat} (he : e = 0 ∨ e = 1)
    (b : BitVec n) {X : Nat} (h1 : X % 2 ^ n = b.toNat % 2 ^ n)
    (h2 : n ≠ 32 ∨ e = 0 ∨ b.toNat < 2 ^ 32 → X = immVal n (e == 0) b.toNat) {a : CV}
    (ha : lo64 a = BitVec.ofNat 64 X) : DivOpnd (e == 0) b a := by
  unfold DivOpnd
  rw [ha]
  rcases hn with rfl | rfl | rfl | rfl
  · have hX := h2 (.inl (by decide))
    simp only [show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
    rcases he with rfl | rfl
    · simp only [beq_self_eq_true, ↓reduceIte]
      rw [hX]
      simp only [immVal, szOf, show ((0 : Nat) == 0) = true by decide, show ((1 : Nat) == 0) = false by decide, show (8 : Nat) ≤ 32 by decide, ↓reduceIte, lcfValue, mask64,
        Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide : 2 ^ 8 < 2 ^ 64)), show (8 : Nat) < 32 by decide]
      rw [BitVec.setWidth_ofNat_of_le (by decide), ofNat_u64_mod32, sextFrom_toInt (by decide)]
      rfl
    · simp only [show ((1 : Nat) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte]
      rw [hX]
      simp only [immVal, szOf, show ((0 : Nat) == 0) = true by decide, show ((1 : Nat) == 0) = false by decide, show (8 : Nat) ≤ 32 by decide, ↓reduceIte, lcfValue, mask64,
        Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide : 2 ^ 8 < 2 ^ 64)), show (8 : Nat) < 32 by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := b.isLt
      omega
  · have hX := h2 (.inl (by decide))
    simp only [show (16 : Nat) ≤ 32 by decide, ↓reduceIte]
    rcases he with rfl | rfl
    · simp only [beq_self_eq_true, ↓reduceIte]
      rw [hX]
      simp only [immVal, szOf, show ((0 : Nat) == 0) = true by decide, show ((1 : Nat) == 0) = false by decide, show (16 : Nat) ≤ 32 by decide, ↓reduceIte, lcfValue, mask64,
        Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide : 2 ^ 16 < 2 ^ 64)), show (16 : Nat) < 32 by decide]
      rw [BitVec.setWidth_ofNat_of_le (by decide), ofNat_u64_mod32, sextFrom_toInt (by decide)]
      rfl
    · simp only [show ((1 : Nat) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte]
      rw [hX]
      simp only [immVal, szOf, show ((0 : Nat) == 0) = true by decide, show ((1 : Nat) == 0) = false by decide, show (16 : Nat) ≤ 32 by decide, ↓reduceIte, lcfValue, mask64,
        Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide : 2 ^ 16 < 2 ^ 64)), show (16 : Nat) < 32 by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := b.isLt
      omega
  · simp only [show (32 : Nat) ≤ 32 by decide, ↓reduceIte]
    have hs : b.signExtend 32 = b := by
      apply BitVec.eq_of_toInt_eq; rw [BitVec.toInt_signExtend_of_le (by decide)]
    have hz : b.setWidth 32 = b := BitVec.setWidth_eq b
    rw [hs, hz]
    have hb : (if (e == 0) = true then b else b) = b := by split <;> rfl
    rw [hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := b.isLt
    rw [Nat.mod_eq_of_lt this] at h1
    omega
  · simp only [show ¬ (64 : Nat) ≤ 32 by decide, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := b.isLt
    rw [Nat.mod_eq_of_lt this] at h1
    omega

theorem prun_runs {F : BitVec 64 → Prop} {isem : Sem} {ms : List MInst} {ρ ρ' : Nat → CV}
    (h : PRun F isem ms ρ ρ') (w : Arm.ArmState) {P : (Nat → CV) → Arm.ArmState → Prop}
    (hP : ∀ w', P ρ' w') : Runs F isem ms ρ w P := by
  obtain ⟨w', hr, hw⟩ := h w
  exact ⟨ρ', w', hr, ⟨fun f hf _ => hw.1 f hf, hw.2.1, hw.2.2⟩, hP w'⟩

theorem lo64_ofX' (r : BitVec 64) : lo64 (ofX r) = r := by
  simp only [lo64, ofX, BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by decide), BitVec.setWidth_eq]

/-- The register an `imm` defines is below the state after it (else the run would not change
it, and it could not hold the constant from every start). -/
theorem immOut_lt {F : BitVec 64 → Prop} {isem : Sem} {w e c : Nat} (hw : 0 < w) (hw64 : w ≤ 64)
    (w0 : Arm.ArmState)
    {st st' : LState} {v : V} (h : ImmOut F isem w e c st st' v) :
    ∃ d ms, v = .reg (.vreg d .int) ∧ CodeShape st st' ms d st.nextVreg ∧ d < st'.nextVreg ∧
      ∀ ρ, ∃ ρ' X, PRun F isem ms ρ ρ' ∧ lo64 (ρ' d) = BitVec.ofNat 64 X ∧ X % 2 ^ w = c % 2 ^ w ∧
        (w ≠ 32 ∨ e = 0 ∨ c < 2 ^ 32 → X = immVal w (e == 0) c) := by
  obtain ⟨ms, d, rfl, hsh, hrun⟩ := h
  refine ⟨d, ms, rfl, hsh, ?_, hrun⟩
  refine Nat.lt_of_not_le fun hle => ?_
  obtain ⟨ρ', X, hp, hX, hXc, -⟩ := hrun (fun _ => ofX (BitVec.ofNat 64 (c + 1)))
  obtain ⟨w', hr, -⟩ := hp w0
  have hfr := seqRun_frame isem hr d fun m hm hd => by have := hsh.defs m hm d hd; omega
  rw [hfr, lo64_ofX'] at hX
  have := congrArg BitVec.toNat hX
  simp only [BitVec.toNat_ofNat] at this
  have hpw : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw64
  have h1 : (c + 1) % 2 ^ w = X % 2 ^ w := by
    rw [← Nat.mod_mod_of_dvd (c + 1) hpw, ← Nat.mod_mod_of_dvd X hpw, this]
  rw [hXc] at h1
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
  have h3 := Nat.sub_mod_eq_zero_of_mod_eq h1
  rw [show c + 1 - c = 1 by omega, Nat.mod_eq_of_lt (by omega)] at h3
  cases h3

/-! ## Meaning of `put_nonzero_in_reg` -/

theorem imm64OfIconst_ne_zero {ty : Clif.Ty} {imm : BitVec ty.width} (h : imm64OfIconst ty imm ≠ 0) :
    imm ≠ 0#ty.width := by
  rintro rfl
  apply h
  unfold imm64OfIconst
  split <;> simp

/-- **Semantic contract of `put_nonzero_in_reg`**: the returned vreg `k` holds the divisor as a
division operand, after a check that halts with `int_divz` on a zero divisor. -/
theorem divisor_sem {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInv f ctx) {y e w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (he : e = 0 ∨ e = 1) {s s' : LState} {v : V} (hvb : ValsBelow ctx s)
    (hD : (∃ j info ity imm, ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
        info.clif = some (.iconst ity imm) ∧ eTy ity = true ∧ imm64OfIconst ity imm ≠ 0 ∧
        ImmOut F isem w e (u64 (imm64OfIconst ity imm)) s s' v) ∨
      (w = 64 ∧ ∃ ry, ctx.valueReg? y = some ry ∧ v = .reg ry ∧
        s' = s.emit (.trapIf (.zero ry .size64) .intDivz)) ∨
      (w ≤ 32 ∧ ∃ r s2, ExtOut ctx y (e == 0) 32 [.int 32, .int 64] s s2 (.reg r) ∧ v = .reg r ∧
        s' = s2.emit (.trapIf (.zero r .size32) .intDivz))) :
    ∃ k ms, v = .reg (.vreg k .int) ∧ Frag s s' ms ∧ (s.nextVreg ≤ k ∨ k = y) ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (ty : Clif.Ty) (b : BitVec ty.width), ty.width = w →
        VHolds ⟨ty, b⟩ (ρ y) → DFGCons ctx fr → fr.regs y = some ⟨ty, b⟩ →
        UsesLo s.nextVreg fr ms ∧ ∀ wd, k < s'.nextVreg ∧
          (b = 0#ty.width → TrapRun isem ms ρ wd .intDivz) ∧
          (b ≠ 0#ty.width → Runs F isem ms ρ wd (fun ρ' _ => DivOpnd (e == 0) b (ρ' k))) := by
  rcases hD with ⟨j, info, ity, imm, hj, hi, hcl, hety, hne, hI⟩ | ⟨rfl, ry, hry, rfl, rfl⟩ |
    ⟨hw32, r, s2, hE, rfl, rfl⟩
  · -- `iconst`: `imm`, no check
    obtain ⟨ms, d, rfl, hsh, hrun⟩ := hI
    refine ⟨d, ms, rfl, ⟨hsh.emitted, hsh.mono, hsh.defs⟩, .inl hsh.res,
      fun fr ρ ty b htw hh hdf hyv => ⟨?_, fun wd => ?_⟩⟩
    · intro m hm u hu
      rcases hsh.uses m hm u hu with h | h
      · exact .inl h
      · exact .inl (by omega)
    have hv := iconst_val hdf hj hi hcl hyv
    simp only [Clif.Val.mk.injEq] at hv
    obtain ⟨rfl, hb⟩ := hv
    have hb' : b = imm := eq_of_heq hb
    subst hb'
    have hw64 := eTy_width hety
    obtain ⟨d', ms', he', hsh', hlt, hrun'⟩ := immOut_lt (by omega) (by omega) wd ⟨ms, d, rfl, hsh, hrun⟩
    cases he'
    refine ⟨hlt, fun h0 => absurd h0 (imm64OfIconst_ne_zero hne), fun _ => ?_⟩
    obtain ⟨ρ', X, hp, hX, hXc, hXv⟩ := hrun ρ
    refine prun_runs hp wd fun _ => ?_
    rw [u64_imm64OfIconst hw64] at hXc hXv
    subst htw
    exact imm_divOpnd hw he b hXc hXv hX
  · -- 64-bit register, `trapIf (zero y)`
    have hry' := hctx.valueReg y ry hry
    subst hry'
    have hylt := hvb y _ hry
    refine ⟨y, _, rfl, Frag.emit_nodef s (vdefs_trapIf_zero _ _ _), .inr rfl,
      fun fr ρ ty b htw hh hdf hyv => ⟨?_, fun wd => ⟨by simpa [LState.emit] using hylt, ?_⟩⟩⟩
    · intro m hm u hu
      simp only [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_trapIf_zero, List.mem_singleton] at hu
      subst hu
      exact .inr (by simp [hyv])
    have hd : DivOpnd (e == 0) b (ρ y) := by
      have hv := hh
      cases ty <;> simp [Clif.Ty.width] at htw
      simp only [VHolds, Clif.Ty.width] at hv
      unfold DivOpnd
      simp only [Clif.Ty.width, show ¬ (64 : Nat) ≤ 32 by decide, ↓reduceIte, lo64, BitVec.setWidth_eq]
      exact hv
    have hz := hd.zero_iff (by omega) wd (.vreg y .int)
    rw [show szOf ty.width = .size64 by rw [htw]; rfl] at hz
    refine ⟨fun h0 => trapRun_trapIf_zero hR _ _ _ ρ wd (by rw [hz, h0]; simp), fun h0 => ?_⟩
    refine (runs_trapIf_zero_fall hR _ _ _ ρ wd (by rw [hz]; simpa using h0)).imp fun ρ' _ _ e => ?_
    rw [e]; exact hd
  · -- extended to 32 bits, `trapIf (zero r)`
    obtain ⟨k, ms, hkr, hf, hklt, hk, hsem⟩ := ExtOut.sem hR hctx hvb (.inl rfl)
      (by intro t ht; simp at ht; rcases ht with rfl | rfl <;> simp) (fun _ => by simp) hE
    cases hkr
    refine ⟨k, ms ++ [.trapIf (.zero (.vreg k .int) .size32) .intDivz], rfl,
      hf.append (Frag.emit_nodef s2 (vdefs_trapIf_zero _ _ _)), hk,
      fun fr ρ ty b htw hh hdf hyv => ?_⟩
    obtain ⟨hu, hrun⟩ := hsem fr ρ _ hh hdf hyv
    refine ⟨UsesLo.append hu ?_, fun wd => ⟨by simpa [LState.emit] using hklt, ?_⟩⟩
    · intro m hm u hu'
      simp only [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_trapIf_zero, List.mem_singleton] at hu'
      subst hu'
      rcases hk with h | rfl
      · exact .inl h
      · exact .inr (by simp [hyv])
    have hd : ∀ a, ExtHolds (e == 0) 32 ⟨ty, b⟩ a → DivOpnd (e == 0) b a := by
      intro a ha
      unfold DivOpnd
      simp only [show ty.width ≤ 32 by omega, ↓reduceIte]
      exact ha.2 (by simp; omega)
    have hsz : szOf ty.width = .size32 := by simp [szOf, show ty.width ≤ 32 by omega]
    refine ⟨fun h0 => TrapRun.prefix (hrun wd) fun ρ1 w1 h1 => ?_, fun h0 => ?_⟩
    · have hz := (hd _ h1).zero_iff (by omega) w1 (.vreg k .int)
      rw [hsz] at hz
      exact trapRun_trapIf_zero hR _ _ _ ρ1 w1 (by rw [hz, h0]; simp)
    · refine Runs.append (hrun wd) fun ρ1 w1 h1 => ?_
      have hz := (hd _ h1).zero_iff (by omega) w1 (.vreg k .int)
      rw [hsz] at hz
      refine (runs_trapIf_zero_fall hR _ _ _ ρ1 w1 (by rw [hz]; simpa using h0)).imp fun ρ' _ _ e => ?_
      rw [e]; exact hd _ h1

end Backend.Proof

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

end Backend.Proof

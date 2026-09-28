import FV.Backend.Proof.IselCmpDivRem

/-!
# Family C: `sdiv` with the overflow check (rules 1145, 1153)

`intmin_check` (562: `lsl` by `32 - w` for i8/i16, else the dividend itself) and
`trap_if_div_overflow` (561: `adds xzr, y, #1; ccmp c, #1, #0000, eq; trapIf vs int_ovf`):
inverse contracts, then their run (`ovfCheck_run`, `intmin_code_sem`) and `sdiv_base_finish`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ctor_u8_into_uimm5_1 (ctx : Ctx) (st : LState) :
    externCtor ctx T.u8_into_uimm5 [.int 1] st = .ok (.op (.uimm5 1), st) := rfl
theorem ctor_nzcv_0 (ctx : Ctx) (st : LState) :
    externCtor ctx T.nzcv [.bool false, .bool false, .bool false, .bool false] st =
      .ok (.op (.nzcv ⟨false, false, false, false⟩), st) := rfl
theorem ctor_cond_br_cond (ctx : Ctx) (st : LState) (c : V) :
    externCtor ctx T.cond_br_cond [c] st = .ok (.data tyCondBrKind VIdx.CondBrKind.Cond [c], st) := rfl
theorem ctor_u8_into_imm12_1 (ctx : Ctx) (st : LState) :
    externCtor ctx T.u8_into_imm12 [.int 1] st = .ok (.op (.imm12 ⟨1, false⟩), st) := rfl

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
theorem size_from_ty_ok {n : Nat} (hn : 30 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 93 560 [.ty (.int w)] s v s') :
    s'.1 = s.1 ∧ v = .data 93 (if w ≤ 32 then 0 else 1) [] := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  isel_split' hp hc h 560 <;> (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  all_goals try (exfalso; obtain ⟨hx⟩ : Nonempty (CTy.int _ = CTy.int _) := ⟨‹_›⟩; cases hx; done)
  all_goals try (exfalso; have hx : (CTy.int 64).bits ≤ 32 := ‹_›; exact absurd hx (by decide))
  all_goals exact ⟨rfl, rfl⟩

theorem ofV_addsImm (i : Nat) {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz) (rd rn : Reg)
    (imm : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 9 [], .data 93 i [], .reg rd, .reg rn, .op (.imm12 imm)]) =
      some (.aluRRImm12 .addS sz rd rn imm) := by
  match i, hi with
  | 0, hi => cases hi; rfl
  | 1, hi => cases hi; rfl

theorem ofV_ccmpImm1 (i : Nat) {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz) (rn : Reg) :
    MInst.ofV (.data 58 36 [.data 93 i [], .reg rn, .op (.uimm5 1),
      .op (.nzcv ⟨false, false, false, false⟩), .data 96 0 []]) =
      some (.ccmpImm sz rn 1 ⟨false, false, false, false⟩ .eq) := by
  match i, hi with
  | 0, hi => cases hi; rfl
  | 1, hi => cases hi; rfl

theorem ofV_trapIf_vs :
    MInst.ofV (.data 58 120 [.data 83 VIdx.CondBrKind.Cond [.data 96 6 []], .op (.trapCode .intOvf)]) =
      some (.trapIf (.cond .vs) .intOvf) := rfl

theorem szIdx_ofIdx (w : Nat) : OperandSize.ofIdx? (if w ≤ 32 then 0 else 1) = some (szOf w) := by
  unfold szOf; split <;> rfl

set_option maxHeartbeats 4000000 in
include hp hc in
theorem trap_if_div_overflow_ok {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {rc rx ry : Reg} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 561 [.ty (.int w), .reg rc, .reg rx, .reg ry] s v s') :
    v = .reg rx ∧ s'.1 = ((s.1.emit (.aluRRImm12 .addS (szOf w) .xzr ry ⟨1, false⟩)).emit
      (.ccmpImm (szOf w) rc 1 ⟨false, false, false, false⟩ .eq)).emit (.trapIf (.cond .vs) .intOvf) := by
  isel_split' hp hc h 561
  all_goals isel_inv' hp [ctor_trap_ovf_iff, ctor_u8_into_uimm5_1, ctor_nzcv_0, ctor_cond_br_cond,
    ctor_u8_into_imm12_1] at hm he
  all_goals
    obtain ⟨h305⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 93 305 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨h560⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 93 560 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨hs5, hv5⟩ := operand_size_ok hp hc (by omega) h305
    obtain ⟨hs6, rfl⟩ := size_from_ty_ok hp hc (by omega) (by decide) h560
    obtain ⟨hm1⟩ : Nonempty (MInst.ofV (.data 58 4 _) = some _) := ⟨‹_›⟩
    obtain ⟨hm2⟩ : Nonempty (MInst.ofV (.data 58 36 _) = some _) := ⟨‹_›⟩
    obtain ⟨hm3⟩ : Nonempty (MInst.ofV (.data 58 120 _) = some _) := ⟨‹_›⟩
    rw [ofV_ccmpImm1 _ (szIdx_ofIdx _)] at hm2
    rw [ofV_trapIf_vs] at hm3
    cases hm2; cases hm3
    rcases hv5 with ⟨hb, rfl⟩ | ⟨hb, -, rfl⟩ <;> (try (exact absurd hb (by decide)))
    all_goals
      rw [ofV_addsImm _ rfl] at hm1
      cases hm1
      try refine ⟨rfl, ?_⟩
      try simp only at hs6 ⊢
      rw [hs6, hs5]
      rfl
theorem ctor_imm_shift_from_u8' (ctx : Ctx) (st : LState) (k : Nat) (hk : k < 64) :
    externCtor ctx T.imm_shift_from_u8 [.int (k : Int)] st = .ok (.op (.immShift k), st) := by
  show (if (k : Int) < 64 then ExtResult.ok (V.op (.immShift (k : Int).toNat), st) else .fail) = _
  split
  · rfl
  · omega

set_option maxHeartbeats 4000000 in
include hp hc in
theorem diff_from_32_ok {n : Nat} (hn : 30 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 1 306 [.ty (.int w)] s v s') :
    s'.1 = s.1 ∧ v = .int ((32 - w : Nat) : Int) := by
  rcases hw with rfl | rfl <;>
  isel_split' hp hc h 306 <;> (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  all_goals first
    | rfl
    | (exfalso; simp only [CTy.int.injEq] at *; omega)

set_option maxHeartbeats 4000000 in
include hp hc in
theorem lsl_imm32_ok {n : Nat} (hn : 40 ≤ n) {k w : Nat} (hw : w ≤ 32) {ra : Reg} {i : Nat}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 361 [.data 59 k [], .ty (.int w), .reg ra, .op (.immShift i)] s v s') :
    ∃ m, MInst.ofV (.data 58 6 [.data 59 k [], .data 93 0 [], .reg (s.1.fresh .int).1, .reg ra, .op (.immShift i)]) = some m ∧
    v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  isel_split' hp hc h 361
  all_goals isel_inv' hp [] at hm he
  obtain ⟨h305⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 93 305 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hm1⟩ : Nonempty (MInst.ofV _ = some _) := ⟨‹_›⟩
  obtain ⟨hs, hsz⟩ := operand_size_ok hp hc (by omega) h305
  simp only [show (CTy.int w).bits = w from rfl] at hsz
  rcases hsz with ⟨hb, rfl⟩ | ⟨hb, -, rfl⟩
  · refine ⟨_, hm1, ?_⟩
    first | exact ⟨rfl, by rw [hs]⟩ | rw [hs]
  · omega

theorem ofV_lsl18 (rd rn : Reg) (i : Nat) :
    MInst.ofV (.data 58 6 [.data 59 18 [], .data 93 0 [], .reg rd, .reg rn, .op (.immShift i)]) =
      some (.aluRRImmShift .lsl .size32 rd rn i) := rfl

set_option maxHeartbeats 4000000 in
include hp hc in
theorem intmin_check_ok {n : Nat} (hn : 60 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {rx : Reg} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 562 [.ty (.int w), .reg rx] s v s') :
    (w ≤ 16 ∧ v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.aluRRImmShift .lsl .size32 (s.1.fresh .int).1 rx (32 - w))) ∨
    (16 < w ∧ v = .reg rx ∧ s'.1 = s.1) := by
  isel_split' hp hc h 562
  all_goals isel_inv' hp [] at hm he
  all_goals try (exfalso; have hx : (CTy.int _).bits ≤ 16 := ‹_›; exact absurd hx (by decide); done)
  -- fallback rule for i8/i16: refuted by the `fits_in_16` rule before it
  all_goals try (exact .inr ⟨by decide, rfl, rfl⟩)
  all_goals try (
    exfalso
    obtain ⟨k, s2, h2⟩ := hpre _ (List.mem_singleton_self _)
    revert h2
    cases hp
    isel_eval [*, rule_inst_3888, ext_fits_in_16', CTy.bits]
    simp; done)
  all_goals try (simp; done)
  all_goals
    obtain ⟨h306⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 1 306 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨h361⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 361 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨hsh⟩ : Nonempty (externCtor ctx T.imm_shift_from_u8 _ _ = _) := ⟨‹_›⟩
    obtain ⟨hs6, rfl⟩ := diff_from_32_ok hp hc (by omega) (by decide) h306
    rw [ctor_imm_shift_from_u8' _ _ _ (by decide)] at hsh
    cases hsh
    obtain ⟨m, hm1, rfl, hs⟩ := lsl_imm32_ok hp hc (by omega) (by decide) h361
    rw [ofV_lsl18] at hm1
    cases hm1
    first
      | (left; simp only [hs6] at hs ⊢; exact ⟨rfl, hs⟩)
      | (simp only [hs6] at hs ⊢; exact ⟨rfl, hs⟩)
      | (simp only [hs6] at hs ⊢; simp [hs])
end

section OvfFlags
set_option maxHeartbeats 1000000

theorem condOn_adds1_32 (a : BitVec 32) :
    condOn Cond.eq.bits (Arm.AddWithCarry a (BitVec.ofNat 32 1) 0#1).2 = (a == BitVec.allOnes 32) := by
  simp only [condOn, Cond.bits, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq]
  bv_decide
theorem condOn_adds1_64 (a : BitVec 64) :
    condOn Cond.eq.bits (Arm.AddWithCarry a (BitVec.ofNat 64 1) 0#1).2 = (a == BitVec.allOnes 64) := by
  simp only [condOn, Cond.bits, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq]
  bv_decide
theorem condOn_sub1_vs_32 (a : BitVec 32) :
    condOn Cond.vs.bits (cmpFlags a (BitVec.ofNat 32 1)) = (a == BitVec.intMin 32) := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq]
  bv_decide
theorem condOn_sub1_vs_64 (a : BitVec 64) :
    condOn Cond.vs.bits (cmpFlags a (BitVec.ofNat 64 1)) = (a == BitVec.intMin 64) := by
  simp only [condOn, Cond.bits, cmpFlags, Arm.AddWithCarry, Arm.make_pstate, BitVec.zero_eq]
  bv_decide
theorem condOn_nzcv0_vs :
    condOn Cond.vs.bits (Arm.make_pstate (BitVec.ofBool false) (BitVec.ofBool false)
      (BitVec.ofBool false) (BitVec.ofBool false)) = false := by
  simp only [condOn, Cond.bits, Arm.make_pstate]
  decide

end OvfFlags

theorem condOn_adds1 (sz : OperandSize) (a : BitVec sz.bits) :
    condOn Cond.eq.bits (Arm.AddWithCarry a (BitVec.ofNat sz.bits 1) 0#1).2 = (a == BitVec.allOnes sz.bits) := by
  cases sz
  · exact condOn_adds1_32 a
  · exact condOn_adds1_64 a

theorem condOn_sub1_vs (sz : OperandSize) (a : BitVec sz.bits) :
    condOn Cond.vs.bits (cmpFlags a (BitVec.ofNat sz.bits 1)) = (a == BitVec.intMin sz.bits) := by
  cases sz
  · exact condOn_sub1_vs_32 a
  · exact condOn_sub1_vs_64 a

section Run
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- The overflow check of `trap_if_div_overflow`: `adds xzr, y, #1; ccmp c, #1, #0, eq;
b.vs trap`. -/
def ovfCheck (sz : OperandSize) (kc ky : Nat) : List MInst :=
  [.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩,
   .ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq,
   .trapIf (.cond .vs) .intOvf]

theorem ovfCheck_run (hR : Refines F isem) (sz : OperandSize) (kc ky : Nat) (ρ : Nat → CV)
    (w : Arm.ArmState) :
    (opnd sz (ρ ky) = BitVec.allOnes sz.bits ∧ opnd sz (ρ kc) = BitVec.intMin sz.bits →
      TrapRun isem (ovfCheck sz kc ky) ρ w .intOvf) ∧
    (¬ (opnd sz (ρ ky) = BitVec.allOnes sz.bits ∧ opnd sz (ρ kc) = BitVec.intMin sz.bits) →
      Runs F isem (ovfCheck sz kc ky) ρ w (fun ρ' _ => ρ' = ρ)) := by
  have hs1 : SetsFlags (.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩) ρ
      (Arm.AddWithCarry (opnd sz (ρ ky)) (BitVec.ofNat sz.bits 1) 0#1).2 :=
    ⟨_, rfl, rfl, fun w => by show ispec _ [ρ ky] w = _; simp [ispec, defOut, Imm12.value]⟩
  have h12 : Runs F isem [.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩,
      .ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq] ρ w (fun ρ' w' => ρ' = ρ ∧
      Arm.ConditionHolds Cond.vs.bits w' =
        (opnd sz (ρ ky) == BitVec.allOnes sz.bits && opnd sz (ρ kc) == BitVec.intMin sz.bits)) := by
    refine Runs.append (ms1 := [_]) (Runs.flags hR hs1 w) fun ρ1 w1 ⟨h1, h2⟩ => ?_
    subst h1
    have hs2 : ispec (.ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq) [ρ1 kc] w1 =
        some ([], Arm.write_pstate (if Arm.ConditionHolds Cond.eq.bits w1 then
          cmpFlags (opnd sz (ρ1 kc)) (BitVec.ofNat sz.bits 1) else
          Arm.make_pstate (BitVec.ofBool false) (BitVec.ofBool false) (BitVec.ofBool false)
            (BitVec.ofBool false)) w1, .next) := by
      simp [ispec, cmpFlags]
    refine Runs.one hR rfl hs2 rfl (SameWorldNF.write_pstate F _ w1) fun w'' hw => ⟨vdefUpd_nil _ _, ?_⟩
    rw [SameWorld.conditionHolds hw, conditionHolds_write_pstate, h2, condOn_adds1]
    split
    · rename_i hc; rw [hc, Bool.true_and, condOn_sub1_vs]
    · rename_i hc; simp only [Bool.not_eq_true] at hc; rw [hc, Bool.false_and, condOn_nzcv0_vs]
  have hlast : ovfCheck sz kc ky = [.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩,
      .ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq] ++ [.trapIf (.cond .vs) .intOvf] := rfl
  constructor
  · intro ⟨ha, hb⟩
    rw [hlast]
    refine TrapRun.prefix h12 fun ρ1 w1 ⟨_, hv⟩ => ?_
    have hs : ispec (.trapIf (.cond .vs) .intOvf) [] w1 = some ([], w1, .halt) := by
      show some ([], w1, if Arm.ConditionHolds Cond.vs.bits w1 then Ctl.halt else Ctl.next) = _
      rw [hv, ha, hb]; simp
    obtain ⟨w'', hr⟩ := seqRun_one_halt (F := F) hR (i := .trapIf (.cond .vs) .intOvf) rfl (ρ := ρ1) hs rfl
    exact ⟨_, _, _, _, _, _, _, hr, rfl⟩
  · intro hn
    rw [hlast]
    refine Runs.append h12 fun ρ1 w1 ⟨h1, hv⟩ => ?_
    subst h1
    refine Runs.one hR (i := .trapIf (.cond .vs) .intOvf) rfl (outs := []) (w' := w1) ?_ rfl
      (SameWorldNF.refl F w1) fun _ _ => vdefUpd_nil _ _
    show some ([], w1, if Arm.ConditionHolds Cond.vs.bits w1 then Ctl.halt else Ctl.next) = _
    have : Arm.ConditionHolds Cond.vs.bits w1 = false := by
      rw [hv]; simpa [Bool.and_eq_true, beq_iff_eq] using hn
    rw [this]; rfl

end Run

section Intmin
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem runs_lsl32 (hR : Refines F isem) (d x s : Nat) (hs : s < 32) (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.aluRRImmShift .lsl .size32 (.vreg d .int) (.vreg x .int) s] ρ w
      (fun ρ' _ => ρ' = upd ρ d (resX .size32 (opnd .size32 (ρ x) <<< s))) :=
  Runs.one hR (ops := #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩]) rfl
    (outs := [resX .size32 (opnd .size32 (ρ x) <<< s)])
    (by show ispec _ [ρ x] w = _; simp [ispec, shiftVal, defOut, OperandSize.bits, hs]) rfl
    (SameWorldNF.refl F w) fun _ _ => rfl

set_option maxHeartbeats 1000000 in
theorem shl_intMin_8 (a : BitVec 8) : (a.signExtend 32 <<< 24 = BitVec.intMin 32) ↔ a = BitVec.intMin 8 := by
  bv_decide
set_option maxHeartbeats 1000000 in
theorem shl_intMin_16 (a : BitVec 16) : (a.signExtend 32 <<< 16 = BitVec.intMin 32) ↔ a = BitVec.intMin 16 := by
  bv_decide

theorem divOpnd_intMin {n : Nat} (hn : n = 32 ∨ n = 64) {a : BitVec n} {A : CV} (h : DivOpnd true a A) :
    opnd (szOf n) A = BitVec.intMin _ ↔ a = BitVec.intMin n := by
  rcases hn with rfl | rfl
  · have h' : (opnd .size32 A : BitVec 32) = a := by
      have := h; unfold DivOpnd at this; simp only [show (32:Nat) ≤ 32 by decide, ↓reduceIte] at this
      rw [show (opnd .size32 A : BitVec 32) = (lo64 A).setWidth 32 from rfl, this]
      apply BitVec.eq_of_toInt_eq; rw [BitVec.toInt_signExtend_of_le (by decide)]
    exact h' ▸ Iff.rfl
  · have h' : (opnd .size64 A : BitVec 64) = a := by
      have := h; unfold DivOpnd at this; simp only [show ¬ (64:Nat) ≤ 32 by decide, ↓reduceIte] at this
      rw [show (opnd .size64 A : BitVec 64) = (lo64 A).setWidth 64 from rfl, this]
      exact BitVec.setWidth_eq _
    exact h' ▸ Iff.rfl

theorem divOpnd_allOnes {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) {b : BitVec n} {B : CV}
    (h : DivOpnd true b B) : opnd (szOf n) B = BitVec.allOnes _ ↔ b = BitVec.allOnes n := by
  unfold DivOpnd at h
  rcases hn with rfl | rfl | rfl | rfl
  · simp only [show (8:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 32 = BitVec.allOnes 32) ↔ _
    rw [h]; bv_decide
  · simp only [show (16:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 32 = BitVec.allOnes 32) ↔ _
    rw [h]; bv_decide
  · simp only [show (32:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 32 = BitVec.allOnes 32) ↔ _
    rw [h]; bv_decide
  · simp only [show ¬ (64:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 64 = BitVec.allOnes 64) ↔ _
    rw [h]; simp

theorem vdefs_lsl' (d x s : Nat) :
    vdefs (MInst.aluRRImmShift .lsl .size32 (.vreg d .int) (.vreg x .int) s) = [d] := rfl
theorem vuseNums_lsl' (d x s : Nat) :
    vuseNums (MInst.aluRRImmShift .lsl .size32 (.vreg d .int) (.vreg x .int) s) = [x] := rfl

/-- **`intmin_check`** as code: the register `kc` whose `size_from_ty` operand is the minimum iff
the dividend is. -/
theorem intmin_code_sem (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {s2 s3 : LState} {v : V} {kx : Nat}
    (hI : (w ≤ 16 ∧ v = .reg (s2.fresh .int).1 ∧ s3 = (s2.fresh .int).2.emit
        (.aluRRImmShift .lsl .size32 (s2.fresh .int).1 (.vreg kx .int) (32 - w))) ∨
      (16 < w ∧ v = .reg (.vreg kx .int) ∧ s3 = s2)) :
    ∃ kc msC, v = .reg (.vreg kc .int) ∧ Frag s2 s3 msC ∧ (kc = kx ∨ s2.nextVreg ≤ kc) ∧
      (kc = kx ∨ kc < s3.nextVreg) ∧ (∀ m ∈ msC, ∀ u ∈ vuseNums m, u = kx) ∧
      ∀ (a : BitVec w) (ρ : Nat → CV) (wd : Arm.ArmState), DivOpnd true a (ρ kx) →
        Runs F isem msC ρ wd (fun ρ' _ => (∀ z < s2.nextVreg, ρ' z = ρ z) ∧
          (opnd (szOf w) (ρ' kc) = BitVec.intMin _ ↔ a = BitVec.intMin w)) := by
  rcases hI with ⟨hw16, rfl, rfl⟩ | ⟨hw16, rfl, rfl⟩
  · refine ⟨s2.nextVreg, [.aluRRImmShift .lsl .size32 (.vreg s2.nextVreg .int) (.vreg kx .int) (32 - w)],
      rfl, Frag.fresh_emit s2 (by rw [show (s2.fresh .int).1 = .vreg s2.nextVreg .int from rfl, vdefs_lsl']; simp),
      .inr (Nat.le_refl _),
      .inr (by simp [LState.emit, LState.fresh]), ?_, ?_⟩
    · intro m hm u hu
      simp only [List.mem_singleton] at hm; subst hm
      rw [vuseNums_lsl', List.mem_singleton] at hu; exact hu
    · intro a ρ wd ha
      refine (runs_lsl32 hR _ _ _ (by omega) ρ wd).imp fun ρ' _ _ e => ⟨fun z hz => ?_, ?_⟩
      · rw [e]; simp [upd, show z ≠ s2.nextVreg by omega]
      · rw [e, upd_same]
        unfold DivOpnd at ha
        rcases hw with rfl | rfl | rfl | rfl <;> (try omega)
        · simp only [show (8:Nat) ≤ 32 by decide, ↓reduceIte] at ha
          show (opnd .size32 (resX .size32 (opnd .size32 (ρ kx) <<< 24)) = BitVec.intMin 32) ↔ _
          rw [cmp_opnd_resX, show (opnd .size32 (ρ kx) : BitVec 32) = (lo64 (ρ kx)).setWidth 32 from rfl, ha]
          exact shl_intMin_8 a
        · simp only [show (16:Nat) ≤ 32 by decide, ↓reduceIte] at ha
          show (opnd .size32 (resX .size32 (opnd .size32 (ρ kx) <<< 16)) = BitVec.intMin 32) ↔ _
          rw [cmp_opnd_resX, show (opnd .size32 (ρ kx) : BitVec 32) = (lo64 (ρ kx)).setWidth 32 from rfl, ha]
          exact shl_intMin_16 a
  · refine ⟨kx, [], rfl, Frag.nil _, .inl rfl, .inl rfl, by simp, fun a ρ wd ha =>
      Runs.nil ⟨fun _ _ => rfl, divOpnd_intMin (by omega) ha⟩⟩

end Intmin

theorem vuseNums_adds1 (sz : OperandSize) (k : Nat) :
    vuseNums (MInst.aluRRImm12 .addS sz .xzr (.vreg k .int) ⟨1, false⟩) = [k] := rfl
theorem vuseNums_ccmp1 (sz : OperandSize) (k : Nat) :
    vuseNums (MInst.ccmpImm sz (.vreg k .int) 1 ⟨false, false, false, false⟩ .eq) = [k] := rfl
theorem vuseNums_trapIf_vs : vuseNums (MInst.trapIf (.cond .vs) .intOvf) = [] := rfl

theorem Frag.ovfCheck (s : LState) (sz : OperandSize) (kc ky : Nat) :
    Frag s (((s.emit (.aluRRImm12 .addS sz .xzr (.vreg ky .int) ⟨1, false⟩)).emit
      (.ccmpImm sz (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq)).emit
      (.trapIf (.cond .vs) .intOvf)) (ovfCheck sz kc ky) :=
  ((Frag.emit_nodef s rfl).append (Frag.emit_nodef _ rfl)).append (Frag.emit_nodef _ rfl)

section Finish
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx} {ty : Clif.Ty} {x y : Nat} {st s1 s2 : LState} {kx ky : Nat} {msX msY : List MInst}

theorem sdiv_base_finish (hR : Refines F isem) (hMR : MRStable F MR)
    (hw4 : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {results : List Nat} (h : DivOperands F isem ctx ty x y true st s1 s2 kx ky msX msY)
    {s3 : LState} {kc : Nat} {msC : List MInst} (hfC : Frag s2 s3 msC) (hkc : kc = kx ∨ s2.nextVreg ≤ kc)
    (huC : ∀ m ∈ msC, ∀ u ∈ vuseNums m, u = kx)
    (hsC : ∀ (a : BitVec ty.width) (ρ : Nat → CV) (wd : Arm.ArmState), DivOpnd true a (ρ kx) →
      Runs F isem msC ρ wd (fun ρ' _ => (∀ z < s2.nextVreg, ρ' z = ρ z) ∧
        (opnd (szOf ty.width) (ρ' kc) = BitVec.intMin _ ↔ a = BitVec.intMin ty.width))) :
    let s4 := ((s3.emit (.aluRRImm12 .addS (szOf ty.width) .xzr (.vreg ky .int) ⟨1, false⟩)).emit
      (.ccmpImm (szOf ty.width) (.vreg kc .int) 1 ⟨false, false, false, false⟩ .eq)).emit
      (.trapIf (.cond .vs) .intOvf)
    let m := MInst.aluRRR .sDiv (szOf ty.width) (.vreg s4.nextVreg .int) (.vreg kx .int) (.vreg ky .int)
    LowerInstOk isem MR env cp ctx (.div .sdiv ty x y) results st [[.vreg s4.nextVreg .int]]
      ((s4.fresh .int).2.emit m) (msX ++ msY ++ (msC ++ (ovfCheck (szOf ty.width) kc ky ++ [m]))) ∧
    ((s4.fresh .int).2.emit m).emitted =
      st.emitted ++ (msX ++ msY ++ (msC ++ (ovfCheck (szOf ty.width) kc ky ++ [m]))).toArray := by
  intro s4 m
  have hfO := Frag.ovfCheck s3 (szOf ty.width) kc ky
  have hfM : Frag s4 ((s4.fresh .int).2.emit m) [m] := Frag.fresh_emit s4 (by simp [m, vdefs_aluRRR'])
  have hf := (h.fX.append h.fY).append (hfC.append (hfO.append hfM))
  have hs4 : s4.nextVreg = s3.nextVreg := rfl
  have h23 := hfC.mono
  have hw' : ty.width ≤ 32 ∨ ty.width = 64 := by omega
  refine ⟨lowerInstOk_div hMR hf.mono hf.defs
    (by have := (h.fX.append h.fY).mono; omega) ?_, hf.emitted⟩
  intro fr ρ w a b _ hh hdf hxa hyb
  obtain ⟨hu, hukx, huky⟩ := h.uses hh hdf hxa hyb
  obtain ⟨hky, htr, hrun⟩ := h.run hh hdf hxa hyb w
  have hkx := h.kxlt
  have h12 := h.fY.mono
  have hlo : st.nextVreg ≤ s2.nextVreg := (h.fX.append h.fY).mono
  -- the code after the operands, from the operand values
  have hrest : ∀ ρ1 w1, DivOpnd true a (ρ1 kx) → DivOpnd true b (ρ1 ky) →
      ((a = BitVec.intMin _ ∧ b = BitVec.allOnes _) →
        TrapRun isem (msC ++ (ovfCheck (szOf ty.width) kc ky ++ [m])) ρ1 w1 .intOvf) ∧
      (¬ (a = BitVec.intMin _ ∧ b = BitVec.allOnes _) →
        Runs F isem (msC ++ (ovfCheck (szOf ty.width) kc ky ++ [m])) ρ1 w1
          (fun ρ' _ => VHolds ⟨ty, a.sdiv b⟩ (ρ' s4.nextVreg))) := by
    intro ρ1 w1 h1 h2
    have hC := hsC a ρ1 w1 h1
    constructor
    · intro hov
      refine TrapRun.prefix hC fun ρ2 w2 ⟨hfr, hic⟩ => ?_
      refine TrapRun.append ((ovfCheck_run hR (szOf ty.width) kc ky ρ2 w2).1 ⟨?_, hic.2 hov.1⟩)
      rw [hfr ky (by omega)]
      exact (divOpnd_allOnes hw4 h2).2 hov.2
    · intro hov
      refine Runs.append hC fun ρ2 w2 ⟨hfr, hic⟩ => ?_
      refine Runs.append ((ovfCheck_run hR (szOf ty.width) kc ky ρ2 w2).2 ?_) fun ρ3 w3 e3 => ?_
      · rintro ⟨hb1, hc1⟩
        rw [hfr ky (by omega)] at hb1
        exact hov ⟨hic.1 hc1, (divOpnd_allOnes hw4 h2).1 hb1⟩
      · subst e3
        refine (runs_sdiv hR _ _ _ _ _ w3).imp fun ρ' _ _ e => ?_
        rw [e, upd_same, hfr kx (by omega), hfr ky (by omega)]
        refine sdiv_core hw' h1 h2 ?_
        by_cases ha : a = BitVec.intMin _
        · exact .inr (by rw [BitVec.neg_one_eq_allOnes]; exact fun hb => hov ⟨ha, hb⟩)
        · exact .inl ha
  refine ⟨hu.append ?_, fun c hc => ?_, fun q hq => ?_⟩
  · intro mi hm u hu'
    simp only [List.mem_append, ovfCheck, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with hm | (rfl | rfl | rfl) | rfl
    · rw [huC mi hm u hu']; exact hukx
    · rw [vuseNums_adds1, List.mem_singleton] at hu'; subst hu'; exact huky
    · rw [vuseNums_ccmp1, List.mem_singleton] at hu'; subst hu'
      rcases hkc with rfl | hkc
      · exact hukx
      · exact .inl (by omega)
    · rw [vuseNums_trapIf_vs] at hu'; cases hu'
    · simp only [m, vuseNums_aluRRR', List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl
      · exact hukx
      · exact huky
  · rcases sdiv_trap hc with ⟨h0, rfl⟩ | ⟨h0, ha, hb, rfl⟩
    · exact (htr h0).append
    · exact TrapRun.prefix (hrun h0) fun ρ1 w1 ⟨h1, h2⟩ => (hrest ρ1 w1 h1 h2).1 ⟨ha, hb⟩
  · obtain ⟨h0, hn, rfl⟩ := sdiv_ok hq
    exact Runs.append (hrun h0) fun ρ1 w1 ⟨h1, h2⟩ => (hrest ρ1 w1 h1 h2).2 hn

end Finish


section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem sdiv64_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1145 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h493⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 493 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h561⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 561 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h562⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 562 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h557⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 557 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  obtain ⟨hty⟩ : Nonempty (CTy.int 64 = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .sdiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hty
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width,
    CTy.int.injEq] at hty
  have hE := sext64_ok hp hco (hn := by omega) h557
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpnd hR hctx hvb (w := ty.width) (.inr ⟨rfl, rfl, hty.symm⟩) (.inr hty.symm) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := 64) (e := 0) (by decide)
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_sem hR hctx (w := 64) (e := 0) (by decide) (by decide) hvb2 hD
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b hty.symm hv hdf hyb }
  have hw4 : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := .inr (.inr (.inr hty.symm))
  have hI := intmin_check_ok hp hco (hn := by omega) (w := 64) (by decide) h562
  rw [show (64 : Nat) = ty.width from hty] at hI
  obtain ⟨kc, msC, rfl, hfC, hkc, -, huC, hsC⟩ := intmin_code_sem (F := F) (isem := isem) hR
    (w := ty.width) hw4 hI
  obtain ⟨hv5, hs5⟩ := trap_if_div_overflow_ok hp hco (hn := by omega) (by decide) h561
  subst hv5
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by decide) h493
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  obtain ⟨hok, hem⟩ := sdiv_base_finish (env := env) (cp := cp) hR hMR hw4 (results := info.results) hdo
    hfC hkc huC hsC
  simp only at hs3
  rw [hs3, hs2, hs5]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem sdiv32_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1153 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h493⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 493 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h561⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 561 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h562⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 562 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h555⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 555 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  have hb32 : (info.resTys.head?.getD CTy.invalid).bits ≤ 32 := by
    rw [hi, Option.some.injEq] at hins; subst hins; assumption
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .sdiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hb32 h698 h562 h561 h493
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width]
    at hb32 h698 h562 h561 h493
  have hw32 : ty.width ≤ 32 := hb32
  have hwid := cmp_eTy_widths hety
  have hE := sext32_ok hp hco (hn := by omega) h555
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpnd hR hctx hvb (w := ty.width) (.inl ⟨rfl, rfl⟩) (.inl hw32) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := ty.width) (e := 0) hwid
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_sem hR hctx (w := ty.width) (e := 0) hwid (by decide) hvb2 hD
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  have hw4 : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := hwid
  have hI := intmin_check_ok hp hco (hn := by omega) (w := ty.width) hwid h562
  obtain ⟨kc, msC, rfl, hfC, hkc, -, huC, hsC⟩ := intmin_code_sem (F := F) (isem := isem) hR
    (w := ty.width) hw4 hI
  obtain ⟨hv5, hs5⟩ := trap_if_div_overflow_ok hp hco (hn := by omega) hwid h561
  subst hv5
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by omega) h493
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  obtain ⟨hok, hem⟩ := sdiv_base_finish (env := env) (cp := cp) hR hMR hw4 (results := info.results) hdo
    hfC hkc huC hsC
  simp only at hs3
  rw [hs3, hs2, hs5]
  exact ⟨_, hem, _, rfl, hok⟩

end Root

end Backend.Proof

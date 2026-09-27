import FV.Backend.Proof.IselCmpIcmp
import FV.Backend.Proof.IselFamALUA

/-!
# `emit_icmp`: the condition of an integer comparison

`emit_icmp_ok`: the code `emit_icmp cc x y` appends leaves a condition (`CondCode`) that is
`Clif.Sem.intcc cc a b` whenever `x`, `y` hold `a`, `b` of one type.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## `IntCC` values -/

/-- Variant index of an `IntCC` (`mkVariant tyIntCC (intccName cc)`). -/
def ccIdx : Clif.IntCC → Nat
  | .eq => 0 | .ne => 1 | .sgt => 2 | .sge => 3 | .slt => 4 | .sle => 5
  | .ugt => 6 | .uge => 7 | .ult => 8 | .ule => 9

theorem mkVariant_intcc (cc : Clif.IntCC) :
    mkVariant tyIntCC (intccName cc) = .data 145 (ccIdx cc) [] := by
  cases cc <;> rfl

theorem condOfIntCC_ccIdx (cc : Clif.IntCC) : condOfIntCC (ccIdx cc) = some (condOf cc) := by
  cases cc <;> rfl

theorem V.intcc?_data (k : Nat) : (V.data 145 k []).intcc? = some k := rfl

theorem ccIdx_eq_0 {cc : Clif.IntCC} (h : ccIdx cc = 0) : cc = .eq := by
  cases cc <;> simp [ccIdx] at h ⊢
theorem ccIdx_eq_1 {cc : Clif.IntCC} (h : ccIdx cc = 1) : cc = .ne := by
  cases cc <;> simp [ccIdx] at h ⊢
theorem ccIdx_eq_3 {cc : Clif.IntCC} (h : ccIdx cc = 3) : cc = .sge := by
  cases cc <;> simp [ccIdx] at h ⊢
theorem ccIdx_eq_7 {cc : Clif.IntCC} (h : ccIdx cc = 7) : cc = .uge := by
  cases cc <;> simp [ccIdx] at h ⊢

theorem condOf_ne_al (cc : Clif.IntCC) : condOf cc ≠ .al ∧ condOf cc ≠ .nv := by
  cases cc <;> decide

section Ext
variable (ctx : Ctx) (st : LState)

/-- `signed_cond_code` accepts the variant index. -/
def signedIdx (k : Nat) : Bool :=
  [VIdx.IntCC.SignedGreaterThanOrEqual, VIdx.IntCC.SignedGreaterThan,
    VIdx.IntCC.SignedLessThanOrEqual, VIdx.IntCC.SignedLessThan].contains k

/-- `unsigned_cond_code` accepts the variant index. -/
def unsignedIdx (k : Nat) : Bool :=
  [VIdx.IntCC.Equal, VIdx.IntCC.UnsignedGreaterThanOrEqual, VIdx.IntCC.UnsignedGreaterThan,
    VIdx.IntCC.UnsignedLessThanOrEqual, VIdx.IntCC.UnsignedLessThan, VIdx.IntCC.NotEqual].contains k

theorem ctor_signed_cond_code_iff (k : Nat) (v : V) (st' : LState) :
    externCtor ctx T.signed_cond_code [.data 145 k []] st = .ok (v, st') ↔
      signedIdx k = true ∧ v = .data 145 k [] ∧ st' = st := by
  have : externCtor ctx T.signed_cond_code [.data 145 k []] st =
      if signedIdx k then .ok (.data 145 k [], st) else .fail := rfl
  rw [this]
  cases signedIdx k <;> simp [eq_comm]

theorem ctor_unsigned_cond_code_iff (k : Nat) (v : V) (st' : LState) :
    externCtor ctx T.unsigned_cond_code [.data 145 k []] st = .ok (v, st') ↔
      unsignedIdx k = true ∧ v = .data 145 k [] ∧ st' = st := by
  have : externCtor ctx T.unsigned_cond_code [.data 145 k []] st =
      if unsignedIdx k then .ok (.data 145 k [], st) else .fail := rfl
  rw [this]
  cases unsignedIdx k <;> simp [eq_comm]

theorem ctor_u64_is_odd_iff (a : Int) (v : V) (st' : LState) :
    externCtor ctx T.u64_is_odd [.int a] st = .ok (v, st') ↔ v = .bool (a % 2 == 1) ∧ st' = st := by
  have : externCtor ctx T.u64_is_odd [.int a] st = .ok (.bool (a % 2 == 1), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_u64_wrapping_sub_iff (a b : Int) (v : V) (st' : LState) :
    externCtor ctx T.u64_wrapping_sub [.int a, .int b] st = .ok (v, st') ↔
      v = .int (u64 (a - b)) ∧ st' = st := by
  have : externCtor ctx T.u64_wrapping_sub [.int a, .int b] st = .ok (.int (u64 (a - b)), st) := rfl
  rw [this]; simp [eq_comm]

end Ext

theorem signed_of_idx {cc : Clif.IntCC} (h : signedIdx (ccIdx cc) = true) : signedCC cc = true := by
  revert h; cases cc <;> decide

theorem unsigned_of_idx {cc : Clif.IntCC} (h : unsignedIdx (ccIdx cc) = true) :
    signedCC cc = false := by
  revert h; cases cc <;> decide

theorem some_bind_ccIdx (cc : Clif.IntCC) :
    (some (ccIdx cc) >>= condOfIntCC) = some (condOf cc) := condOfIntCC_ccIdx cc

/-! ## The condition an `icmp` computes -/

/-- `x` and `y` hold values `a`, `b'` of one type and `b` is `intcc cc a b'`. -/
def IcmpT (cc : Clif.IntCC) (x y : Nat) (fr : Clif.Frame) (b : Bool) : Prop :=
  ∃ (ty : Clif.Ty) (a b' : BitVec ty.width), fr.regs x = some ⟨ty, a⟩ ∧ fr.regs y = some ⟨ty, b'⟩ ∧
    b = Clif.Sem.intcc cc a b'

theorem CondCode.weaken {F : BitVec 64 → Prop} {isem : Sem} {ctx : Ctx} {st st' : LState} {c : V}
    {T T' : Clif.Frame → Bool → Prop} (h : CondCode F isem ctx st st' c T)
    (hT : ∀ fr ρ b, ValsHeld fr ρ → DFGCons ctx fr → T' fr b → T fr b) :
    CondCode F isem ctx st st' c T' := by
  obtain ⟨ms, hf, hs, hr⟩ := h
  exact ⟨ms, hf, hs, fun fr ρ b hh hd hT' => hr fr ρ b hh hd (hT fr ρ b hh hd hT')⟩

theorem CondCode.shape {F : BitVec 64 → Prop} {isem : Sem} {ctx : Ctx} {st st' : LState} {c : V}
    {T : Clif.Frame → Bool → Prop} (h : CondCode F isem ctx st st' c T) :
    CondShape c (· < st'.nextVreg) := by
  obtain ⟨_, _, hs, _⟩ := h
  exact hs

theorem CondCode.st_eq {F : BitVec 64 → Prop} {isem : Sem} {ctx : Ctx} {st st' st'' : LState}
    {c : V} {T : Clif.Frame → Bool → Prop} (h : CondCode F isem ctx st st' c T) (he : st'' = st') :
    CondCode F isem ctx st st'' c T := he ▸ h

/-! ## `iconst` look-through -/

theorem iconst_data_inv {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {y j : Nat}
    {info : IInfo} {w : V} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hd : V.data 152 35 [V.data 151 57 [], w] = info.data) :
    ∃ ty imm, w = .int (imm64OfIconst ty imm) ∧ eTy ty = true ∧ info.clif = some (.iconst ty imm) := by
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hi
  rw [← hd] at hdat
  obtain ⟨ty, imm, rfl, hfs⟩ := instData_iconst_inv hdat
  exact ⟨ty, imm, by simpa using hfs, instData_iconst_eTy hdat, hcl⟩

theorem iconst_val {ctx : Ctx} {fr : Clif.Frame} (hdf : DFGCons ctx fr) {y j : Nat} {info : IInfo}
    {ty : Clif.Ty} {imm : BitVec ty.width} {v : Clif.Val} (hj : ctx.defInst? y = some j)
    (hi : ctx.insts[j]? = some info) (hcl : info.clif = some (.iconst ty imm))
    (hv : fr.regs y = some v) : v = ⟨ty, imm⟩ :=
  dfg_single hdf hj hi hcl rfl hv fun vals cm cm' h => by
    rw [evalInst_iconst] at h; cases h; rfl

theorem u64_iconst {ty : Clif.Ty} (he : eTy ty = true) (imm : BitVec ty.width) :
    u64 ((u64 (imm64OfIconst ty imm) : Nat) : Int) = imm.toNat := by
  have hw := eTy_width he
  rw [u64_imm64OfIconst hw]
  exact u64_ofNat (Nat.lt_of_lt_of_le imm.isLt (Nat.pow_le_pow_right (by omega) hw))

/-! ## Compare instructions -/

theorem vuseNums_cmpRR (sz : OperandSize) (a b : Nat) :
    vuseNums (.aluRRR .subS sz .xzr (.vreg a .int) (.vreg b .int)) = [a, b] := rfl
theorem vuseNums_cmpImm (sz : OperandSize) (a : Nat) (imm : Imm12) :
    vuseNums (.aluRRImm12 .subS sz .xzr (.vreg a .int) imm) = [a] := rfl
theorem vuseNums_cmpExt (sz : OperandSize) (a b : Nat) (e : ExtendOp) :
    vuseNums (.aluRRRExtend .subS sz .xzr (.vreg a .int) (.vreg b .int) e) = [a, b] := rfl

theorem setsFlags_cmpRR (sz : OperandSize) (a b : Nat) (ρ : Nat → CV) :
    SetsFlags (.aluRRR .subS sz .xzr (.vreg a .int) (.vreg b .int)) ρ
      (cmpFlags (opnd sz (ρ a)) (opnd sz (ρ b))) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

theorem setsFlags_cmpImm (sz : OperandSize) (a : Nat) {imm : Imm12} (hb : imm.bits < 4096)
    (ρ : Nat → CV) :
    SetsFlags (.aluRRImm12 .subS sz .xzr (.vreg a .int) imm) ρ
      (cmpFlags (opnd sz (ρ a)) (BitVec.ofNat sz.bits imm.value)) :=
  ⟨_, rfl, rfl, fun w => by
    show ispec _ [ρ a] w = _
    simp only [ispec, hb, ↓reduceIte, defOut, cmpFlags]⟩

theorem setsFlags_cmpExt (sz : OperandSize) (a b : Nat) (e : ExtendOp) (ρ : Nat → CV) :
    SetsFlags (.aluRRRExtend .subS sz .xzr (.vreg a .int) (.vreg b .int) e) ρ
      (cmpFlags (opnd sz (ρ a)) (Arm.extend_reg (opnd sz (ρ b)) (Arm.decode_reg_extend e.bits) 0)) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

theorem ofV_cmpRR32 (rn rm : Reg) :
    MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 0 [], .reg .xzr, .reg rn, .reg rm]) =
      some (.aluRRR .subS .size32 .xzr rn rm) := rfl
theorem ofV_cmpRR64 (rn rm : Reg) :
    MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 1 [], .reg .xzr, .reg rn, .reg rm]) =
      some (.aluRRR .subS .size64 .xzr rn rm) := rfl
theorem ofV_cmpImm32 (rn : Reg) (imm : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 10 [], .data 93 0 [], .reg .xzr, .reg rn, .op (.imm12 imm)]) =
      some (.aluRRImm12 .subS .size32 .xzr rn imm) := rfl
theorem ofV_cmpImm64 (rn : Reg) (imm : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 10 [], .data 93 1 [], .reg .xzr, .reg rn, .op (.imm12 imm)]) =
      some (.aluRRImm12 .subS .size64 .xzr rn imm) := rfl
theorem ofV_cmpExt_uxtb (rn rm : Reg) :
    MInst.ofV (.data 58 8 [.data 59 10 [], .data 93 0 [], .reg .xzr, .reg rn, .reg rm, .data 84 0 []]) =
      some (.aluRRRExtend .subS .size32 .xzr rn rm .uxtb) := rfl
theorem ofV_cmpExt_uxth (rn rm : Reg) :
    MInst.ofV (.data 58 8 [.data 59 10 [], .data 93 0 [], .reg .xzr, .reg rn, .reg rm, .data 84 1 []]) =
      some (.aluRRRExtend .subS .size32 .xzr rn rm .uxth) := rfl
theorem ofV_cmpExt_sxtb (rn rm : Reg) :
    MInst.ofV (.data 58 8 [.data 59 10 [], .data 93 0 [], .reg .xzr, .reg rn, .reg rm, .data 84 4 []]) =
      some (.aluRRRExtend .subS .size32 .xzr rn rm .sxtb) := rfl
theorem ofV_cmpExt_sxth (rn rm : Reg) :
    MInst.ofV (.data 58 8 [.data 59 10 [], .data 93 0 [], .reg .xzr, .reg rn, .reg rm, .data 84 5 []]) =
      some (.aluRRRExtend .subS .size32 .xzr rn rm .sxth) := rfl

/-! ## Values -/

theorem ofNat_toNat_self {w : Nat} (b : BitVec w) : BitVec.ofNat w b.toNat = b :=
  BitVec.eq_of_toNat_eq (by simp)

theorem cmp_rr_cond (cc : Clif.IntCC) {ty : Clif.Ty} {sz : OperandSize}
    (hs : (ty = .i32 ∧ sz = .size32) ∨ (ty = .i64 ∧ sz = .size64)) {a b : BitVec ty.width}
    {X Y : CV} (hx : VHolds ⟨ty, a⟩ X) (hy : VHolds ⟨ty, b⟩ Y) :
    condOn (condOf cc).bits (cmpFlags (opnd sz X) (opnd sz Y)) = Clif.Sem.intcc cc a b := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ha : opnd .size32 X = a := by rw [opnd32_setWidth]; exact hx
    have hb : opnd .size32 Y = b := by rw [opnd32_setWidth]; exact hy
    rw [ha, hb]; exact condOn_cmp_32 cc a b
  · rw [opnd64_vholds hx, opnd64_vholds hy]; exact condOn_cmp_64 cc a b

theorem cmp_imm_cond (cc : Clif.IntCC) {ty : Clif.Ty} {sz : OperandSize}
    (hs : (ty = .i32 ∧ sz = .size32) ∨ (ty = .i64 ∧ sz = .size64)) {a b : BitVec ty.width}
    {X : CV} (hx : VHolds ⟨ty, a⟩ X) :
    condOn (condOf cc).bits (cmpFlags (opnd sz X) (BitVec.ofNat sz.bits b.toNat)) =
      Clif.Sem.intcc cc a b := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ha : opnd .size32 X = a := by rw [opnd32_setWidth]; exact hx
    have hb : (BitVec.ofNat 32 b.toNat : BitVec 32) = b := ofNat_toNat_self b
    show condOn _ (cmpFlags (opnd .size32 X : BitVec 32) (BitVec.ofNat 32 b.toNat)) = _
    rw [ha, hb]; exact condOn_cmp_32 cc a b
  · have hb : (BitVec.ofNat 64 b.toNat : BitVec 64) = b := ofNat_toNat_self b
    show condOn _ (cmpFlags (opnd .size64 X : BitVec 64) (BitVec.ofNat 64 b.toNat)) = _
    rw [opnd64_vholds hx, hb]; exact condOn_cmp_64 cc a b

theorem ofNat_pred32 (b : BitVec 32) (hb : b.toNat % 2 = 1) :
    BitVec.ofNat 32 (b.toNat - 1) = b - 1 := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_ofNat, BitVec.toNat_sub, h1]
  omega

theorem ofNat_pred64 (b : BitVec 64) (hb : b.toNat % 2 = 1) :
    BitVec.ofNat 64 (b.toNat - 1) = b - 1 := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_ofNat, BitVec.toNat_sub, h1]
  omega

theorem cmp_pred_cond {cc : Clif.IntCC} {cd : Cond}
    (hcc : (cc = .uge ∧ cd = .hi) ∨ (cc = .sge ∧ cd = .gt)) {ty : Clif.Ty} {sz : OperandSize}
    (hs : (ty = .i32 ∧ sz = .size32) ∨ (ty = .i64 ∧ sz = .size64)) {a b : BitVec ty.width}
    {X : CV} (hx : VHolds ⟨ty, a⟩ X) (hodd : b.toNat % 2 = 1) :
    condOn cd.bits (cmpFlags (opnd sz X) (BitVec.ofNat sz.bits (b.toNat - 1))) =
      Clif.Sem.intcc cc a b := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change BitVec 32 at a b
    have ha : opnd .size32 X = a := by rw [opnd32_setWidth]; exact hx
    show condOn cd.bits (cmpFlags (opnd .size32 X) (BitVec.ofNat 32 (b.toNat - 1))) = _
    rw [ha, ofNat_pred32 b hodd]
    rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact condOn_hi_pred_32 a b (by rintro rfl; simp at hodd)
    · exact condOn_gt_pred_32 a b (by rintro rfl; revert hodd; decide)
  · change BitVec 64 at a b
    show condOn cd.bits (cmpFlags (opnd .size64 X) (BitVec.ofNat 64 (b.toNat - 1))) = _
    rw [opnd64_vholds hx, ofNat_pred64 b hodd]
    rcases hcc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact condOn_hi_pred_64 a b (by rintro rfl; simp at hodd)
    · exact condOn_gt_pred_64 a b (by rintro rfl; revert hodd; decide)

theorem narrow_cond (cc : Clif.IntCC) {sg : Bool} (hs : signedCC cc = sg) {ty : Clif.Ty}
    (hw : ty = .i8 ∨ ty = .i16) {a b : BitVec ty.width} {A B : BitVec 32}
    (hA : A = if sg then a.signExtend 32 else a.setWidth 32)
    (hB : B = if sg then b.signExtend 32 else b.setWidth 32) :
    condOn (condOf cc).bits (cmpFlags A B) = Clif.Sem.intcc cc a b := by
  rw [condOn_cmp_32]
  rcases hw with rfl | rfl <;> cases sg <;> simp only [Bool.false_eq_true, ↓reduceIte] at hA hB <;>
    subst hA hB
  · exact intcc_zeroExtend_8 cc hs a b
  · exact intcc_signExtend_8 cc hs a b
  · exact intcc_zeroExtend_16 cc hs a b
  · exact intcc_signExtend_16 cc hs a b

theorem decode_uxtb : Arm.decode_reg_extend ExtendOp.uxtb.bits = .UXTB := rfl
theorem decode_uxth : Arm.decode_reg_extend ExtendOp.uxth.bits = .UXTH := rfl
theorem decode_sxtb : Arm.decode_reg_extend ExtendOp.sxtb.bits = .SXTB := rfl
theorem decode_sxth : Arm.decode_reg_extend ExtendOp.sxth.bits = .SXTH := rfl

theorem extend_reg_uxtb (Y : CV) :
    Arm.extend_reg (opnd .size32 Y) (Arm.decode_reg_extend ExtendOp.uxtb.bits) 0 =
      (Y.setWidth 8).setWidth 32 := by
  rw [decode_uxtb]
  show (BitVec.setWidth 32 (BitVec.extractLsb' 0 8 (opnd .size32 Y))) <<< 0 = _
  simp only [opnd, lo64, OperandSize.bits]
  bv_decide

theorem extend_reg_uxth (Y : CV) :
    Arm.extend_reg (opnd .size32 Y) (Arm.decode_reg_extend ExtendOp.uxth.bits) 0 =
      (Y.setWidth 16).setWidth 32 := by
  rw [decode_uxth]
  show (BitVec.setWidth 32 (BitVec.extractLsb' 0 16 (opnd .size32 Y))) <<< 0 = _
  simp only [opnd, lo64, OperandSize.bits]
  bv_decide

theorem extend_reg_sxtb (Y : CV) :
    Arm.extend_reg (opnd .size32 Y) (Arm.decode_reg_extend ExtendOp.sxtb.bits) 0 =
      (Y.setWidth 8).signExtend 32 := by
  rw [decode_sxtb]
  show (BitVec.signExtend 32 (BitVec.extractLsb' 0 8 (opnd .size32 Y))) <<< 0 = _
  simp only [opnd, lo64, OperandSize.bits]
  bv_decide

theorem extend_reg_sxth (Y : CV) :
    Arm.extend_reg (opnd .size32 Y) (Arm.decode_reg_extend ExtendOp.sxth.bits) 0 =
      (Y.setWidth 16).signExtend 32 := by
  rw [decode_sxth]
  show (BitVec.signExtend 32 (BitVec.extractLsb' 0 16 (opnd .size32 Y))) <<< 0 = _
  simp only [opnd, lo64, OperandSize.bits]
  bv_decide

/-! ## The code of each `emit_icmp` rule -/

section Rules
variable {F : BitVec 64 → Prop} {isem : Sem} {f : Clif.Function} {ctx : Ctx}

theorem sz_3264 {t : CTy} {sv : V} (h3264 : (t.bits == 32 || t.bits == 64) = true)
    (hsz : (t.bits ≤ 32 ∧ sv = .data 93 0 []) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ sv = .data 93 1 [])) :
    (t.bits = 32 ∧ sv = .data 93 0 []) ∨ (t.bits = 64 ∧ sv = .data 93 1 []) := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h3264
  rcases hsz with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact .inl ⟨by omega, rfl⟩
  · exact .inr ⟨by omega, rfl⟩

theorem ty_of_bits {ty : Clif.Ty} {t : CTy} (ht : CTy.ofClif ty = t) {sz : OperandSize}
    (h : (t.bits = 32 ∧ sz = .size32) ∨ (t.bits = 64 ∧ sz = .size64)) :
    (ty = .i32 ∧ sz = .size32) ∨ (ty = .i64 ∧ sz = .size64) := by
  subst ht; rw [ofClif_bits] at h
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> cases ty <;> simp [Clif.Ty.width] at h ⊢

theorem ty_narrow {ty : Clif.Ty} {t : CTy} (ht : CTy.ofClif ty = t) (h : t.bits ≤ 16) :
    ty = .i8 ∨ ty = .i16 := by
  subst ht; rw [ofClif_bits] at h
  cases ty <;> simp [Clif.Ty.width] at h ⊢

theorem imm_lt {ty : Clif.Ty} (he : eTy ty = true) (imm : BitVec ty.width) : imm.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le imm.isLt (Nat.pow_le_pow_right (by omega) (eTy_width he))

theorem mem2 {u a b : Nat} (h : u ∈ [a, b]) : u = a ∨ u = b := by
  simpa using h

/-- Rule 2 (`cmp` of two 32/64-bit registers). -/
theorem emit_rr (hctx : CtxInv f ctx) {st : LState} (hvb : ValsBelow ctx st) (cc : Clif.IntCC)
    {x y : Nat} {rx ry : Reg} {t : CTy} {sv : V}
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry)
    (hT : ctx.valueType? y = some t) (h3264 : (t.bits == 32 || t.bits == 64) = true)
    (hsz : (t.bits ≤ 32 ∧ sv = .data 93 0 []) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ sv = .data 93 1 [])) :
    CondCode F isem ctx st st (.data 123 2 [.data 47 1 [.data 58 2 [.data 59 10 [], sv, .reg .xzr,
      .reg rx, .reg ry]], .data 96 (condOf cc).idx []]) (IcmpT cc x y) := by
  have := hctx.valueReg x _ hx; subst this
  have := hctx.valueReg y _ hy; subst this
  obtain ⟨sz, hsv, hofv⟩ : ∃ sz, ((t.bits = 32 ∧ sz = .size32) ∨ (t.bits = 64 ∧ sz = .size64)) ∧
      MInst.ofV (.data 58 2 [.data 59 10 [], sv, .reg .xzr, .reg (.vreg x .int), .reg (.vreg y .int)]) =
        some (.aluRRR .subS sz .xzr (.vreg x .int) (.vreg y .int)) := by
    rcases sz_3264 h3264 hsz with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact ⟨.size32, .inl ⟨h, rfl⟩, rfl⟩
    · exact ⟨.size64, .inr ⟨h, rfl⟩, rfl⟩
  refine CondCode.flag (ms := []) (Frag.nil _) hofv (condOf_ne_al cc) rfl ?_ ?_
  · intro u hu
    rw [vuseNums_cmpRR] at hu
    rcases mem2 hu with rfl | rfl
    · exact vreg_lt hvb hx
    · exact vreg_lt hvb hy
  · rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, rfl⟩
    refine ⟨UsesLo.nil _ _, fun u hu => ?_, fun w => Runs.nil ⟨_, setsFlags_cmpRR sz x y ρ, ?_⟩⟩
    · rw [vuseNums_cmpRR] at hu
      rcases mem2 hu with rfl | rfl
      · exact .inr (by simp [hxv])
      · exact .inr (by simp [hyv])
    · exact cmp_rr_cond cc (ty_of_bits (vholds_ty hdf hT hyv) hsv) (hh x _ hxv) (hh y _ hyv)

/-- Rule 6 (`cmp` of a 32/64-bit register with an `imm12` constant). -/
theorem emit_imm (hctx : CtxInv f ctx) {st : LState} (hvb : ValsBelow ctx st) (cc : Clif.IntCC)
    {x y j : Nat} {info : IInfo} {ity : Clif.Ty} {iimm : BitVec ity.width} {rx : Reg} {t : CTy}
    {sv : V} {imm : Imm12}
    (hx : ctx.valueReg? x = some rx) (hT : ctx.valueType? x = some t)
    (h3264 : (t.bits == 32 || t.bits == 64) = true)
    (hsz : (t.bits ≤ 32 ∧ sv = .data 93 0 []) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ sv = .data 93 1 []))
    (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.iconst ity iimm)) (hety : eTy ity = true)
    (himm : Imm12.ofNat? (u64 ((u64 (imm64OfIconst ity iimm) : Nat) : Int)) = some imm) :
    CondCode F isem ctx st st (.data 123 2 [.data 47 1 [.data 58 4 [.data 59 10 [], sv, .reg .xzr,
      .reg rx, .op (.imm12 imm)]], .data 96 (condOf cc).idx []]) (IcmpT cc x y) := by
  have := hctx.valueReg x _ hx; subst this
  rw [u64_iconst hety] at himm
  obtain ⟨hval, hbits⟩ := imm12_ofNat_value himm (imm_lt hety iimm)
  obtain ⟨sz, hsv, hofv⟩ : ∃ sz, ((t.bits = 32 ∧ sz = .size32) ∨ (t.bits = 64 ∧ sz = .size64)) ∧
      MInst.ofV (.data 58 4 [.data 59 10 [], sv, .reg .xzr, .reg (.vreg x .int), .op (.imm12 imm)]) =
        some (.aluRRImm12 .subS sz .xzr (.vreg x .int) imm) := by
    rcases sz_3264 h3264 hsz with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact ⟨.size32, .inl ⟨h, rfl⟩, rfl⟩
    · exact ⟨.size64, .inr ⟨h, rfl⟩, rfl⟩
  refine CondCode.flag (ms := []) (Frag.nil _) hofv (condOf_ne_al cc) rfl ?_ ?_
  · intro u hu
    rw [vuseNums_cmpImm, List.mem_singleton] at hu
    subst hu; exact vreg_lt hvb hx
  · rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, rfl⟩
    have hyc := iconst_val hdf hj hi hcl hyv
    cases hyc
    refine ⟨UsesLo.nil _ _, fun u hu => ?_, fun w => Runs.nil ⟨_, setsFlags_cmpImm sz x hbits ρ, ?_⟩⟩
    · rw [vuseNums_cmpImm, List.mem_singleton] at hu
      subst hu; exact .inr (by simp [hxv])
    · rw [hval]
      exact cmp_imm_cond cc (ty_of_bits (vholds_ty hdf hT hxv) hsv) (hh x _ hxv)

theorem u64_pred {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 64) : u64 ((n : Int) - 1) = n - 1 := by
  unfold u64; omega

/-- Rule 5 (`uge`/`sge` against an odd constant `b`: `cmp` with `b - 1`, `hi`/`gt`). -/
theorem emit_pred (hctx : CtxInv f ctx) {st : LState} (hvb : ValsBelow ctx st) {cc : Clif.IntCC}
    {cd : Cond} (hcc : (cc = .uge ∧ cd = .hi) ∨ (cc = .sge ∧ cd = .gt))
    {x y j : Nat} {info : IInfo} {ity : Clif.Ty} {iimm : BitVec ity.width} {rx : Reg} {t : CTy}
    {sv : V} {imm : Imm12}
    (hx : ctx.valueReg? x = some rx) (hT : ctx.valueType? x = some t)
    (h3264 : (t.bits == 32 || t.bits == 64) = true)
    (hsz : (t.bits ≤ 32 ∧ sv = .data 93 0 []) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ sv = .data 93 1 []))
    (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.iconst ity iimm)) (hety : eTy ity = true)
    (hodd : ((u64 (imm64OfIconst ity iimm) : Nat) : Int) % 2 = 1)
    (himm : Imm12.ofNat? (u64 ((u64 (((u64 (imm64OfIconst ity iimm) : Nat) : Int) - 1) : Nat) : Int)) =
      some imm) :
    CondCode F isem ctx st st (.data 123 2 [.data 47 1 [.data 58 4 [.data 59 10 [], sv, .reg .xzr,
      .reg rx, .op (.imm12 imm)]], .data 96 cd.idx []]) (IcmpT cc x y) := by
  have := hctx.valueReg x _ hx; subst this
  have hN : u64 (imm64OfIconst ity iimm) = iimm.toNat := u64_imm64OfIconst (eTy_width hety) iimm
  have hlt := imm_lt hety iimm
  rw [hN] at hodd himm
  have hodd' : iimm.toNat % 2 = 1 := by omega
  rw [u64_pred (by omega) hlt, u64_ofNat (by omega)] at himm
  obtain ⟨hval, hbits⟩ := imm12_ofNat_value himm (by omega)
  have hcd : cd ≠ .al ∧ cd ≠ .nv := by rcases hcc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨sz, hsv, hofv⟩ : ∃ sz, ((t.bits = 32 ∧ sz = .size32) ∨ (t.bits = 64 ∧ sz = .size64)) ∧
      MInst.ofV (.data 58 4 [.data 59 10 [], sv, .reg .xzr, .reg (.vreg x .int), .op (.imm12 imm)]) =
        some (.aluRRImm12 .subS sz .xzr (.vreg x .int) imm) := by
    rcases sz_3264 h3264 hsz with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact ⟨.size32, .inl ⟨h, rfl⟩, rfl⟩
    · exact ⟨.size64, .inr ⟨h, rfl⟩, rfl⟩
  refine CondCode.flag (ms := []) (Frag.nil _) hofv hcd rfl ?_ ?_
  · intro u hu
    rw [vuseNums_cmpImm, List.mem_singleton] at hu
    subst hu; exact vreg_lt hvb hx
  · rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, rfl⟩
    have hyc := iconst_val hdf hj hi hcl hyv
    cases hyc
    refine ⟨UsesLo.nil _ _, fun u hu => ?_, fun w => Runs.nil ⟨_, setsFlags_cmpImm sz x hbits ρ, ?_⟩⟩
    · rw [vuseNums_cmpImm, List.mem_singleton] at hu
      subst hu; exact .inr (by simp [hxv])
    · rw [hval]
      exact cmp_pred_cond hcc (ty_of_bits (vholds_ty hdf hT hxv) hsv) (hh x _ hxv) hodd'

/-- Rule 3 (8/16-bit, unsigned: `cmp` of the zero-extended register with an `imm12`). -/
theorem emit_narrow_imm (hR : Refines F isem) (hctx : CtxInv f ctx) {st st' : LState}
    (hvb : ValsBelow ctx st) {cc : Clif.IntCC} (hus : signedCC cc = false)
    {x y j : Nat} {info : IInfo} {ity : Clif.Ty} {iimm : BitVec ity.width} {vx : V} {t : CTy}
    {imm : Imm12}
    (hext : ExtOut ctx x false 32 [.int 32, .int 64] st st' vx) (hT : ctx.valueType? x = some t)
    (h16 : t.bits ≤ 16)
    (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.iconst ity iimm)) (hety : eTy ity = true)
    (himm : Imm12.ofNat? (u64 ((u64 (imm64OfIconst ity iimm) : Nat) : Int)) = some imm) :
    CondCode F isem ctx st st' (.data 123 2 [.data 47 1 [.data 58 4 [.data 59 10 [], .data 93 0 [],
      .reg .xzr, vx, .op (.imm12 imm)]], .data 96 (condOf cc).idx []]) (IcmpT cc x y) := by
  rw [u64_iconst hety] at himm
  obtain ⟨hval, hbits⟩ := imm12_ofNat_value himm (imm_lt hety iimm)
  obtain ⟨k, ms, rfl, hf, hk, hkx, hrun⟩ :=
    ExtOut.sem hR hctx hvb (.inl rfl) (by simp) (fun _ => by simp) hext
  refine CondCode.flag hf (ofV_cmpImm32 _ _) (condOf_ne_al cc) rfl ?_ ?_
  · intro u hu
    rw [vuseNums_cmpImm, List.mem_singleton] at hu
    subst hu; exact hk
  · rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, rfl⟩
    have hyc := iconst_val hdf hj hi hcl hyv
    cases hyc
    obtain ⟨hu, hr⟩ := hrun fr ρ _ hh hdf hxv
    refine ⟨hu, fun u hu' => ?_, fun w => (hr w).imp fun ρ' _ _ he =>
      ⟨_, setsFlags_cmpImm .size32 k hbits ρ', ?_⟩⟩
    · rw [vuseNums_cmpImm, List.mem_singleton] at hu'
      subst hu'
      rcases hkx with h | rfl
      · exact .inl h
      · exact .inr (by simp [hxv])
    · have hw : ity = .i8 ∨ ity = .i16 := ty_narrow (vholds_ty hdf hT hxv) h16
      have hw32 : ity.width ≤ 32 := by rcases hw with rfl | rfl <;> decide
      rw [hval]
      exact narrow_cond cc hus hw (he.2 hw32)
        (by simp only [Bool.false_eq_true, ↓reduceIte]
            exact BitVec.eq_of_toNat_eq (by simp [OperandSize.bits, BitVec.toNat_setWidth]))

/-- Rules 0/1 (8/16-bit: `cmp` of the extended register with the other register extended by the
compare, `sxt`/`uxt` `b`/`h`). -/
theorem emit_narrow_ext (hR : Refines F isem) (hctx : CtxInv f ctx) {st st' : LState}
    (hvb : ValsBelow ctx st) {cc : Clif.IntCC} {sg : Bool} (hsg : signedCC cc = sg)
    {x y : Nat} {vx ev : V} {ry : Reg} {t : CTy} {ai : Nat}
    (hext : ExtOut ctx x sg 32 [.int 32, .int 64] st st' vx) (hy : ctx.valueReg? y = some ry)
    (hT : ctx.valueType? y = some t) (hai : ai = if sg then 2 else 1)
    (hev : (t = .int 8 ∧ ai = 2 ∧ ev = .data 84 4 []) ∨ (t = .int 16 ∧ ai = 2 ∧ ev = .data 84 5 []) ∨
      (t = .int 8 ∧ ai = 1 ∧ ev = .data 84 0 []) ∨ (t = .int 16 ∧ ai = 1 ∧ ev = .data 84 1 [])) :
    CondCode F isem ctx st st' (.data 123 2 [.data 47 1 [.data 58 8 [.data 59 10 [], .data 93 0 [],
      .reg .xzr, vx, .reg ry, ev]], .data 96 (condOf cc).idx []]) (IcmpT cc x y) := by
  have := hctx.valueReg y _ hy; subst this
  obtain ⟨e, hofv, hesem, h16⟩ : ∃ e : ExtendOp, (∀ rn : Reg, MInst.ofV (.data 58 8 [.data 59 10 [],
      .data 93 0 [], .reg .xzr, .reg rn, .reg (.vreg y .int), ev]) =
        some (.aluRRRExtend .subS .size32 .xzr rn (.vreg y .int) e)) ∧
      (∀ (Y : CV) (ty : Clif.Ty) (b : BitVec ty.width), CTy.ofClif ty = t → VHolds ⟨ty, b⟩ Y →
        Arm.extend_reg (opnd .size32 Y) (Arm.decode_reg_extend e.bits) 0 =
          if sg then b.signExtend 32 else b.setWidth 32) ∧ t.bits ≤ 16 := by
    rcases hev with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      cases sg <;> simp at hai
    · refine ⟨.sxtb, fun _ => rfl, fun Y ty b ht hb => ?_, by decide⟩
      cases ty <;> simp [CTy.ofClif] at ht
      rw [extend_reg_sxtb]; simp only [VHolds, Clif.Ty.width] at hb; rw [hb]; rfl
    · refine ⟨.sxth, fun _ => rfl, fun Y ty b ht hb => ?_, by decide⟩
      cases ty <;> simp [CTy.ofClif] at ht
      rw [extend_reg_sxth]; simp only [VHolds, Clif.Ty.width] at hb; rw [hb]; rfl
    · refine ⟨.uxtb, fun _ => rfl, fun Y ty b ht hb => ?_, by decide⟩
      cases ty <;> simp [CTy.ofClif] at ht
      rw [extend_reg_uxtb]; simp only [VHolds, Clif.Ty.width] at hb; rw [hb]; rfl
    · refine ⟨.uxth, fun _ => rfl, fun Y ty b ht hb => ?_, by decide⟩
      cases ty <;> simp [CTy.ofClif] at ht
      rw [extend_reg_uxth]; simp only [VHolds, Clif.Ty.width] at hb; rw [hb]; rfl
  obtain ⟨k, ms, rfl, hf, hk, hkx, hrun⟩ :=
    ExtOut.sem hR hctx hvb (.inl rfl) (by simp) (fun _ => by simp) hext
  refine CondCode.flag hf (hofv (.vreg k .int)) (condOf_ne_al cc) rfl ?_ ?_
  · intro u hu
    rw [vuseNums_cmpExt] at hu
    rcases mem2 hu with rfl | rfl
    · exact hk
    · exact Nat.lt_of_lt_of_le (vreg_lt hvb hy) hf.mono
  · rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, rfl⟩
    obtain ⟨hu, hr⟩ := hrun fr ρ _ hh hdf hxv
    refine ⟨hu, fun u hu' => ?_, fun w => (hr w).imp fun ρ' w' hrun' he =>
      ⟨_, setsFlags_cmpExt .size32 k y e ρ', ?_⟩⟩
    · rw [vuseNums_cmpExt] at hu'
      rcases mem2 hu' with rfl | rfl
      · rcases hkx with h | rfl
        · exact .inl h
        · exact .inr (by simp [hxv])
      · exact .inr (by simp [hyv])
    · have ht := vholds_ty hdf hT hyv
      have hw := ty_narrow ht h16
      have hw32 : ty.width ≤ 32 := by rcases hw with rfl | rfl <;> decide
      have hy' : ρ' y = ρ y := hf.frame hrun' (vreg_lt hvb hy)
      exact narrow_cond cc hsg hw (he.2 hw32) (by rw [hy']; exact hesem _ _ _ ht (hh y _ hyv))

theorem beq_zero_comm {w : Nat} (b : BitVec w) : (0#w == b) = (b == 0#w) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩)

/-- Rules 7/8 with `ne`: `is_nonzero` of the operand compared with the constant 0. -/
theorem emit_zero_ne {st st' : LState} {c : V} {cc : Clif.IntCC} (hcc : cc = .ne)
    {x y z v j : Nat} {info : IInfo} {ity : Clif.Ty} {iimm : BitVec ity.width}
    (hz0 : ((u64 (imm64OfIconst ity iimm) : Nat) : Int) = 0) (hety : eTy ity = true)
    (hj : ctx.defInst? z = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.iconst ity iimm)) (hzv : (x = z ∧ y = v) ∨ (x = v ∧ y = z))
    (h : CondCode F isem ctx st st' c (fun fr b => ∃ w, fr.regs v = some w ∧ b = Clif.Sem.truthy w.bits)) :
    CondCode F isem ctx st st' c (IcmpT cc x y) := by
  subst hcc
  have hz : iimm = 0 := by
    have := u64_imm64OfIconst (eTy_width hety) iimm
    apply BitVec.eq_of_toNat_eq; simp; omega
  subst hz
  refine h.weaken ?_
  rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, rfl⟩
  rcases hzv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hc := iconst_val hdf hj hi hcl hxv
    cases hc
    exact ⟨_, hyv, by simp [Clif.Sem.intcc, Clif.Sem.truthy, bne, beq_zero_comm]⟩
  · have hc := iconst_val hdf hj hi hcl hyv
    cases hc
    exact ⟨_, hxv, by simp [Clif.Sem.intcc, Clif.Sem.truthy]⟩

/-- Rules 7/8 with `eq`: the inverted `is_nonzero`. -/
theorem emit_zero_eq {st st' : LState} {c : V} {cc : Clif.IntCC} (hcc : cc = .eq)
    {x y z v j : Nat} {info : IInfo} {ity : Clif.Ty} {iimm : BitVec ity.width}
    (hz0 : ((u64 (imm64OfIconst ity iimm) : Nat) : Int) = 0) (hety : eTy ity = true)
    (hj : ctx.defInst? z = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.iconst ity iimm)) (hzv : (x = z ∧ y = v) ∨ (x = v ∧ y = z))
    (h : CondCode F isem ctx st st' c
      (fun fr b => ∃ w, fr.regs v = some w ∧ (!b) = Clif.Sem.truthy w.bits)) :
    CondCode F isem ctx st st' c (IcmpT cc x y) := by
  subst hcc
  have hz : iimm = 0 := by
    have := u64_imm64OfIconst (eTy_width hety) iimm
    apply BitVec.eq_of_toNat_eq; simp; omega
  subst hz
  refine h.weaken ?_
  rintro fr ρ b hh hdf ⟨ty, a, b', hxv, hyv, rfl⟩
  rcases hzv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hc := iconst_val hdf hj hi hcl hxv
    cases hc
    exact ⟨_, hyv, by simp [Clif.Sem.intcc, Clif.Sem.truthy, bne, beq_zero_comm]⟩
  · have hc := iconst_val hdf hj hi hcl hyv
    cases hc
    exact ⟨_, hxv, by simp [Clif.Sem.intcc, Clif.Sem.truthy, bne]⟩

end Rules

/-! ## The contracts -/

/-- Close a lowering-state equation left by inversion (chains of `s.1 = s'.1` facts). -/
macro "icmp_st" : tactic => `(tactic| first | rfl | (simp only [*]; done) | (simp_all; done))

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`lower_extend_op`** at `i8`/`i16`: `sxtb`/`sxth`/`uxtb`/`uxth`. -/
theorem lower_extend_op_ok {n : Nat} (hn : 40 ≤ n) {t : CTy} {ai : Nat}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 84 657 [.ty t, .data 56 ai []] s v s') :
    s'.1 = s.1 ∧ ((t = .int 8 ∧ ai = 2 ∧ v = .data 84 4 []) ∨ (t = .int 16 ∧ ai = 2 ∧ v = .data 84 5 []) ∨
      (t = .int 8 ∧ ai = 1 ∧ v = .data 84 0 []) ∨ (t = .int 16 ∧ ai = 1 ∧ v = .data 84 1 [])) := by
  isel_split' hp hc h 657
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  all_goals simp_all

set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`emit_icmp`** on integer values: the condition is `intcc cc a b` of the operands' values. -/
theorem emit_icmp_ok {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {f : Clif.Function}
    (hctx : CtxInv f ctx) {n : Nat} (hn : 200 ≤ n) {cc : Clif.IntCC} {x y : Nat}
    {s s' : LState × Array RuleId} {c : V} (hvb : ValsBelow ctx s.1)
    (h : ApplyInternal p (sem ctx) cfg n 123 652 [.data 145 (ccIdx cc) [], .value x, .value y] s c s') :
    CondCode F isem ctx s.1 s'.1 c (IcmpT cc x y) := by
  isel_split' hp hc h 652
  all_goals (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [ctor_signed_cond_code_iff, ctor_unsigned_cond_code_iff, ctor_u64_is_odd_iff,
    ctor_u64_wrapping_sub_iff, ctor_put_in_regs_iff, V.intcc?_data, some_bind_ccIdx,
    Int.toNat_one, Int.toNat_zero, List.getElem?_cons_succ, List.getElem?_nil] at hm he
  all_goals try (isel_opcode_absurd hctx; done)
  all_goals isel_call hp hc [operand_size_ok, cmp_ok, cmp_imm_ok, cmp_extend_ok, zext32_ok, sext32_ok,
    lower_extend_op_ok]
  all_goals try (
    obtain ⟨ity, iimm, rfl, hety, hcl⟩ := iconst_data_inv hctx ‹_› ‹_› ‹V.data 152 35 [V.data 151 57 [], _] = _›
    isel_inv_simp [ctor_u64_is_odd_iff, ctor_u64_wrapping_sub_iff] at *
    isel_destruct
    subst_vars
    try (isel_inv_simp [ctor_u64_is_odd_iff, ctor_u64_wrapping_sub_iff] at *
         isel_destruct
         subst_vars))
  all_goals try (dsimp only at *)
  all_goals first
    | (refine (emit_narrow_ext hR hctx hvb (signed_of_idx ‹_›) ‹ExtOut _ _ true _ _ _ _ _› ‹_› ‹_› rfl
        ‹_›).st_eq ?_; icmp_st)
    | (refine (emit_narrow_ext hR hctx hvb (unsigned_of_idx ‹_›) ‹ExtOut _ _ false _ _ _ _ _› ‹_› ‹_› rfl
        ‹_›).st_eq ?_; icmp_st)
    | (refine (emit_rr hctx hvb cc ‹ctx.valueReg? x = _› ‹ctx.valueReg? y = _› ‹_› ‹_› ‹_›).st_eq ?_
       icmp_st)
    | (refine (emit_narrow_imm hR hctx hvb (unsigned_of_idx ‹_›) ‹ExtOut _ _ false _ _ _ _ _› ‹_› ‹_›
        ‹_› ‹_› ‹_› ‹_› ‹_›).st_eq ?_; icmp_st)
    | (refine (emit_imm hctx hvb cc ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).st_eq ?_; icmp_st)
    | (exact emit_zero_ne (ccIdx_eq_1 ‹_›) (by omega) hety ‹_› ‹_› hcl (.inl ⟨rfl, rfl⟩)
        (by
          obtain ⟨h651⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 651 _ _ _ _) := ⟨‹_›⟩
          exact is_nonzero_ok hp hc hR hctx (hn := by omega) hvb h651))
    | (exact emit_zero_ne (ccIdx_eq_1 ‹_›) (by omega) hety ‹_› ‹_› hcl (.inr ⟨rfl, rfl⟩)
        (by
          obtain ⟨h651⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 651 _ _ _ _) := ⟨‹_›⟩
          exact is_nonzero_ok hp hc hR hctx (hn := by omega) hvb h651))
    | (obtain ⟨h651⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 651 _ _ _ _) := ⟨‹_›⟩
       obtain ⟨h649⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 649 _ _ _ _) := ⟨‹_›⟩
       have hnz := is_nonzero_ok hp hc hR hctx (hn := by omega) hvb h651
       obtain ⟨hst, hinv⟩ := cri_ok hp hc (hn := by omega) hnz.shape h649
       first
        | exact (emit_zero_eq (ccIdx_eq_0 ‹_›) (by omega) hety ‹_› ‹_› hcl (.inl ⟨rfl, rfl⟩)
            (hnz.inv hinv)).st_eq hst
        | exact (emit_zero_eq (ccIdx_eq_0 ‹_›) (by omega) hety ‹_› ‹_› hcl (.inr ⟨rfl, rfl⟩)
            (hnz.inv hinv)).st_eq hst)
    | (isel_inv_simp [] at *
       isel_destruct
       subst_vars
       have hodd : ((u64 (imm64OfIconst ity iimm) : Nat) : Int) % 2 = 1 := by
         have h := ‹V.bool true = _›; simp at h; omega
       first
        | (refine (emit_pred hctx hvb (cd := .hi) (.inl ⟨ccIdx_eq_7 ‹_›, rfl⟩) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
            hcl hety hodd ‹_›).st_eq ?_; icmp_st)
        | (refine (emit_pred hctx hvb (cd := .gt) (.inr ⟨ccIdx_eq_3 ‹_›, rfl⟩) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
            hcl hety hodd ‹_›).st_eq ?_; icmp_st))

end

end Backend.Proof

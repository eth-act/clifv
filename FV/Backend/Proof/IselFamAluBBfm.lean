import FV.Backend.Proof.IselFamAluBNotShift

/-!
# Family B: `sbfm`/`ubfm` (`lower.isle:1704`/`1707`)

`(sshr/ushr (ty_32_or_64 ty) (ishl x (u64_from_iconst a)) (u64_from_iconst b))` →
`(bitfield_move ty (BfmOp.SBfm/UBfm) x (bfm_immr ty a b) (bfm_imms ty a b))`: one `sbfm`/`ubfm`.
The root operand `ishl` and both constants are looked through (`DFGCons`); the emitted code reads
the `ishl`'s operand, not the root's, so the template `shift_ruleOk_uses` takes the read values
from the right-hand side. `bfm_sshr`/`bfm_ushr`: the bitfield move with these immediates is the
shift pair.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The bitfield move of the shift pair -/

theorem bfm_ushr {w : Nat} (x : BitVec w) {a b : Nat} (ha : a < w) (hb : b < w) :
    bfmVal .uBfm x (if a ≤ b then b - a else w - (a - b)) (w - 1 - a) = (x <<< a) >>> b := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  by_cases hab : a ≤ b
  · have h1 : b - a ≤ w - 1 - a := by omega
    simp only [bfmVal, hab, ↓reduceIte, h1]
    simp [BitVec.getElem_setWidth, BitVec.getElem_ushiftRight, hab]
    rw [show b - a + i = b + i - a by omega]
    by_cases h : b + i < w
    · simp [h, show i < w - 1 - a - (b - a) + 1 by omega, show ¬ b + i < a by omega]
    · simp [h, show ¬ i < w - 1 - a - (b - a) + 1 by omega]
  · have h1 : ¬ w - (a - b) ≤ w - 1 - a := by omega
    simp only [bfmVal, hab, ↓reduceIte, h1]
    simp [BitVec.getElem_setWidth, BitVec.getElem_ushiftRight]
    rw [show w - (w - (a - b)) = a - b by omega]
    by_cases h : i < a - b
    · simp [h, show b + i < a by omega]
    · rw [show i - (a - b) = b + i - a by omega]
      by_cases h2 : b + i < w
      · simp [h, h2, show ¬ b + i < a by omega, show b + i - a < w - 1 - a + 1 by omega]
      · simp [h, h2, show ¬ b + i - a < w - 1 - a + 1 by omega]

theorem bfm_sshr {w : Nat} (x : BitVec w) {a b : Nat} (ha : a < w) (hb : b < w) :
    bfmVal .sBfm x (if a ≤ b then b - a else w - (a - b)) (w - 1 - a) = (x <<< a).sshiftRight b := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  by_cases hab : a ≤ b
  · have h1 : b - a ≤ w - 1 - a := by omega
    simp only [bfmVal, hab, ↓reduceIte, h1]
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_signExtend, BitVec.getLsbD_sshiftRight,
      BitVec.getLsbD_shiftLeft, hab, ↓reduceIte, BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    rw [show b - a + (w - 1 - a - (b - a) + 1 - 1) = w - 1 - a by omega,
      show b - a + i = b + i - a by omega]
    by_cases h : b + i < w
    · simp [h, hi, show i < w - 1 - a - (b - a) + 1 by omega, show ¬ b + i < a by omega]
    · simp [h, hi, show ¬ i < w - 1 - a - (b - a) + 1 by omega, show ¬ w - 1 < a by omega,
        show ¬ w ≤ i by omega, show w - 1 < w by omega]
  · have h1 : ¬ w - (a - b) ≤ w - 1 - a := by omega
    simp only [bfmVal, hab, ↓reduceIte, h1]
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_signExtend, BitVec.getLsbD_sshiftRight,
      BitVec.getLsbD_shiftLeft, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
    rw [show w - (w - (a - b)) = a - b by omega, show w - 1 - a + 1 - 1 = w - 1 - a by omega]
    by_cases h : i < a - b
    · simp [h, hi, show b + i < w by omega, show b + i < a by omega]
    · rw [show i - (a - b) = b + i - a by omega]
      by_cases h2 : b + i < w
      · simp [h, h2, hi, show ¬ b + i < a by omega, show b + i - a < w - 1 - a + 1 by omega,
          show b + i - a < w by omega]
      · simp [h, h2, hi, show ¬ b + i - a < w - 1 - a + 1 by omega, show ¬ w - 1 < a by omega,
          show ¬ w ≤ i by omega, show w - 1 < w by omega, show b + i - a < w by omega]

/-- The result of the emitted `sbfm`, at the operand size. -/
theorem bfm_fin_s (sz : OperandSize) (X : CV) {a b : Nat} (ha : a < sz.bits) (hb : b < sz.bits) :
    (resX sz (bfmVal .sBfm (opnd sz X) (if a ≤ b then b - a else sz.bits - (a - b))
      (sz.bits - 1 - a))).setWidth sz.bits = ((X.setWidth sz.bits) <<< a).sshiftRight b := by
  rw [setWidth_opnd_self, opnd_resX, bfm_sshr _ ha hb, setWidth_opnd_self]

/-- The result of the emitted `ubfm`, at the operand size. -/
theorem bfm_fin_u (sz : OperandSize) (X : CV) {a b : Nat} (ha : a < sz.bits) (hb : b < sz.bits) :
    (resX sz (bfmVal .uBfm (opnd sz X) (if a ≤ b then b - a else sz.bits - (a - b))
      (sz.bits - 1 - a))).setWidth sz.bits = ((X.setWidth sz.bits) <<< a) >>> b := by
  rw [setWidth_opnd_self, opnd_resX, bfm_ushr _ ha hb, setWidth_opnd_self]

theorem u64_toNat_fb {ty : Clif.Ty} (hw : ty.width ≤ 64) (imm : BitVec ty.width) :
    u64 (imm.toNat : Int) = imm.toNat := by
  have hlt := imm.isLt
  have : imm.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hw)
  unfold u64; omega

theorem immr_lt {w a b : Nat} (ha : a < w) (hb : b < w) :
    (if a ≤ b then b - a else w - (a - b)) < w := by
  split <;> omega

theorem land_mod256 {w : Nat} (hw : IW w) (c : Nat) : Nat.land (c % 256) (w - 1) = c % w := by
  rw [land_mask_mod hw, Nat.mod_mod_of_dvd _ (hw.dvd (show 6 ≤ 8 by omega))]

theorem ispec_bfm_fb {sz : OperandSize} {op : BfmOp} {d : Nat} {rn : Reg} {r s : Nat}
    (hr : r < sz.bits) (hs : s < sz.bits) {a : CV} {w : Arm.ArmState} :
    ispec (.bitfieldMove sz op (.vreg d .int) rn r s) [a] w =
      some ([resX sz (bfmVal op (opnd sz a) r s)], w, .next) := by
  simp only [ispec, hr, hs, and_self, ↓reduceIte]; rfl

/-! ## Extern constructors and `bitfield_move` -/

section Ctor
variable (ctx : Ctx) (st : LState)

theorem ctor_temp_writable_reg_int_iff (w : Nat) (v : V) (st' : LState) :
    externCtor ctx T.temp_writable_reg [.ty (.int w)] st = .ok (v, st') ↔
      w ≤ 64 ∧ v = .reg (st.fresh .int).1 ∧ st' = (st.fresh .int).2 := by
  have : externCtor ctx T.temp_writable_reg [.ty (.int w)] st =
    match (CTy.int w).regClass? with
    | some cls => let (r, st) := st.fresh cls; .ok (.reg r, st)
    | none => .unmodeled s!"temp_writable_reg of {repr (CTy.int w)}" := rfl
  rw [this]
  by_cases hw : w ≤ 64
  · simp only [CTy.regClass?, hw, ↓reduceIte, true_and]
    constructor
    · intro h; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; rfl
  · simp [CTy.regClass?, hw]

/-- `bfm_immr ty a b` (`w = 32/64`): the rotate amount of the shift pair. -/
def bfmImmr (w a b : Nat) : Nat :=
  if Nat.land (a % 256) (w - 1) ≤ Nat.land (b % 256) (w - 1) then
    Nat.land (b % 256) (w - 1) - Nat.land (a % 256) (w - 1)
  else w - (Nat.land (a % 256) (w - 1) - Nat.land (b % 256) (w - 1))

theorem ctor_bfm_immr_iff (w : Nat) (a b : Int) (v : V) (st' : LState) :
    externCtor ctx T.bfm_immr [.ty (.int w), .int a, .int b] st = .ok (v, st') ↔
      v = .op (.uimm6 (bfmImmr w (u64 a) (u64 b))) ∧ st' = st := by
  have : externCtor ctx T.bfm_immr [.ty (.int w), .int a, .int b] st =
    .ok (.op (.uimm6 (bfmImmr (CTy.int w).laneBits (u64 a) (u64 b))), st) := rfl
  rw [this]; simp only [CTy.laneBits]; simp [eq_comm]

theorem ctor_bfm_imms_iff (w : Nat) (a b : Int) (v : V) (st' : LState) :
    externCtor ctx T.bfm_imms [.ty (.int w), .int a, .int b] st = .ok (v, st') ↔
      v = .op (.uimm6 (w - 1 - Nat.land (u64 a % 256) (w - 1))) ∧ st' = st := by
  have : externCtor ctx T.bfm_imms [.ty (.int w), .int a, .int b] st =
    .ok (.op (.uimm6 ((CTy.int w).laneBits - 1 - Nat.land (u64 a % 256) ((CTy.int w).laneBits - 1))),
      st) := rfl
  rw [this]; simp only [CTy.laneBits]; simp [eq_comm]

end Ctor

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem bitfield_move_ok {n : Nat} (hn : 40 ≤ n) {w : Nat} {op a r s : V}
    {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 418 [.ty (.int w), op, a, r, s] st v st') :
    ∃ ks, OSz (.int w) ks ∧
      EmitOut st.1 st'.1 v (fun rd => .data 58 29 [.data 93 ks [], op, .reg rd, a, r, s]) := by
  have hp' := hp
  isel_split hp hc h 418
  isel_inv [*, rule_inst_2999, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  have ht := ‹externCtor ctx T.temp_writable_reg _ _ = _›
  obtain ⟨-, rfl, rfl⟩ := (ctor_temp_writable_reg_int_iff ctx _ _ _ _).mp ht
  have hsz := ‹ApplyInternal _ _ _ _ 93 305 _ _ _ _›
  obtain ⟨hs, hk⟩ := operand_size_ok hp' hc (by omega) hsz
  simp only at hs
  rcases hk with ⟨hb, rfl⟩ | ⟨hb, hb', rfl⟩
  · exact ⟨0, .inl ⟨hb, rfl⟩, rfl, _, ‹_›, by rw [hs]⟩
  · exact ⟨1, .inr ⟨hb, hb', rfl⟩, rfl, _, ‹_›, by rw [hs]⟩

theorem ofV_bitfieldMove_fb {ks : Nat} {sz : OperandSize} {opv : V} {bop : BfmOp}
    (hs : OperandSize.ofIdx? ks = some sz) (hop : opv.bfmOp? = some bop) (rd rn : Reg) (i j : Nat) :
    MInst.ofV (.data 58 29 [.data 93 ks [], opv, .reg rd, .reg rn, .op (.uimm6 i), .op (.uimm6 j)]) =
      some (.bitfieldMove sz bop rd rn i j) := by
  have e1 : MInst.ofV (.data 58 29 [.data 93 ks [], opv, .reg rd, .reg rn, .op (.uimm6 i),
      .op (.uimm6 j)]) = (do
        return .bitfieldMove (← (V.data 93 ks []).size?) (← opv.bfmOp?) rd rn i j) := rfl
  rw [e1]
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e3, hs, hop]
  rfl

/-! ## Template: a shift root rule whose code reads looked-through values -/

/-- As `shift_ruleOk_gen`, but the code may read any values `xs` the right-hand side names,
provided they are defined in every frame the instruction runs in. -/
theorem shift_ruleOk_uses {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp} {n : String}
    (hshift : cop.isShift = true)
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hMR : MRStable F MR)
    (hrhs : ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ∀ (cfg : Config) ii (info : IInfo)
      x y w (st : LState) tr m n env' s1 v s', cfg.checkOverlap = false → ValsBelow ctx st →
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) →
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] →
      (w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) →
      (matchRule p (sem ctx) cfg (m + 10) r [.inst ii]).run (st, tr) = .ok (some env', s1) →
      (evalExpr p (sem ctx) cfg (n + 200) r.rhs env').run s1 = .ok (some v, s') →
      ∃ ms d xs, v = .regsVec [[.vreg d .int]] ∧ CodeShapeU st s'.1 ms d xs ∧
        ∀ (ty : Clif.Ty), ty.width = w → eTy ty = true →
        ∀ (fr : Clif.Frame) (ρ : Nat → CV) (u : BitVec ty.width) (yv : Clif.Val) (res : BitVec ty.width),
          fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → fr.regs x = some ⟨ty, u⟩ →
          fr.regs y = some yv → Clif.Sem.shift cop u yv.bits = some res →
          (∀ z ∈ xs, (fr.regs z).isSome) ∧ ∃ ρ', PRun F isem ms ρ ρ' ∧ VHolds ⟨ty, res⟩ (ρ' d)) :
    LowerRuleOk isem MR env cp p r := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb hfirst
    hmatch' heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, y, rfl, hety, hd, hhead⟩ :=
    binary_front hp hargs hto hko hname hcop hctx hi hc (m := m' + 9) hmatch'
  have hws : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    cases ty <;> simp [eTy, Clif.Ty.width] at hety ⊢
  obtain ⟨ms, d, xs, rfl, hsh, hsem⟩ :=
    hrhs f ctx hctx cfg ii info x y ty.width st tr m' n' env' s1 out (st', tr') hco hvb hi hhead hd
      hws hmatch' heval
  refine ⟨ms, _, hsh.emitted, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' hf hvals hdfg ho
  obtain ⟨u, yv, res, hu, hy, hres, rfl, rfl⟩ := evalInst_shift_ok hshift ho
  have hxv := getAs_ok hu
  obtain ⟨hxs, ρ', hrun, hheld⟩ := hsem ty rfl hety fr ρ u yv res hf hvals hdfg hxv hy hres
  exact ⟨rfl, usesOk_of xs hsh.uses hxs, .inl hsh.res, _, ρ', rfl, hrun, hheld⟩

end Terms

section Rules
variable {F : BitVec 64 → Prop} {isem : Sem}

set_option maxHeartbeats 1000000 in
/-- **`sbfm`** (`lower.isle:1704`), i32/i64. -/
theorem sbfm_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1704 := by
  refine shift_ruleOk_uses hp (cop := .sshr) rfl rfl hp.t2389 term_2389_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info z y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1704] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
  subst hdat
  have h3264 : w = 32 ∨ w = 64 := by
    have := ‹(w == 32 || w == 64) = true›
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  -- root operands
  have hva := ‹externExtract ctx T.value_array_2 (.values [z, y]) _ = _›
  simp only [ext_value_array_2_iff, List.cons.injEq, and_true] at hva
  obtain ⟨rfl, rfl⟩ := hva
  obtain ⟨jz, hjz, hl⟩ := (ext_def_inst_iff ctx st _ _).mp ‹externExtract ctx T.def_inst (.value z) _ = _›
  simp only [List.cons.injEq, and_true] at hl
  subst hl
  obtain ⟨jy, hjy, hl⟩ := (ext_def_inst_iff ctx st _ _).mp ‹externExtract ctx T.def_inst (.value y) _ = _›
  simp only [List.cons.injEq, and_true] at hl
  subst hl
  obtain ⟨infoz, hiz, hfz⟩ :=
    (ext_inst_data_value_iff ctx st _ _).mp ‹externExtract ctx T.inst_data_value (.inst jz) _ = _›
  simp only [List.cons.injEq, and_true] at hfz
  obtain ⟨-, hdz0⟩ := hfz
  obtain ⟨infoy, hiy, hfy⟩ :=
    (ext_inst_data_value_iff ctx st _ _).mp ‹externExtract ctx T.inst_data_value (.inst jy) _ = _›
  simp only [List.cons.injEq, and_true] at hfy
  obtain ⟨-, hdy⟩ := hfy
  -- the looked-through `ishl`
  obtain ⟨clz, hclz⟩ := Option.isSome_iff_exists.mp (hctx.defClif z _ _ hjz hiz)
  have hdz := hctx.data _ _ clz hiz hclz
  rw [← hdz0] at hdz
  obtain ⟨hf, ho⟩ := instData_inv_names hdz
  rw [variantNames_Binary] at hf
  rw [variantNames_Ishl_fb] at ho
  have hnm : instNames clz = ("Binary", "Ishl") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty1, x, ya, rfl⟩ := instNames_binary (cop := .ishl) rfl hnm
  obtain ⟨-, hfs⟩ := instData_binary_data rfl hdz
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  have hva2 := ‹externExtract ctx T.value_array_2 (.values [x, ya]) _ = _›
  simp only [ext_value_array_2_iff, List.cons.injEq, and_true] at hva2
  obtain ⟨rfl, rfl⟩ := hva2
  obtain ⟨ja, hja, hl⟩ :=
    (ext_def_inst_iff ctx st _ _).mp ‹externExtract ctx T.def_inst (.value ya) _ = _›
  simp only [List.cons.injEq, and_true] at hl
  subst hl
  obtain ⟨infoa, hia, hfa⟩ :=
    (ext_inst_data_value_iff ctx st _ _).mp ‹externExtract ctx T.inst_data_value (.inst ja) _ = _›
  simp only [List.cons.injEq, and_true] at hfa
  obtain ⟨-, hda⟩ := hfa
  -- the two constants
  obtain ⟨tyb, immb, hclb, hfb⟩ := defInst_iconst_clif ctx hctx hjy hiy hdy.symm
  simp only [List.cons.injEq, and_true] at hfb
  subst hfb
  obtain ⟨tya, imma, hcla, hfa'⟩ := defInst_iconst_clif ctx hctx hja hia hda.symm
  simp only [List.cons.injEq, and_true] at hfa'
  subst hfa'
  have hetyb : eTy tyb = true := by
    have hdat := hctx.data _ _ _ hiy hclb
    rw [← hdy] at hdat
    exact (fb_instData_iconst hdat).1
  have hetya : eTy tya = true := by
    have hdat := hctx.data _ _ _ hia hcla
    rw [← hda] at hdat
    exact (fb_instData_iconst hdat).1
  have hub := ‹externExtract ctx T.u64_from_imm64 (.int (imm64OfIconst tyb immb)) _ = _›
  rw [ext_u64_from_imm64_iff, u64_imm64OfIconst_fb (eTy_width hetyb)] at hub
  simp only [List.cons.injEq, and_true] at hub
  subst hub
  have hua := ‹externExtract ctx T.u64_from_imm64 (.int (imm64OfIconst tya imma)) _ = _›
  rw [ext_u64_from_imm64_iff, u64_imm64OfIconst_fb (eTy_width hetya)] at hua
  simp only [List.cons.injEq, and_true] at hua
  subst hua
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_reg [.value x] _ = _›
  obtain rfl := hctx.valueReg x _ hrx
  obtain ⟨rfl, rfl⟩ :=
    (ctor_bfm_immr_iff ctx _ _ _ _ _ _).mp ‹externCtor ctx T.bfm_immr _ _ = _›
  obtain ⟨rfl, rfl⟩ :=
    (ctor_bfm_imms_iff ctx _ _ _ _ _ _).mp ‹externCtor ctx T.bfm_imms _ _ = _›
  have hW : IW w := by rcases h3264 with rfl | rfl <;> simp [IW]
  simp only [u64_toNat_fb (eTy_width hetya), u64_toNat_fb (eTy_width hetyb), bfmImmr,
    land_mod256 hW] at *
  have hA := ‹ApplyInternal _ _ _ _ 27 418 _ _ _ _›
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := bitfield_move_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_bitfieldMove_fb (hks.ofIdx hW) (rfl : (V.data 62 1 []).bfmOp? = some .sBfm)] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  rename LState => st0
  refine ⟨_, _, rfl, [x], by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by rw [show vuseNums _ = [x] from rfl] at hu; exact hu), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hz hy hres
  obtain ⟨vals', hev, hlk⟩ := hdfg.1 z _ _ _ _ hjz hiz hclz rfl hz
  obtain ⟨u1, yva, r, hu1, hyva, hr, rfl, -⟩ :=
    evalInst_shift_ok (rfl : Clif.BinaryOp.ishl.isShift = true) (hev default)
  have hv := lookup_zip_single_fb hlk
  cases hv
  have e1 := dfg_iconst_fb hdfg hja hia hcla hyva
  subst e1
  have e2 := dfg_iconst_fb hdfg hjy hiy hclb hy
  subst e2
  refine ⟨by simp [getAs_ok hu1], ?_⟩
  subst hty
  simp only [Clif.Sem.shift, Clif.Sem.ishl, Clif.Sem.sshr, Clif.Sem.shiftAmt, Option.some.injEq]
    at hr hres
  subst hr
  subst hres
  have hX : (ρ x).setWidth ty1.width = u1 := hvals x _ (getAs_ok hu1)
  cases ty1 <;> simp [Clif.Ty.width] at h3264
  · have ha := Nat.mod_lt imma.toNat (show 0 < 32 by decide)
    have hb := Nat.mod_lt immb.toNat (show 0 < 32 by decide)
    refine ⟨_, prun_rr hR rfl (fun w => ispec_bfm_fb (sz := .size32)
      (immr_lt ha hb)
      (by simp only [Clif.Ty.width, OperandSize.bits]; omega)) (prun_nil _), ?_⟩
    simp only [VHolds, upd_same]
    rw [← hX]
    exact bfm_fin_s .size32 (ρ x) ha hb
  · have ha := Nat.mod_lt imma.toNat (show 0 < 64 by decide)
    have hb := Nat.mod_lt immb.toNat (show 0 < 64 by decide)
    refine ⟨_, prun_rr hR rfl (fun w => ispec_bfm_fb (sz := .size64)
      (immr_lt ha hb)
      (by simp only [Clif.Ty.width, OperandSize.bits]; omega)) (prun_nil _), ?_⟩
    simp only [VHolds, upd_same]
    rw [← hX]
    exact bfm_fin_s .size64 (ρ x) ha hb

set_option maxHeartbeats 1000000 in
/-- **`ubfm`** (`lower.isle:1707`), i32/i64. -/
theorem ubfm_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1707 := by
  refine shift_ruleOk_uses hp (cop := .ushr) rfl rfl hp.t2388 term_2388_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info z y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1707] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
  subst hdat
  have h3264 : w = 32 ∨ w = 64 := by
    have := ‹(w == 32 || w == 64) = true›
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  -- root operands
  have hva := ‹externExtract ctx T.value_array_2 (.values [z, y]) _ = _›
  simp only [ext_value_array_2_iff, List.cons.injEq, and_true] at hva
  obtain ⟨rfl, rfl⟩ := hva
  obtain ⟨jz, hjz, hl⟩ := (ext_def_inst_iff ctx st _ _).mp ‹externExtract ctx T.def_inst (.value z) _ = _›
  simp only [List.cons.injEq, and_true] at hl
  subst hl
  obtain ⟨jy, hjy, hl⟩ := (ext_def_inst_iff ctx st _ _).mp ‹externExtract ctx T.def_inst (.value y) _ = _›
  simp only [List.cons.injEq, and_true] at hl
  subst hl
  obtain ⟨infoz, hiz, hfz⟩ :=
    (ext_inst_data_value_iff ctx st _ _).mp ‹externExtract ctx T.inst_data_value (.inst jz) _ = _›
  simp only [List.cons.injEq, and_true] at hfz
  obtain ⟨-, hdz0⟩ := hfz
  obtain ⟨infoy, hiy, hfy⟩ :=
    (ext_inst_data_value_iff ctx st _ _).mp ‹externExtract ctx T.inst_data_value (.inst jy) _ = _›
  simp only [List.cons.injEq, and_true] at hfy
  obtain ⟨-, hdy⟩ := hfy
  -- the looked-through `ishl`
  obtain ⟨clz, hclz⟩ := Option.isSome_iff_exists.mp (hctx.defClif z _ _ hjz hiz)
  have hdz := hctx.data _ _ clz hiz hclz
  rw [← hdz0] at hdz
  obtain ⟨hf, ho⟩ := instData_inv_names hdz
  rw [variantNames_Binary] at hf
  rw [variantNames_Ishl_fb] at ho
  have hnm : instNames clz = ("Binary", "Ishl") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty1, x, ya, rfl⟩ := instNames_binary (cop := .ishl) rfl hnm
  obtain ⟨-, hfs⟩ := instData_binary_data rfl hdz
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  have hva2 := ‹externExtract ctx T.value_array_2 (.values [x, ya]) _ = _›
  simp only [ext_value_array_2_iff, List.cons.injEq, and_true] at hva2
  obtain ⟨rfl, rfl⟩ := hva2
  obtain ⟨ja, hja, hl⟩ :=
    (ext_def_inst_iff ctx st _ _).mp ‹externExtract ctx T.def_inst (.value ya) _ = _›
  simp only [List.cons.injEq, and_true] at hl
  subst hl
  obtain ⟨infoa, hia, hfa⟩ :=
    (ext_inst_data_value_iff ctx st _ _).mp ‹externExtract ctx T.inst_data_value (.inst ja) _ = _›
  simp only [List.cons.injEq, and_true] at hfa
  obtain ⟨-, hda⟩ := hfa
  -- the two constants
  obtain ⟨tyb, immb, hclb, hfb⟩ := defInst_iconst_clif ctx hctx hjy hiy hdy.symm
  simp only [List.cons.injEq, and_true] at hfb
  subst hfb
  obtain ⟨tya, imma, hcla, hfa'⟩ := defInst_iconst_clif ctx hctx hja hia hda.symm
  simp only [List.cons.injEq, and_true] at hfa'
  subst hfa'
  have hetyb : eTy tyb = true := by
    have hdat := hctx.data _ _ _ hiy hclb
    rw [← hdy] at hdat
    exact (fb_instData_iconst hdat).1
  have hetya : eTy tya = true := by
    have hdat := hctx.data _ _ _ hia hcla
    rw [← hda] at hdat
    exact (fb_instData_iconst hdat).1
  have hub := ‹externExtract ctx T.u64_from_imm64 (.int (imm64OfIconst tyb immb)) _ = _›
  rw [ext_u64_from_imm64_iff, u64_imm64OfIconst_fb (eTy_width hetyb)] at hub
  simp only [List.cons.injEq, and_true] at hub
  subst hub
  have hua := ‹externExtract ctx T.u64_from_imm64 (.int (imm64OfIconst tya imma)) _ = _›
  rw [ext_u64_from_imm64_iff, u64_imm64OfIconst_fb (eTy_width hetya)] at hua
  simp only [List.cons.injEq, and_true] at hua
  subst hua
  obtain ⟨rx, hrx, rfl, rfl⟩ :=
    (ctor_put_in_reg_iff ctx _ _ _ _).mp ‹externCtor ctx T.put_in_reg [.value x] _ = _›
  obtain rfl := hctx.valueReg x _ hrx
  obtain ⟨rfl, rfl⟩ :=
    (ctor_bfm_immr_iff ctx _ _ _ _ _ _).mp ‹externCtor ctx T.bfm_immr _ _ = _›
  obtain ⟨rfl, rfl⟩ :=
    (ctor_bfm_imms_iff ctx _ _ _ _ _ _).mp ‹externCtor ctx T.bfm_imms _ _ = _›
  have hW : IW w := by rcases h3264 with rfl | rfl <;> simp [IW]
  simp only [u64_toNat_fb (eTy_width hetya), u64_toNat_fb (eTy_width hetyb), bfmImmr,
    land_mod256 hW] at *
  have hA := ‹ApplyInternal _ _ _ _ 27 418 _ _ _ _›
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := bitfield_move_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_bitfieldMove_fb (hks.ofIdx hW) (rfl : (V.data 62 0 []).bfmOp? = some .uBfm)] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  rename LState => st0
  refine ⟨_, _, rfl, [x], by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by rw [show vuseNums _ = [x] from rfl] at hu; exact hu), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hz hy hres
  obtain ⟨vals', hev, hlk⟩ := hdfg.1 z _ _ _ _ hjz hiz hclz rfl hz
  obtain ⟨u1, yva, r, hu1, hyva, hr, rfl, -⟩ :=
    evalInst_shift_ok (rfl : Clif.BinaryOp.ishl.isShift = true) (hev default)
  have hv := lookup_zip_single_fb hlk
  cases hv
  have e1 := dfg_iconst_fb hdfg hja hia hcla hyva
  subst e1
  have e2 := dfg_iconst_fb hdfg hjy hiy hclb hy
  subst e2
  refine ⟨by simp [getAs_ok hu1], ?_⟩
  subst hty
  simp only [Clif.Sem.shift, Clif.Sem.ishl, Clif.Sem.ushr, Clif.Sem.shiftAmt, Option.some.injEq]
    at hr hres
  subst hr
  subst hres
  have hX : (ρ x).setWidth ty1.width = u1 := hvals x _ (getAs_ok hu1)
  cases ty1 <;> simp [Clif.Ty.width] at h3264
  · have ha := Nat.mod_lt imma.toNat (show 0 < 32 by decide)
    have hb := Nat.mod_lt immb.toNat (show 0 < 32 by decide)
    refine ⟨_, prun_rr hR rfl (fun w => ispec_bfm_fb (sz := .size32)
      (immr_lt ha hb)
      (by simp only [Clif.Ty.width, OperandSize.bits]; omega)) (prun_nil _), ?_⟩
    simp only [VHolds, upd_same]
    rw [← hX]
    exact bfm_fin_u .size32 (ρ x) ha hb
  · have ha := Nat.mod_lt imma.toNat (show 0 < 64 by decide)
    have hb := Nat.mod_lt immb.toNat (show 0 < 64 by decide)
    refine ⟨_, prun_rr hR rfl (fun w => ispec_bfm_fb (sz := .size64)
      (immr_lt ha hb)
      (by simp only [Clif.Ty.width, OperandSize.bits]; omega)) (prun_nil _), ?_⟩
    simp only [VHolds, upd_same]
    rw [← hX]
    exact bfm_fin_u .size64 (ρ x) ha hb

end Rules

end Backend.Proof

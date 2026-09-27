import FV.Backend.Proof.IselFamAluBRotTerms

/-!
# Family B: the rotate root rules (`rotl`/`rotr`, `lower.isle:1772–1862`)

Through `shift_ruleOk_gen`: the match and the right-hand side are inverted together
(`fbrot_inv`), then the helper contracts (`a64_rotr_ok`, `a64_rotr_imm_ok`, `small_rotr_ok`,
`small_rotr_imm_ok`, `sub_fb_ok`) give the code and its meaning; `rotl` is a right rotation by the
negated amount (`rotr_neg`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Final value lemmas -/

theorem setWidth_opnd_self (sz : OperandSize) (Z : CV) : Z.setWidth sz.bits = opnd sz Z := by
  rw [← setWidth_opnd (Nat.le_refl _) Z, BitVec.setWidth_eq]

theorem IW_bits (sz : OperandSize) : IW sz.bits := by cases sz <;> simp [IW, OperandSize.bits]

/-- A register rotate (`extr`) at operand size `sz`: its low `sz.bits` bits are the rotation of
the operand's by the amount modulo the width. -/
theorem rot_fin (sz : OperandSize) (X Y : CV) (a : Nat) (ha : a % sz.bits = Y.toNat % sz.bits) :
    (resX sz ((opnd sz X).rotateRight ((opnd sz Y).toNat % sz.bits))).setWidth sz.bits =
      (X.setWidth sz.bits).rotateRight (a % sz.bits) := by
  rw [setWidth_opnd_self, opnd_resX, setWidth_opnd_self, ha, opnd_mod (IW_bits sz)]

/-- An immediate rotate (`extr` with an immediate) at operand size `sz`. -/
theorem rot_imm_fin (sz : OperandSize) (X : CV) (L : Nat) :
    (resX sz ((opnd sz X).rotateRight L)).setWidth sz.bits = (X.setWidth sz.bits).rotateRight L := by
  rw [setWidth_opnd_self, opnd_resX, setWidth_opnd_self]

/-- The left rotate by a register: `extr` by the negated amount (`sub` from `xzr`). -/
theorem rotl_fin (sz : OperandSize) (X Y : CV) (a : Nat) (ha : a % sz.bits = Y.toNat % sz.bits) :
    (resX sz ((opnd sz X).rotateRight ((opnd sz (resX sz (0 - opnd sz Y))).toNat % sz.bits))).setWidth
      sz.bits = (X.setWidth sz.bits).rotateLeft (a % sz.bits) := by
  rw [setWidth_opnd_self, opnd_resX, opnd_resX, setWidth_opnd_self]
  have hpos : 0 < sz.bits := by cases sz <;> decide
  apply rotr_neg hpos
  rw [Nat.mod_mod, neg_mod (by cases sz <;> simp [OperandSize.bits]), opnd_mod (IW_bits sz), ha,
    Nat.mod_mod]

section Rules
variable {F : BitVec 64 → Prop} {isem : Sem}

set_option maxHeartbeats 1000000 in
/-- **`rotr_32_base_case`** (`lower.isle:1844`). -/
theorem rotr_32_base_case_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1844 := by
  refine shift_ruleOk_gen hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1844] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  have hty := ‹_ = info.resTys.head?.getD CTy.invalid›
  rw [hhead, Option.getD_some] at hty
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff] at hdat hty
  simp only [CTy.int.injEq] at hty
  subst hty
  have hrx := ‹ctx.valueReg? x = some _›
  have hry := ‹ctx.valueReg? y = some _›
  obtain rfl := hctx.valueReg x _ hrx
  obtain rfl := hctx.valueReg y _ hry
  have hA := ‹ApplyInternal _ _ _ _ 27 513 _ _ _ _›
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 32))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by rw [show vuseNums _ = [x, y] from rfl] at hu; exact hu), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width] at hty
  refine ⟨_, prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_extr_fb) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 32 = u := hvals x _ hx
  rw [← hX]
  exact rot_fin .size32 (ρ x) (ρ y) _ (amt_of_holds (IW_bits .size32) (hvals y yv hy))

set_option maxHeartbeats 1000000 in
/-- **`rotr_64_base_case`** (`lower.isle:1848`). -/
theorem rotr_64_base_case_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1848 := by
  refine shift_ruleOk_gen hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1848] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  have hty := ‹_ = info.resTys.head?.getD CTy.invalid›
  rw [hhead, Option.getD_some] at hty
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff] at hdat hty
  simp only [CTy.int.injEq] at hty
  subst hty
  have hrx := ‹ctx.valueReg? x = some _›
  have hry := ‹ctx.valueReg? y = some _›
  obtain rfl := hctx.valueReg x _ hrx
  obtain rfl := hctx.valueReg y _ hry
  have hA := ‹ApplyInternal _ _ _ _ 27 513 _ _ _ _›
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 64))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by rw [show vuseNums _ = [x, y] from rfl] at hu; exact hu), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width] at hty
  refine ⟨_, prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_extr_fb) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 64 = u := hvals x _ hx
  rw [← hX]
  exact rot_fin .size64 (ρ x) (ρ y) _ (amt_of_holds (IW_bits .size64) (hvals y yv hy))

set_option maxHeartbeats 1000000 in
/-- **`rotl_32_base_case`** (`lower.isle:1791`). -/
theorem rotl_32_base_case_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1791 := by
  refine shift_ruleOk_gen hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1791] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  have hty := ‹_ = info.resTys.head?.getD CTy.invalid›
  rw [hhead, Option.getD_some] at hty
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff, ctor_zero_reg']
    at hdat hty
  simp only [CTy.int.injEq] at hty
  subst hty
  have hrx := ‹ctx.valueReg? x = some _›
  have hry := ‹ctx.valueReg? y = some _›
  obtain rfl := hctx.valueReg x _ hrx
  obtain rfl := hctx.valueReg y _ hry
  have hxlt := vreg_lt hvb hrx
  have hS := ‹ApplyInternal _ _ _ _ 27 437 _ _ _ _›
  obtain ⟨ks0, hks0, rfl, m0, hm0, hs0⟩ := sub_fb_ok hp' hco (by omega) hS
  dsimp only at hm0 hs0
  rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 1 = some .sub) (hks0.ofIdx (by simp [IW] : IW 32))] at hm0
  cases hm0
  have hA := ‹ApplyInternal _ _ _ _ 27 513 _ _ _ _›
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [hs0] at hm1 hs1
  rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 32))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1, hs0]
    exact codeShapeU_two rfl rfl
      (fun u hu => by rw [show vuseNums _ = [y] from rfl] at hu; simp at hu; simp [hu])
      (fun u hu => by
        rw [show vuseNums _ = [x, _] from rfl] at hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl <;> simp), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width] at hty
  refine ⟨_, prun_rr hR rfl (fun w => ispec_sub_xzr_fb)
    (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_extr_fb) (prun_nil _)), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp (disch := omega) only [VHolds, hs0, LState.emit, LState.fresh, upd_same, upd_ne_fb]
  have hX : (ρ x).setWidth 32 = u := hvals x _ hx
  rw [← hX]
  exact rotl_fin .size32 (ρ x) (ρ y) _ (amt_of_holds (IW_bits .size32) (hvals y yv hy))

set_option maxHeartbeats 1000000 in
/-- **`rotl_64_base_case`** (`lower.isle:1797`). -/
theorem rotl_64_base_case_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1797 := by
  refine shift_ruleOk_gen hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1797] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  have hty := ‹_ = info.resTys.head?.getD CTy.invalid›
  rw [hhead, Option.getD_some] at hty
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff, ctor_zero_reg']
    at hdat hty
  simp only [CTy.int.injEq] at hty
  subst hty
  have hrx := ‹ctx.valueReg? x = some _›
  have hry := ‹ctx.valueReg? y = some _›
  obtain rfl := hctx.valueReg x _ hrx
  obtain rfl := hctx.valueReg y _ hry
  have hxlt := vreg_lt hvb hrx
  have hS := ‹ApplyInternal _ _ _ _ 27 437 _ _ _ _›
  obtain ⟨ks0, hks0, rfl, m0, hm0, hs0⟩ := sub_fb_ok hp' hco (by omega) hS
  dsimp only at hm0 hs0
  rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 1 = some .sub) (hks0.ofIdx (by simp [IW] : IW 64))] at hm0
  cases hm0
  have hA := ‹ApplyInternal _ _ _ _ 27 513 _ _ _ _›
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [hs0] at hm1 hs1
  rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 64))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1, hs0]
    exact codeShapeU_two rfl rfl
      (fun u hu => by rw [show vuseNums _ = [y] from rfl] at hu; simp at hu; simp [hu])
      (fun u hu => by
        rw [show vuseNums _ = [x, _] from rfl] at hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl <;> simp), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width] at hty
  refine ⟨_, prun_rr hR rfl (fun w => ispec_sub_xzr64_fb)
    (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_extr_fb) (prun_nil _)), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp (disch := omega) only [VHolds, hs0, LState.emit, LState.fresh, upd_same, upd_ne_fb]

  have hX : (ρ x).setWidth 64 = u := hvals x _ hx
  rw [← hX]
  exact rotl_fin .size64 (ρ x) (ρ y) _ (amt_of_holds (IW_bits .size64) (hvals y yv hy))

end Rules

end Backend.Proof

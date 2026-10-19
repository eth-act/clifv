import FV.Backend.Proof.IselFamAluBRot
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamAluBShiftTI
import FV.Backend.Proof.IselFamAluBShiftBaseTI
import FV.Backend.Proof.IselTermsShiftTI

/-!
# `IselFamAluBRot` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBRot`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Rules
variable {F : BitVec 64 → Prop} {isem : Sem}
set_option maxHeartbeats 1000000 in
/-- **`rotr_32_base_case`** (`lower.isle:1844`). -/
theorem rotr_32_base_case_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1844 := by
  refine shift_ruleOk_genTI hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
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
  obtain rfl := hctx.valueRegI x _ hrx
  obtain rfl := hctx.valueRegI y _ hry
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
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  refine ⟨_, prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_extr_fb) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 32 = u := hvals x _ hx
  rw [← hX]
  exact rot_fin .size32 (ρ x) (ρ y) _ (amt_of_holds (IW_bits .size32) (hvals y yv hy))

set_option maxHeartbeats 1000000 in
/-- **`rotr_64_base_case`** (`lower.isle:1848`). -/
theorem rotr_64_base_case_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1848 := by
  refine shift_ruleOk_genTI hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
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
  obtain rfl := hctx.valueRegI x _ hrx
  obtain rfl := hctx.valueRegI y _ hry
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
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  refine ⟨_, prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_extr_fb) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 64 = u := hvals x _ hx
  rw [← hX]
  exact rot_fin .size64 (ρ x) (ρ y) _ (amt_of_holds (IW_bits .size64) (hvals y yv hy))

set_option maxHeartbeats 1000000 in
/-- **`rotl_32_base_case`** (`lower.isle:1791`). -/
theorem rotl_32_base_case_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1791 := by
  refine shift_ruleOk_genTI hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
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
  obtain rfl := hctx.valueRegI x _ hrx
  obtain rfl := hctx.valueRegI y _ hry
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
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
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
theorem rotl_64_base_case_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1797 := by
  refine shift_ruleOk_genTI hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
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
  obtain rfl := hctx.valueRegI x _ hrx
  obtain rfl := hctx.valueRegI y _ hry
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
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  refine ⟨_, prun_rr hR rfl (fun w => ispec_sub_xzr64_fb)
    (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_extr_fb) (prun_nil _)), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp (disch := omega) only [VHolds, hs0, LState.emit, LState.fresh, upd_same, upd_ne_fb]

  have hX : (ρ x).setWidth 64 = u := hvals x _ hx
  rw [← hX]
  exact rotl_fin .size64 (ρ x) (ρ y) _ (amt_of_holds (IW_bits .size64) (hvals y yv hy))

set_option maxHeartbeats 1000000 in
/-- **`rotr_32_imm`** (`lower.isle:1857`). -/
theorem rotr_32_imm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1857 := by
  refine shift_ruleOk_genTI hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1857] at hm he
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
  obtain rfl := hctx.valueRegI x _ hrx
  have hdata := ‹V.data 152 35 _ = _›
  have hdj := ‹ctx.defInst? y = some _›
  have hij := ‹ctx.insts[_]? = some _›
  obtain ⟨ty', imm, hcl, hfs⟩ := defInst_iconst_clifTI ctx hctx hdj hij hdata.symm
  have hety' : eTy ty' = true := by
    have hdat := hctx.data _ _ _ hij hcl
    rw [← hdata] at hdat
    exact (fb_instData_iconst hdat).1
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
    ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
  have hL : Nat.land (u64 (imm64OfIconst ty' imm)) (32 - 1) = imm.toNat % 32 := by
    rw [land_mask_mod (by simp [IW]), u64_imm64OfIconst_fb (eTy_width hety')]
  have hA := ‹ApplyInternal _ _ _ _ 27 514 _ _ _ _›
  rw [hL] at hA
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_imm_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_aluRRImmShift_fb _ _ (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 32))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by
      rw [show vuseNums _ = [x] from rfl] at hu; simp at hu; simp [hu]), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  have hyv := dfg_iconst_fb hdfg hdj hij hcl hy
  subst hyv
  have hlt : imm.toNat % 32 < OperandSize.size32.bits := Nat.mod_lt _ (by decide)
  refine ⟨_, prun_rr hR rfl (fun w => ispec_imm_extr_fb hlt) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 32 = u := hvals x _ hx
  rw [← hX]
  exact rot_imm_fin .size32 (ρ x) _

set_option maxHeartbeats 1000000 in
/-- **`rotr_64_imm`** (`lower.isle:1862`). -/
theorem rotr_64_imm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1862 := by
  refine shift_ruleOk_genTI hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1862] at hm he
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
  obtain rfl := hctx.valueRegI x _ hrx
  have hdata := ‹V.data 152 35 _ = _›
  have hdj := ‹ctx.defInst? y = some _›
  have hij := ‹ctx.insts[_]? = some _›
  obtain ⟨ty', imm, hcl, hfs⟩ := defInst_iconst_clifTI ctx hctx hdj hij hdata.symm
  have hety' : eTy ty' = true := by
    have hdat := hctx.data _ _ _ hij hcl
    rw [← hdata] at hdat
    exact (fb_instData_iconst hdat).1
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
    ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
  have hL : Nat.land (u64 (imm64OfIconst ty' imm)) (64 - 1) = imm.toNat % 64 := by
    rw [land_mask_mod (by simp [IW]), u64_imm64OfIconst_fb (eTy_width hety')]
  have hA := ‹ApplyInternal _ _ _ _ 27 514 _ _ _ _›
  rw [hL] at hA
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_imm_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_aluRRImmShift_fb _ _ (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 64))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by
      rw [show vuseNums _ = [x] from rfl] at hu; simp at hu; simp [hu]), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  have hyv := dfg_iconst_fb hdfg hdj hij hcl hy
  subst hyv
  have hlt : imm.toNat % 64 < OperandSize.size64.bits := Nat.mod_lt _ (by decide)
  refine ⟨_, prun_rr hR rfl (fun w => ispec_imm_extr_fb hlt) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 64 = u := hvals x _ hx
  rw [← hX]
  exact rot_imm_fin .size64 (ρ x) _

set_option maxHeartbeats 1000000 in
/-- **`rotl_32_imm`** (`lower.isle:1803`). -/
theorem rotl_32_imm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1803 := by
  refine shift_ruleOk_genTI hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1803] at hm he
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
  obtain rfl := hctx.valueRegI x _ hrx
  have hdata := ‹V.data 152 35 _ = _›
  have hdj := ‹ctx.defInst? y = some _›
  have hij := ‹ctx.insts[_]? = some _›
  obtain ⟨ty', imm, hcl, hfs⟩ := defInst_iconst_clifTI ctx hctx hdj hij hdata.symm
  have hety' : eTy ty' = true := by
    have hdat := hctx.data _ _ _ hij hcl
    rw [← hdata] at hdat
    exact (fb_instData_iconst hdat).1
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
    ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
  have hL : Nat.land (u64 (imm64OfIconst ty' imm)) (32 - 1) = imm.toNat % 32 := by
    rw [land_mask_mod (by simp [IW]), u64_imm64OfIconst_fb (eTy_width hety')]
  have hA := ‹ApplyInternal _ _ _ _ 27 514 _ _ _ _›
  have hN := ‹externCtor ctx T.negate_imm_shift _ _ = _›
  rw [hL] at hN
  obtain ⟨rfl, rfl⟩ := (ctor_negate_imm_shift_iff ctx _ _ _ _ _).mp hN
  rw [neg_imm (by simp [IW]) (Nat.mod_lt _ (by decide))] at hA
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_imm_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_aluRRImmShift_fb _ _ (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 32))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by
      rw [show vuseNums _ = [x] from rfl] at hu; simp at hu; simp [hu]), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  have hyv := dfg_iconst_fb hdfg hdj hij hcl hy
  subst hyv
  have hlt : (32 - imm.toNat % 32) % 32 < OperandSize.size32.bits := Nat.mod_lt _ (by decide)
  refine ⟨_, prun_rr hR rfl (fun w => ispec_imm_extr_fb hlt) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 32 = u := hvals x _ hx
  rw [← hX]
  refine (rot_imm_fin .size32 (ρ x) _).trans ?_
  exact rotr_neg (by decide) _ _ _ (by simp only [OperandSize.bits, Clif.Ty.width, Nat.mod_mod])

set_option maxHeartbeats 1000000 in
/-- **`rotl_64_imm`** (`lower.isle:1808`). -/
theorem rotl_64_imm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1808 := by
  refine shift_ruleOk_genTI hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1808] at hm he
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
  obtain rfl := hctx.valueRegI x _ hrx
  have hdata := ‹V.data 152 35 _ = _›
  have hdj := ‹ctx.defInst? y = some _›
  have hij := ‹ctx.insts[_]? = some _›
  obtain ⟨ty', imm, hcl, hfs⟩ := defInst_iconst_clifTI ctx hctx hdj hij hdata.symm
  have hety' : eTy ty' = true := by
    have hdat := hctx.data _ _ _ hij hcl
    rw [← hdata] at hdat
    exact (fb_instData_iconst hdat).1
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
    ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
  have hL : Nat.land (u64 (imm64OfIconst ty' imm)) (64 - 1) = imm.toNat % 64 := by
    rw [land_mask_mod (by simp [IW]), u64_imm64OfIconst_fb (eTy_width hety')]
  have hA := ‹ApplyInternal _ _ _ _ 27 514 _ _ _ _›
  have hN := ‹externCtor ctx T.negate_imm_shift _ _ = _›
  rw [hL] at hN
  obtain ⟨rfl, rfl⟩ := (ctor_negate_imm_shift_iff ctx _ _ _ _ _).mp hN
  rw [neg_imm (by simp [IW]) (Nat.mod_lt _ (by decide))] at hA
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := a64_rotr_imm_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_aluRRImmShift_fb _ _ (rfl : ALUOp.ofIdx? 15 = some .extr) (hks.ofIdx (by simp [IW] : IW 64))] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_, _, rfl, by
    rw [hst, hs1]
    exact codeShapeU_one rfl (fun u hu => by
      rw [show vuseNums _ = [x] from rfl] at hu; simp at hu; simp [hu]), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  cases ty <;> simp [Clif.Ty.width, eTy] at hty hety
  have hyv := dfg_iconst_fb hdfg hdj hij hcl hy
  subst hyv
  have hlt : (64 - imm.toNat % 64) % 64 < OperandSize.size64.bits := Nat.mod_lt _ (by decide)
  refine ⟨_, prun_rr hR rfl (fun w => ispec_imm_extr_fb hlt) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  simp only [VHolds, upd_same]
  have hX : (ρ x).setWidth 64 = u := hvals x _ hx
  rw [← hX]
  refine (rot_imm_fin .size64 (ρ x) _).trans ?_
  exact rotr_neg (by decide) _ _ _ (by simp only [OperandSize.bits, Clif.Ty.width, Nat.mod_mod])

set_option maxHeartbeats 1000000 in
/-- **`rotr_fits_in_16`** (`lower.isle:1840`), i8/i16. -/
theorem rotr_fits_in_16_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1840 := by
  refine shift_ruleOk_genTI hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1840] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff, ctor_zero_reg']
    at hdat
  simp only [hhead, Option.getD_some] at *
  have h16 : w ≤ 16 := ‹_›
  have hw : w = 8 ∨ w = 16 := by omega
  have hry := ‹ctx.valueReg? y = some _›
  obtain rfl := hctx.valueRegI y _ hry
  have hylt := vreg_lt hvb hry
  have hZ := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
  have hE := zext32_ok hp' hco (by omega) hZ
  obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
    extOut_prunTI hR hctx hvb (.inl rfl) (by simp) (by simp) hE
  have hS := ‹ApplyInternal _ _ _ _ 27 710 _ _ _ _›
  obtain ⟨ms2, d, rfl, hsh, hsem2⟩ := small_rotr_ok hp' hco hR (by omega) hw hklt (by omega) hS
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨ms1 ++ ms2, d, rfl, by rw [hst]; exact codeShapeU_compose hem hmono hdefs huses hkx hsh, ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  subst hty
  obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr ρ ⟨_, u⟩ (hvals x _ hx) hdfg hx
  obtain ⟨ρ', hr2, -, hrot⟩ := hsem2 ρ1
  refine ⟨ρ', prun_append hr1 hr2, ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  have hA := hext.2 (show ty.width ≤ 32 by omega)
  simp only [Bool.false_eq_true, ↓reduceIte] at hA
  have hW : IW ty.width := by rcases hw with h | h <;> simp [IW, h]
  simp only [VHolds]
  rw [hrot u (by exact hA), hfr y hylt, amt_of_holds hW (hvals y yv hy)]

set_option maxHeartbeats 1000000 in
/-- **`rotr_fits_in_16_imm`** (`lower.isle:1852`), i8/i16. -/
theorem rotr_fits_in_16_imm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1852 := by
  refine shift_ruleOk_genTI hp (cop := .rotr) rfl rfl hp.t2386 term_2386_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1852] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff, ctor_zero_reg']
    at hdat
  simp only [hhead, Option.getD_some] at *
  have h16 : w ≤ 16 := ‹_›
  have hw : w = 8 ∨ w = 16 := by omega
  have hW : IW w := by rcases hw with h | h <;> simp [IW, h]
  have hdata := ‹V.data 152 35 _ = _›
  have hdj := ‹ctx.defInst? y = some _›
  have hij := ‹ctx.insts[_]? = some _›
  obtain ⟨ty', imm, hcl, hfs⟩ := defInst_iconst_clifTI ctx hctx hdj hij hdata.symm
  have hety' : eTy ty' = true := by
    have hdat := hctx.data _ _ _ hij hcl
    rw [← hdata] at hdat
    exact (fb_instData_iconst hdat).1
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
    ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
  have hL : Nat.land (u64 (imm64OfIconst ty' imm)) (w - 1) = imm.toNat % w := by
    rw [land_mask_mod hW, u64_imm64OfIconst_fb (eTy_width hety')]
  have hS := ‹ApplyInternal _ _ _ _ 27 712 _ _ _ _›
  rw [hL] at hS
  have hZ := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
  have hE := zext32_ok hp' hco (by omega) hZ
  obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
    extOut_prunTI hR hctx hvb (.inl rfl) (by simp) (by simp) hE
  obtain ⟨ms2, d, rfl, hsh, hsem2⟩ :=
    small_rotr_imm_ok hp' hco hR (by omega) hw (Nat.mod_lt _ hW.pos) hklt hS
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨ms1 ++ ms2, d, rfl, by
    rw [hst]
    exact codeShapeU_compose hem hmono hdefs huses hkx
      (hsh.weaken (fun u hu => by simp at hu; simp [hu])), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  subst hty
  have hyv := dfg_iconst_fb hdfg hdj hij hcl hy
  subst hyv
  obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr ρ ⟨_, u⟩ (hvals x _ hx) hdfg hx
  obtain ⟨ρ', hr2, -, hrot⟩ := hsem2 ρ1
  refine ⟨ρ', prun_append hr1 hr2, ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  have hA := hext.2 (show ty.width ≤ 32 by omega)
  simp only [Bool.false_eq_true, ↓reduceIte] at hA
  simp only [VHolds]
  rw [hrot u (by exact hA)]

set_option maxHeartbeats 1000000 in
/-- **`rotl_fits_in_16_imm`** (`lower.isle:1778`), i8/i16. -/
theorem rotl_fits_in_16_imm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1778 := by
  refine shift_ruleOk_genTI hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1778] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff, ctor_zero_reg']
    at hdat
  simp only [hhead, Option.getD_some] at *
  have h16 : w ≤ 16 := ‹_›
  have hw : w = 8 ∨ w = 16 := by omega
  have hW : IW w := by rcases hw with h | h <;> simp [IW, h]
  have hdata := ‹V.data 152 35 _ = _›
  have hdj := ‹ctx.defInst? y = some _›
  have hij := ‹ctx.insts[_]? = some _›
  obtain ⟨ty', imm, hcl, hfs⟩ := defInst_iconst_clifTI ctx hctx hdj hij hdata.symm
  have hety' : eTy ty' = true := by
    have hdat := hctx.data _ _ _ hij hcl
    rw [← hdata] at hdat
    exact (fb_instData_iconst hdat).1
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
    ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
  have hL : Nat.land (u64 (imm64OfIconst ty' imm)) (w - 1) = imm.toNat % w := by
    rw [land_mask_mod hW, u64_imm64OfIconst_fb (eTy_width hety')]
  have hS := ‹ApplyInternal _ _ _ _ 27 712 _ _ _ _›
  have hN := ‹externCtor ctx T.negate_imm_shift _ _ = _›
  rw [hL] at hN
  obtain ⟨rfl, rfl⟩ := (ctor_negate_imm_shift_iff ctx _ _ _ _ _).mp hN
  rw [neg_imm hW (Nat.mod_lt _ hW.pos)] at hS
  have hZ := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
  have hE := zext32_ok hp' hco (by omega) hZ
  obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
    extOut_prunTI hR hctx hvb (.inl rfl) (by simp) (by simp) hE
  obtain ⟨ms2, d, rfl, hsh, hsem2⟩ :=
    small_rotr_imm_ok hp' hco hR (by omega) hw (Nat.mod_lt _ hW.pos) hklt hS
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨ms1 ++ ms2, d, rfl, by
    rw [hst]
    exact codeShapeU_compose hem hmono hdefs huses hkx
      (hsh.weaken (fun u hu => by simp at hu; simp [hu])), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  subst hty
  have hyv := dfg_iconst_fb hdfg hdj hij hcl hy
  subst hyv
  obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr ρ ⟨_, u⟩ (hvals x _ hx) hdfg hx
  obtain ⟨ρ', hr2, -, hrot⟩ := hsem2 ρ1
  refine ⟨ρ', prun_append hr1 hr2, ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  have hA := hext.2 (show ty.width ≤ 32 by omega)
  simp only [Bool.false_eq_true, ↓reduceIte] at hA
  simp only [VHolds]
  rw [hrot u (by exact hA)]
  exact rotr_neg hW.pos _ _ _ (by simp only [Nat.mod_mod])

set_option maxHeartbeats 1000000 in
/-- **`rotl_fits_in_16`** (`lower.isle:1772`), i8/i16. -/
theorem rotl_fits_in_16_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1772 := by
  refine shift_ruleOk_genTI hp (cop := .rotl) rfl rfl hp.t2385 term_2385_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info x y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1772] at hm he
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 2 _ = info.data›
  rw [hd] at hdat
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ctor_value_regs_get_iff, ctor_zero_reg']
    at hdat
  simp only [hhead, Option.getD_some] at *
  have h16 : w ≤ 16 := ‹_›
  have hw : w = 8 ∨ w = 16 := by omega
  have hW : IW w := by rcases hw with h | h <;> simp [IW, h]
  have hry := ‹ctx.valueReg? y = some _›
  obtain rfl := hctx.valueRegI y _ hry
  have hylt := vreg_lt hvb hry
  rename LState => st0
  have hS0 := ‹ApplyInternal _ _ _ _ 27 437 _ _ _ _›
  obtain ⟨ks0, hks0, rfl, m0, hm0, hs0⟩ := sub_fb_ok hp' hco (by omega) hS0
  dsimp only at hm0 hs0
  rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 1 = some .sub) (hks0.ofIdx (by simp [IW] : IW 32))] at hm0
  cases hm0
  have hZ := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
  have hE := zext32_ok hp' hco (by omega) hZ
  obtain ⟨-, -, rx, hrx, -⟩ := id hE
  have hxlt := vreg_lt hvb hrx
  rw [hs0] at hE
  have hvb1 : ValsBelow ctx ((st0.fresh .int).2.emit (MInst.aluRRR .sub (szOf 32) (st0.fresh .int).1
      .xzr (.vreg y .int))) := fun z r hz => by
    have := hvb z r hz; simp only [LState.emit, LState.fresh]; omega
  obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
    extOut_prunTI hR hctx hvb1 (.inl rfl) (by simp) (by simp) hE
  have hS := ‹ApplyInternal _ _ _ _ 27 710 _ _ _ _›
  obtain ⟨ms2, d, rfl, hsh, hsem2⟩ := small_rotr_ok hp' hco hR (by omega) hw (a := st0.nextVreg) hklt
    (by simp only [LState.emit, LState.fresh] at hmono ⊢; omega) hS
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  refine ⟨_ :: (ms1 ++ ms2), d, rfl, by
    rw [hst]
    exact codeShapeU_cons rfl (fun u hu => by
      rw [show vuseNums _ = [y] from rfl] at hu; simpa using hu)
      (codeShapeU_compose hem hmono hdefs huses hkx hsh), ?_⟩
  intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
  subst hty
  have hx0 : VHolds ⟨ty, u⟩ (upd ρ st0.nextVreg
      (resX .size32 (0 - opnd .size32 (ρ y))) x) := by
    rw [upd_ne_fb (by omega)]; exact hvals x _ hx
  obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr _ ⟨_, u⟩ hx0 hdfg hx
  obtain ⟨ρ', hr2, -, hrot⟩ := hsem2 ρ1
  refine ⟨ρ', prun_rr hR rfl (fun w => ispec_sub_xzr_fb) (prun_append hr1 hr2), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.rotl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
  subst hres
  have hA := hext.2 (show ty.width ≤ 32 by omega)
  simp only [Bool.false_eq_true, ↓reduceIte] at hA
  simp only [VHolds]
  rw [hrot u (by exact hA), hfr st0.nextVreg (by simp [LState.emit, LState.fresh]), upd_same,
    ← opnd_mod hW .size32, opnd_resX,
    neg_mod (N := OperandSize.size32.bits) (.inl ⟨rfl, by rcases hw with h | h <;> simp [h]⟩),
    opnd_mod hW,
    amt_of_holds hW (hvals y yv hy)]
  exact rotr_neg hW.pos _ _ _ (by simp only [Nat.mod_mod])

end Rules
end Backend.Proof

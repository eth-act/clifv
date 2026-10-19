import FV.Backend.Proof.IselFamAluBBfm
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamAluBShiftBaseTI
import FV.Backend.Proof.IselTermsShiftTI

/-!
# `IselFamAluBBfm` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBBfm`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Ctor
variable (ctx : Ctx) (st : LState)
end Ctor
section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
/-- As `shift_ruleOk_genTI`, but the code may read any values `xs` the right-hand side names,
provided they are defined in every frame the instruction runs in. -/
theorem shift_ruleOk_usesTI {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp} {n : String}
    (hshift : cop.isShift = true)
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hMR : MRStable F MR)
    (hrhs : ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx → ∀ (cfg : Config) ii (info : IInfo)
      x y w (st : LState) tr m n env' s1 v s', cfg.checkOverlap = false → ValsBelow ctx st →
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) →
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] →
      (w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) →
      (matchRule p (sem ctx) cfg (m + 10) r [.inst ii]).run (st, tr) = .ok (some env', s1) →
      (evalExpr p (sem ctx) cfg (n + 200) r.rhs env').run s1 = .ok (some v, s') →
      IntPos ctx x → IntPos ctx y →
      ∃ ms d xs, v = .regsVec [[.vreg d .int]] ∧ CodeShapeU st s'.1 ms d xs ∧
        ∀ (ty : Clif.Ty), ty.width = w → eTy ty = true →
        ∀ (fr : Clif.Frame) (ρ : Nat → CV) (u : BitVec ty.width) (yv : Clif.Val) (res : BitVec ty.width),
          fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → fr.regs x = some ⟨ty, u⟩ →
          fr.regs y = some yv → Clif.Sem.shift cop u yv.bits = some res →
          (∀ z ∈ xs, (fr.regs z).isSome) ∧ ∃ ρ', PRun F isem ms ρ ρ' ∧ VHolds ⟨ty, res⟩ (ρ' d)) :
    LowerRuleOkTI isem MR env cp p r := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb hfirst
      hmatch' heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, y, rfl, hety, hd, hhead⟩ :=
    binary_frontTI hp hargs hto hko hname hcop hctx hi hc (m := m' + 9) hmatch'
  have hws : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    cases ty <;> simp [eTy, Clif.Ty.width] at hety ⊢
  obtain ⟨ms, d, xs, rfl, hsh, hsem⟩ :=
    hrhs f ctx hctx cfg ii info x y ty.width st tr m' n' env' s1 out (st', tr') hco hvb hi hhead hd
      hws hmatch' heval (hops x (by simp [intArgs])) (hops y (by simp [intArgs]))
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
theorem sbfm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1704 := by
  refine shift_ruleOk_usesTI hp (cop := .sshr) rfl rfl hp.t2389 term_2389_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info z y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
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
  obtain ⟨tyb, immb, hclb, hfb⟩ := defInst_iconst_clifTI ctx hctx hjy hiy hdy.symm
  simp only [List.cons.injEq, and_true] at hfb
  subst hfb
  obtain ⟨tya, imma, hcla, hfa'⟩ := defInst_iconst_clifTI ctx hctx hja hia hda.symm
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
  obtain rfl := hctx.valueRegI x _ hrx
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
  cases ty1 <;> simp [Clif.Ty.width, eTy] at h3264 hety
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
theorem ubfm_okTI {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1707 := by
  refine shift_ruleOk_usesTI hp (cop := .ushr) rfl rfl hp.t2388 term_2388_kind rfl rfl F isem MR env
    cp hMR ?_
  intro f ctx hctx cfg ii info z y w st tr m n env' s1 v s' hco hvb hi hhead hd hws hm he
  intro hxI hyI
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
  obtain ⟨tyb, immb, hclb, hfb⟩ := defInst_iconst_clifTI ctx hctx hjy hiy hdy.symm
  simp only [List.cons.injEq, and_true] at hfb
  subst hfb
  obtain ⟨tya, imma, hcla, hfa'⟩ := defInst_iconst_clifTI ctx hctx hja hia hda.symm
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
  obtain rfl := hctx.valueRegI x _ hrx
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
  cases ty1 <;> simp [Clif.Ty.width, eTy] at h3264 hety
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

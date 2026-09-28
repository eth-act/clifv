import FV.Backend.Proof.IselFamAluBRot

/-!
# Family B: `bnot_ishl` (`lower.isle:1401`)

`(bnot ty (ishl x (iconst k)))` → `(orr_not_shift ty (zero_reg) x (lshl_from_imm64 ty k))`:
one `orn wd, wzr, wx, lsl #amt` (`AluRRRShift .orrNot` with the zero register as first operand).
The match is inverted together with the right-hand side (`fbrot_inv`); the `ishl` and the
`iconst` are looked through (`DFGCons`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

theorem ofV_aluRRRShift_fb {k ks : Nat} {op : ALUOp} {sz : OperandSize}
    (hk : ALUOp.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (rd rn rm : Reg)
    (sh : ShiftOpAndAmt) :
    MInst.ofV (.data 58 7 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm,
      .op (.shiftOpAndAmt sh)]) = some (.aluRRRShift op sz rd rn rm sh) := by
  have e1 : MInst.ofV (.data 58 7 [.data 59 k [], .data 93 ks [], .reg rd, .reg rn, .reg rm,
      .op (.shiftOpAndAmt sh)]) = (do
        return .aluRRRShift (← (V.data 59 k []).aluOp?) (← (V.data 93 ks []).size?) rd rn rm sh) :=
    rfl
  rw [e1]
  have e2 : (V.data 59 k []).aluOp? = ALUOp.ofIdx? k := rfl
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e2, e3, hk, hs]
  rfl

include hp hc in
theorem alu_rrr_shift_ok {n : Nat} (hn : 40 ≤ n) {op a b c : V} {t : CTy}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 377 [op, .ty t, a, b, c] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 7 [op, .data 93 ks [], .reg rd, a, b, c]) := by
  have hp' := hp
  isel_split hp hc h 377
  isel_inv [*, rule_inst_2656] at hm he
  rename_i hsz
  obtain ⟨hs, hk⟩ := operand_size_ok hp' hc (by omega) hsz
  rcases hk with ⟨hb, rfl⟩ | ⟨hb, hb', rfl⟩
  · exact ⟨0, .inl ⟨hb, rfl⟩, rfl, _, ‹_›, by rw [hs]⟩
  · exact ⟨1, .inr ⟨hb, hb', rfl⟩, rfl, _, ‹_›, by rw [hs]⟩

include hp hc in
theorem orr_not_shift_ok {n : Nat} (hn : 50 ≤ n) {a b c : V} {t : CTy}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 496 [.ty t, a, b, c] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 7 [.data 59 3 [], .data 93 ks [], .reg rd, a, b, c]) := by
  have hp' := hp
  isel_split hp hc h 496
  isel_inv [*, rule_inst_3407] at hm he
  rename_i hl
  exact alu_rrr_shift_ok hp' hc (by omega) hl

end Terms

/-! ## The root rule -/

theorem not_shl_fin (sz : OperandSize) {w : Nat} (hw : w ≤ sz.bits) (X : CV) (u : BitVec w)
    (hX : X.setWidth w = u) (s : Nat) :
    (resX sz (0#sz.bits ||| ~~~(opnd sz X <<< s))).setWidth w = ~~~(u <<< s) := by
  rw [← setWidth_opnd hw, opnd_resX, BitVec.zero_or, BitVec.setWidth_not hw, shl_setWidth hw,
    setWidth_opnd hw, hX]

theorem ispec_orn_shift_fb {sz : OperandSize} {d : Nat} {rm : Reg} {s : Nat} (hs : s < sz.bits)
    {b : CV} {w : Arm.ArmState} :
    ispec (.aluRRRShift .orrNot sz (.vreg d .int) .xzr rm ⟨.lsl, s⟩) [b] w =
      some ([resX sz (0#sz.bits ||| ~~~(opnd sz b <<< s))], w, .next) := by
  simp only [ispec, aluShiftable, hs, and_self, ↓reduceIte, aluVal, Option.map_some]; rfl

theorem ctor_lshl_fb {ctx : Ctx} {st : LState} (w : Nat) (k : Int) :
    externCtor ctx T.lshl_from_imm64 [.ty (.int w), .int k] st =
      match shiftImm? (u64 k) with
      | some s => if w ≤ 255 then .ok (.op (.shiftOpAndAmt ⟨.lsl, Nat.land s (w - 1)⟩), st)
        else .fail
      | none => .fail := by
  have e : externCtor ctx T.lshl_from_imm64 [.ty (.int w), .int k] st =
      match shiftImm? (u64 k) with
      | some s => if (CTy.int w).bits ≤ 255 then
          .ok (.op (.shiftOpAndAmt ⟨.lsl, Nat.land s ((CTy.int w).bits - 1)⟩), st) else .fail
      | none => .fail := rfl
  rw [e]; rfl

theorem variantNames_Ishl_fb : (variantNames 151)[103]? = some "Ishl" := rfl

section Rule
variable {F : BitVec 64 → Prop} {isem : Sem}

set_option maxHeartbeats 1000000 in
/-- **`bnot_ishl`** (`lower.isle:1401`), i8..i64. -/
theorem bnot_ishl_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1401 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, z, rfl, hety, -, hd, hhead⟩ := unary_front hp (cop := .bnot) rfl hp.t2384
    term_2384_kind variantNames_Bnot rfl hctx hi hc (m := m' + 9) hmatch
  have hp' := hp
  cases hp
  fbrot_inv [*, rule_lower_1401] at hmatch heval
  have hii := Option.some.inj (hi.symm.trans ‹ctx.insts[ii]? = some _›)
  subst hii
  have hdat := ‹V.data 152 29 _ = info.data›
  rw [hd] at hdat
  simp only [hhead, Option.getD_some] at *
  fbrot_inv [ext_value_array_2_iff, ctor_put_in_reg_iff, ext_def_inst_iff, ext_inst_data_value_iff]
    at hdat
  -- the looked-through `ishl`
  have hjz := ‹ctx.defInst? z = some _›
  have hijz := ‹ctx.insts[_]? = some _›
  have hdz0 := ‹V.data 152 2 [V.data 151 103 [], _] = _›
  obtain ⟨clz, hclz⟩ := Option.isSome_iff_exists.mp (hctx.defClif z _ _ hjz hijz)
  have hdz := hctx.data _ _ clz hijz hclz
  rw [← hdz0] at hdz
  obtain ⟨hf, ho⟩ := instData_inv_names hdz
  rw [variantNames_Binary] at hf
  rw [variantNames_Ishl_fb] at ho
  have hnm : instNames clz = ("Binary", "Ishl") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty1, x, y, rfl⟩ := instNames_binary (cop := .ishl) rfl hnm
  obtain ⟨-, hfs⟩ := instData_binary_data rfl hdz
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  have hva := ‹externExtract ctx T.value_array_2 _ _ = _›
  simp only [ext_value_array_2_iff, List.cons.injEq, and_true] at hva
  obtain ⟨rfl, rfl⟩ := hva
  have hdi := ‹externExtract ctx T.def_inst _ _ = _›
  obtain ⟨jy, hjy, hl⟩ := (ext_def_inst_iff ctx st _ _).mp hdi
  simp only [List.cons.injEq, and_true] at hl
  subst hl
  have hidv := ‹externExtract ctx T.inst_data_value _ _ = _›
  obtain ⟨infoy, hiy, hfy⟩ := (ext_inst_data_value_iff ctx st _ _).mp hidv
  simp only [List.cons.injEq, and_true] at hfy
  obtain ⟨-, hdy⟩ := hfy
  have hpr := ‹externCtor ctx T.put_in_reg _ _ = _›
  obtain ⟨rx, hrx, rfl, rfl⟩ := (ctor_put_in_reg_iff ctx _ _ _ _).mp hpr
  obtain rfl := hctx.valueReg x _ hrx
  obtain ⟨ty', imm, hcly, hfs'⟩ := defInst_iconst_clif ctx hctx hjy hiy hdy.symm
  simp only [List.cons.injEq, and_true] at hfs'
  subst hfs'
  have hety' : eTy ty' = true := by
    have hdat := hctx.data _ _ _ hiy hcly
    rw [← hdy] at hdat
    exact (fb_instData_iconst hdat).1
  have hw64 : ty.width ≤ 64 := eTy_width hety
  have hl := ‹externCtor ctx T.lshl_from_imm64 _ _ = _›
  rw [ctor_lshl_fb, u64_imm64OfIconst_fb (eTy_width hety')] at hl
  rcases Nat.lt_or_ge 63 imm.toNat with h63 | h63
  · simp [shiftImm?, show ¬ imm.toNat ≤ 63 by omega] at hl
  simp only [shiftImm?, h63, ↓reduceIte,
    show ty.width ≤ 255 by omega, ExtResult.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  have hW : IW ty.width := by cases ty <;> simp [eTy, IW, Clif.Ty.width] at hety ⊢
  rw [land_mask_mod hW] at *
  have hA := ‹ApplyInternal _ _ _ _ 27 496 _ _ _ _›
  obtain ⟨ks, hks, rfl, m1, hm1, hs1⟩ := orr_not_shift_ok hp' hco (by omega) hA
  dsimp only at hm1 hs1
  rw [ofV_aluRRRShift_fb (rfl : ALUOp.ofIdx? 3 = some .orrNot) (hks.ofIdx hW)] at hm1
  cases hm1
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hO
  have hsh : CodeShapeU st st' [MInst.aluRRRShift .orrNot (szOf ty.width) (.vreg st.nextVreg .int)
      .xzr (.vreg x .int) ⟨.lsl, imm.toNat % ty.width⟩] st.nextVreg [x] := by
    have e : st' = _ := hst.trans hs1
    rw [e]
    exact codeShapeU_one rfl (fun u hu => by rw [show vuseNums _ = [x] from rfl] at hu; exact hu)
  refine ⟨_, hsh.emitted, _, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  have ho' : Clif.evalInst fr cm (.unary .bnot ty z) = .ok (vals, cm') := ho
  obtain ⟨a, ha, rfl, rfl⟩ := evalInst_unary_ok ho'
  obtain ⟨vals', hev, hlk⟩ := hdfg.1 z _ _ _ _ hjz hijz hclz rfl (getAs_ok ha)
  obtain ⟨u1, yv, r, hu1, hyv, hr, rfl, -⟩ :=
    evalInst_shift_ok (rfl : Clif.BinaryOp.ishl.isShift = true) (hev default)
  have hv := lookup_zip_single_fb hlk
  cases hv
  have hyv' := dfg_iconst_fb hdfg hjy hiy hcly hyv
  subst hyv'
  have hlt : imm.toNat % ty.width < (szOf ty.width).bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hW.pos) (szOf_bits hw64)
  refine ⟨rfl, usesOk_of [x] hsh.uses (by simp [getAs_ok hu1]), .inl hsh.res, _, _, rfl,
    prun_rr hR rfl (fun w => ispec_orn_shift_fb hlt) (prun_nil _), ?_⟩
  simp only [Clif.Sem.shift, Clif.Sem.ishl, Clif.Sem.shiftAmt, Option.some.injEq] at hr
  subst hr
  simp only [VHolds, upd_same, Clif.Sem.unary, Clif.Sem.bnot]
  exact not_shl_fin _ (szOf_bits hw64) _ _ (hvals x _ (getAs_ok hu1)) _

end Rule

end Backend.Proof

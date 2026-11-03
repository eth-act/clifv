import FV.Backend.Proof.IselRulesALUA
import FV.Backend.Proof.IselFamilyALU

/-!
# Family A root rules: `LowerRuleOk` at every width i8..i64

Each theorem: match inversion (`binary_root_inv`, `values2_match_inv`, `defInst_match_inv`)
names the instruction and the looked-through definitions; the forward lemmas
(`IselRulesALUA`) fix the environment and the emitted code; `lowerInstOk_one` reduces the
obligation to the value-level meaning of the emitted instruction, which `DFGCons` (the
looked-through values) and the width lemmas (`IselFamALUA`) discharge.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000 in
theorem variantNames_Imul : (variantNames 151)[77]? = some "Imul" := rfl

/-! ## Immediate operands (`imm12_from_value`) -/

/-- The meaning of `aluRRImm12 add/sub` on the register `r` and the looked-through constant
`c` (with `imm.value = c.toNat`). -/
theorem imm12_sem {sz : OperandSize} {ty : Clif.Ty} (hw : ty.width ≤ sz.bits) {d r : Nat}
    {imm : Imm12} {c : BitVec ty.width} (hiv : imm.value = c.toNat) (hib : imm.bits < 4096)
    {ρ : Nat → CV} {u : BitVec ty.width} (hr : VHolds ⟨ty, u⟩ (ρ r)) (w : Arm.ArmState) :
    (∃ res, ispec (.aluRRImm12 .add sz (.vreg d .int) (.vreg r .int) imm)
        (vuses #[⟨d, .int, .def, .late, .reg⟩, ⟨r, .int, .use, .early, .reg⟩] ρ) w =
        some ([res], w, .next) ∧ VHolds ⟨ty, u + c⟩ res) ∧
    (∃ res, ispec (.aluRRImm12 .sub sz (.vreg d .int) (.vreg r .int) imm)
        (vuses #[⟨d, .int, .def, .late, .reg⟩, ⟨r, .int, .use, .early, .reg⟩] ρ) w =
        some ([res], w, .next) ∧ VHolds ⟨ty, u - c⟩ res) :=
  ⟨⟨_, ispec_aluRRImm12_add hib, by rw [hiv]; exact holds_add_imm hw hr⟩,
   ⟨_, ispec_aluRRImm12_sub hib, by rw [hiv]; exact holds_sub_imm hw hr⟩⟩

/-- The looked-through `iconst` at the instruction's type: its value, and the `Imm12` the
rule built from it. -/
theorem iconst_imm12 {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {y j : Nat}
    {infoj : IInfo} {ty ty' : Clif.Ty} {c : BitVec ty'.width} {v : BitVec ty.width}
    {imm : Imm12} (hw : ty.width ≤ 64) (hj : ctx.defInst? y = some j)
    (hij : ctx.insts[j]? = some infoj) (hcl : infoj.clif = some (.iconst ty' c))
    (hy : fr.getAs y ty = .ok v) (himm : Imm12.ofNat? (u64 (imm64OfIconst ty' c)) = some imm) :
    imm.value = v.toNat ∧ imm.bits < 4096 := by
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hy) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  rw [u64_imm64OfIconst hw v] at himm
  exact imm12_ofNat_value himm (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) hw))

/-- **`iadd_imm12_right`** (`lower.isle:90`, `iadd x (iconst k)` with `k` an `Imm12` →
`add x, #k`), i8..i64. -/
theorem iadd_imm12_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_90 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, hfs⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨imm, himm, -⟩ := imm12_args_inv hp ctx hfs
  rw [match_90 hp ctx hi hhead hw hd hj hij hdj himm st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_90_none hp ctx hrx st tr n' out (st', tr'))
  | some rx =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain ⟨tr'', he⟩ := rhs_90 hp ctx hco hrx hw st tr n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨hiv, hib⟩ := iconst_imm12 hdfg hw hj hij hcl hy himm
  refine ⟨fun z hz => ?_, (imm12_sem (szOf_bits hw) hiv hib (hvals x _ (getAs_ok hx)) w).1⟩
  rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
  subst hz
  simp [getAs_ok hx]

/-- **`iadd_imm12_left`** (`lower.isle:93`, `iadd (iconst k) y` → `add y, #k`), i8..i64. -/
theorem iadd_imm12_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_93 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, hfs⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpx
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨imm, himm, -⟩ := imm12_args_inv hp ctx hfs
  rw [match_93 hp ctx hi hhead hw hd hj hij hdj himm st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_93_none hp ctx hry st tr n' out (st', tr'))
  | some ry =>
  obtain rfl := hctx.valueReg y ry hry
  obtain ⟨tr'', he⟩ := rhs_93 hp ctx hco hry hw st tr n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨hiv, hib⟩ := iconst_imm12 hdfg hw hj hij hcl hx himm
  obtain ⟨res, hs, hh⟩ := (imm12_sem (szOf_bits hw) hiv hib (hvals y _ (getAs_ok hy)) w).1
  refine ⟨fun z hz => ?_, res, hs, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hy]
  · show VHolds ⟨ty, u + v⟩ res
    rw [BitVec.add_comm]
    exact hh

/-- **`isub_imm12`** (`lower.isle:805`, `isub x (iconst k)` → `sub x, #k`), i8..i64. -/
theorem isub_imm12_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_805 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, hfs⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨imm, himm, -⟩ := imm12_args_inv hp ctx hfs
  rw [match_805 hp ctx hi hhead hw hd hj hij hdj himm st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_805_none hp ctx hrx st tr n' out (st', tr'))
  | some rx =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain ⟨tr'', he⟩ := rhs_805 hp ctx hco hrx hw st tr n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨hiv, hib⟩ := iconst_imm12 hdfg hw hj hij hcl hy himm
  refine ⟨fun z hz => ?_, (imm12_sem (szOf_bits hw) hiv hib (hvals x _ (getAs_ok hx)) w).2⟩
  rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
  subst hz
  simp [getAs_ok hx]

/-- **iadd_imm12_neg_right** (`lower.isle:98`, `iadd x (iconst k)` with `-k` an `Imm12` → `sub x, #-k`), i8..i64. -/
theorem iadd_imm12_neg_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_98 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, hil⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 39) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, hpy⟩ := values2_match_inv hp ctx hrest
  have he1 := matchPat_bind_wild_inv ctx hpy
  have he2 := matchPat_bind_wild_inv ctx hpx
  have hy : e1[2]? = some (some (.value y)) := getElem_bind_env (matchPat_bind_inv hpy).1 he1
  obtain ⟨v0, s2, happ⟩ := iflet_term_var_inv ctx (m := m' + 35) hil hy
  obtain ⟨j, infoj, ty', c, hj, hij, hcl, hdj, htyj⟩ :=
    negated_value_inv hp ctx hctx hco (m := m' + 32) happ
  cases hneg : negImm12? ty'.width (imm64OfIconst ty' c) with
  | none =>
    rw [match_98_none hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
    cases hmatch
  | some imm =>
  rw [match_98 hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hr : ctx.valueReg? x with
  | none => exact absurd heval (rhs_98_none hp ctx hr st _ n' out (st', tr'))
  | some r =>
  obtain rfl := hctx.valueReg x r hr
  obtain ⟨tr'', he⟩ := rhs_98 hp ctx hco hr hw st _ n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hy) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hib, hK⟩ := negImm12_value hw v (by unfold negImm12? at hneg; exact hneg)
  refine ⟨fun z hz => ?_, _, ispec_aluRRImm12_sub hib, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hx]
  · have := holds_sub_K (szOf_bits hw) (hK _ (szOf_bits hw)) (hvals x _ (getAs_ok hx))
    show VHolds ⟨ty, u + v⟩ _
    rwa [BitVec.sub_eq_add_neg, BitVec.neg_neg] at this

/-- **iadd_imm12_neg_left** (`lower.isle:102`, `iadd (iconst k) y` with `-k` an `Imm12` → `sub y, #-k`), i8..i64. -/
theorem iadd_imm12_neg_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_102 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, hil⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 39) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, hpy⟩ := values2_match_inv hp ctx hrest
  have he1 := matchPat_bind_wild_inv ctx hpy
  have he2 := matchPat_bind_wild_inv ctx hpx
  have hx : e1[1]? = some (some (.value x)) := by rw [getElem_bind_env_ne (by decide) he1]; exact getElem_bind_env (matchPat_bind_inv hpx).1 he2
  obtain ⟨v0, s2, happ⟩ := iflet_term_var_inv ctx (m := m' + 35) hil hx
  obtain ⟨j, infoj, ty', c, hj, hij, hcl, hdj, htyj⟩ :=
    negated_value_inv hp ctx hctx hco (m := m' + 32) happ
  cases hneg : negImm12? ty'.width (imm64OfIconst ty' c) with
  | none =>
    rw [match_102_none hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
    cases hmatch
  | some imm =>
  rw [match_102 hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hr : ctx.valueReg? y with
  | none => exact absurd heval (rhs_102_none hp ctx hr st _ n' out (st', tr'))
  | some r =>
  obtain rfl := hctx.valueReg y r hr
  obtain ⟨tr'', he⟩ := rhs_102 hp ctx hco hr hw st _ n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hx) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hib, hK⟩ := negImm12_value hw u (by unfold negImm12? at hneg; exact hneg)
  refine ⟨fun z hz => ?_, _, ispec_aluRRImm12_sub hib, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hy]
  · have := holds_sub_K (szOf_bits hw) (hK _ (szOf_bits hw)) (hvals y _ (getAs_ok hy))
    show VHolds ⟨ty, u + v⟩ _
    rwa [BitVec.sub_eq_add_neg, BitVec.neg_neg, BitVec.add_comm] at this

/-- **isub_imm12_neg** (`lower.isle:810`, `isub x (iconst k)` with `-k` an `Imm12` → `add x, #-k`), i8..i64. -/
theorem isub_imm12_neg_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_810 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, hil⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 39) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, hpx, hpy⟩ := values2_match_inv hp ctx hrest
  have he1 := matchPat_bind_wild_inv ctx hpy
  have he2 := matchPat_bind_wild_inv ctx hpx
  have hy : e1[2]? = some (some (.value y)) := getElem_bind_env (matchPat_bind_inv hpy).1 he1
  obtain ⟨v0, s2, happ⟩ := iflet_term_var_inv ctx (m := m' + 35) hil hy
  obtain ⟨j, infoj, ty', c, hj, hij, hcl, hdj, htyj⟩ :=
    negated_value_inv hp ctx hctx hco (m := m' + 32) happ
  cases hneg : negImm12? ty'.width (imm64OfIconst ty' c) with
  | none =>
    rw [match_810_none hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
    cases hmatch
  | some imm =>
  rw [match_810 hp ctx hco hi hhead hw hd hj hij htyj hdj hneg st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hr : ctx.valueReg? x with
  | none => exact absurd heval (rhs_810_none hp ctx hr st _ n' out (st', tr'))
  | some r =>
  obtain rfl := hctx.valueReg x r hr
  obtain ⟨tr'', he⟩ := rhs_810 hp ctx hco hr hw st _ n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  have hval := dfg_single hdfg hj hij hcl rfl (getAs_ok hy) (a := ⟨ty', c⟩)
    (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
  cases hval
  obtain ⟨hib, hK⟩ := negImm12_value hw v (by unfold negImm12? at hneg; exact hneg)
  refine ⟨fun z hz => ?_, _, ispec_aluRRImm12_add hib, ?_⟩
  · rw [vuseNums_aluRRImm12, List.mem_singleton] at hz
    subst hz
    simp [getAs_ok hx]
  · have := holds_add_K (szOf_bits hw) (hK _ (szOf_bits hw)) (hvals x _ (getAs_ok hx))
    show VHolds ⟨ty, u - v⟩ _
    rwa [← BitVec.sub_eq_add_neg] at this

end Backend.Proof

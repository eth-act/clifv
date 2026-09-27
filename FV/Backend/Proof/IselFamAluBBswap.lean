import FV.Backend.Proof.IselFamAluBBitrev

/-!
# Family B: `bswap` root rules (`lower.isle:2035`, `2038`, `2041`)

`bswap.i16`: 32-bit `rev16` (the low halfword's bytes swapped); `bswap.i32`: 32-bit `rev`;
`bswap.i64`: 64-bit `rev`. (`bswap.i8` is rejected by the verifier and by `instData`.)
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxRecDepth 20000 in
theorem variantNames_Bswap : (variantNames 151)[110]? = some "Bswap" := rfl

theorem bswap_16 (x : BitVec 16) : Clif.Sem.bswap x = (x <<< 8) ||| (x >>> 8) := by
  unfold Clif.Sem.bswap
  simp only [show List.range (16 / 8) = [0, 1] from rfl, List.foldl_cons, List.foldl_nil]
  bv_decide
theorem bswap_32 (x : BitVec 32) : Clif.Sem.bswap x =
    (x <<< 24) ||| ((x <<< 8) &&& 0xFF0000#32) ||| ((x >>> 8) &&& 0xFF00#32) ||| (x >>> 24) := by
  unfold Clif.Sem.bswap
  simp only [show List.range (32 / 8) = [0, 1, 2, 3] from rfl, List.foldl_cons, List.foldl_nil]
  bv_decide
theorem bswap_64 (x : BitVec 64) : Clif.Sem.bswap x =
    (x <<< 56) ||| ((x <<< 40) &&& 0xFF000000000000#64) ||| ((x <<< 24) &&& 0xFF0000000000#64) |||
    ((x <<< 8) &&& 0xFF00000000#64) ||| ((x >>> 8) &&& 0xFF000000#64) |||
    ((x >>> 24) &&& 0xFF0000#64) ||| ((x >>> 40) &&& 0xFF00#64) ||| (x >>> 56) := by
  unfold Clif.Sem.bswap
  simp only [show List.range (64 / 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons,
    List.foldl_nil]
  bv_decide

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_2035 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 16))
    (hd : info.data = .data 152 29 [.data 151 110 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_2035 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_2035]

include hp in
theorem match_2035_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 16)
    (hd : info.data = .data 152 29 [.data 151 110 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_2035 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 16)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_2035]

include hp hc in
theorem rhs_2035 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_2035.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.bitRR .rev16 .size32 (st.fresh .int).1 rx), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 3) (op := .rev16) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 16) (by decide)) rfl rfl a
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_2035, rule_inst_3527, ctor_put_in_reg ctx _ hx]
    rfl

include hp in
theorem rhs_2035_none {x : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_2035.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_2035, rule_inst_3527, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem match_2038 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 32))
    (hd : info.data = .data 152 29 [.data 151 110 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_2038 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_2038]

include hp in
theorem match_2038_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 32)
    (hd : info.data = .data 152 29 [.data 151 110 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_2038 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 32)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_2038]

include hp hc in
theorem rhs_2038 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_2038.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.bitRR .rev32 .size32 (st.fresh .int).1 rx), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 4) (op := .rev32) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_2038, rule_inst_3531, ctor_put_in_reg ctx _ hx]
    rfl

include hp in
theorem rhs_2038_none {x : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_2038.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_2038, rule_inst_3531, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem match_2041 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 64))
    (hd : info.data = .data 152 29 [.data 151 110 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_2041 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_2041]

include hp in
theorem match_2041_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 64)
    (hd : info.data = .data 152 29 [.data 151 110 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_2041 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_2041]

include hp hc in
theorem rhs_2041 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_2041.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.bitRR .rev64 .size64 (st.fresh .int).1 rx), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 5) (op := .rev64) (sz := .size64)
    (fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide) (by decide)) rfl rfl a
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_2041, rule_inst_3535, ctor_put_in_reg ctx _ hx]
    rfl

include hp in
theorem rhs_2041_none {x : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_2041.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_2041, rule_inst_3535, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

end

/-! ## The rule theorems -/

include hp in
/-- **`bswap.i16`** (`lower.isle:2035`). -/
theorem bswap_i16_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2035 :=
  unary_ruleOk hp (cop := .bswap) rfl hp.t2394 term_2394_kind variantNames_Bswap rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) (fun _ _ => True) (fun _ _ => 1)
    (fun _ _ b x => [.bitRR .rev16 .size32 (.vreg b .int) (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 16
      · subst hw
        rw [match_2035 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_2035_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_2035 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_2035_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u _ _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i16) hP (by decide)
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth 16 = u := hu
      subst hu'
      wfix [Clif.Sem.unary, bswap_16, bswap_32, bswap_64, rev16w])

include hp in
/-- **`bswap.i32`** (`lower.isle:2038`). -/
theorem bswap_i32_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2038 :=
  unary_ruleOk hp (cop := .bswap) rfl hp.t2394 term_2394_kind variantNames_Bswap rfl
    (fun _ x => env1 (.value x)) (fun w => w = 32) (fun _ _ => True) (fun _ _ => 1)
    (fun _ _ b x => [.bitRR .rev32 .size32 (.vreg b .int) (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 32
      · subst hw
        rw [match_2038 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_2038_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_2038 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_2038_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u _ _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i32) hP (by decide)
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth 32 = u := hu
      subst hu'
      wfix [Clif.Sem.unary, bswap_16, bswap_32, bswap_64, rev16w])

include hp in
/-- **`bswap.i64`** (`lower.isle:2041`). -/
theorem bswap_i64_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2041 :=
  unary_ruleOk hp (cop := .bswap) rfl hp.t2394 term_2394_kind variantNames_Bswap rfl
    (fun _ x => env1 (.value x)) (fun w => w = 64) (fun _ _ => True) (fun _ _ => 1)
    (fun _ _ b x => [.bitRR .rev64 .size64 (.vreg b .int) (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 64
      · subst hw
        rw [match_2041 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_2041_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_2041 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_2041_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u _ _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i64) hP (by decide)
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth 64 = u := hu
      subst hu'
      wfix [Clif.Sem.unary, bswap_16, bswap_32, bswap_64, rev16w])

end Backend.Proof

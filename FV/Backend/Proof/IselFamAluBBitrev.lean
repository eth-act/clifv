import FV.Backend.Proof.IselFamAluBBase
import FV.Backend.Proof.IselTermsAluB

/-!
# Family B: `bitrev` root rules (`lower.isle:1931`, `1937`, `1946`)

`bitrev.i8`/`bitrev.i16`: `rbit w, x` then `lsr w, #24`/`#16` (the reversed byte/halfword is in
the top bits); `bitrev.i32`/`i64`: one `rbit` (rule `1946`, which also matches at i8/i16 but is
only selected there if the higher-priority rules failed to match, which they cannot).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxRecDepth 20000 in
theorem variantNames_Bitrev : (variantNames 151)[106]? = some "Bitrev" := rfl

theorem sem_eq_beq (a b : V) : (sem ctx).eq a b = (a == b) := rfl

theorem ctor_imm_shift_from_u8_24 (st : LState) :
    externCtor ctx T.imm_shift_from_u8 [.int 24] st = .ok (.op (.immShift 24), st) := rfl
theorem ctor_imm_shift_from_u8_16 (st : LState) :
    externCtor ctx T.imm_shift_from_u8 [.int 16] st = .ok (.op (.immShift 16), st) := rfl

set_option maxRecDepth 20000 in
theorem lower_idx_1931 (hp : Data p) : (p.rulesOf TId.lower)[278]? = some rule_lower_1931 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl
set_option maxRecDepth 20000 in
theorem lower_idx_1937 (hp : Data p) : (p.rulesOf TId.lower)[279]? = some rule_lower_1937 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl
set_option maxRecDepth 20000 in
theorem lower_idx_1946 (hp : Data p) : (p.rulesOf TId.lower)[441]? = some rule_lower_1946 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl

/-! ## Forward lemmas -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_1931 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 8))
    (hd : info.data = .data 152 29 [.data 151 106 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1931 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_1931]

include hp in
theorem match_1931_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 8)
    (hd : info.data = .data 152 29 [.data 151 106 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1931 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 8)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1931]

include hp in
theorem match_1937 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 16))
    (hd : info.data = .data 152 29 [.data 151 106 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1937 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_1937]

include hp in
theorem match_1937_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 16)
    (hd : info.data = .data 152 29 [.data 151 106 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1937 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 16)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1937]

include hp in
theorem match_1946 {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w))
    (hd : info.data = .data 152 29 [.data 151 106 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1946 [.inst i]).run (st, tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  cases hp
  isel_eval [*, rule_lower_1946]

include hp hc in
theorem rhs_1931 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1931.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 1) .int]]),
        (((st.fresh .int).2.emit (.bitRR .rbit .size32 (st.fresh .int).1 rx)).fresh .int).2.emit
          (.aluRRImmShift .lsr .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1 24), tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h4 := fun st tr n a i => alu_rr_imm_shift_run hp ctx hc st tr n (k := 16) (op := .lsr)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h5 := ctor_imm_shift_from_u8_24 ctx
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1931, rule_inst_3512, rule_inst_3375, ctor_put_in_reg ctx _ hx]
    rfl

include hp hc in
theorem rhs_1937 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1937.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 1) .int]]),
        (((st.fresh .int).2.emit (.bitRR .rbit .size32 (st.fresh .int).1 rx)).fresh .int).2.emit
          (.aluRRImmShift .lsr .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1 16), tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h4 := fun st tr n a i => alu_rr_imm_shift_run hp ctx hc st tr n (k := 16) (op := .lsr)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h5 := ctor_imm_shift_from_u8_16 ctx
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1937, rule_inst_3512, rule_inst_3375, ctor_put_in_reg ctx _ hx]
    rfl

include hp hc in
theorem rhs_1946 {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1946.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.bitRR .rbit (szOf w) (st.fresh .int).1 rx), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  by_cases h32 : w ≤ 32
  · have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit)
      (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n h32) rfl rfl a
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w ?h
    case h =>
      isel_eval [*, rule_lower_1946, rule_inst_3512, ctor_put_in_reg ctx _ hx]
      rfl
  · have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit)
      (sz := .size64) (fun st tr n => operand_size_64 hp ctx hc st tr n (by omega) hw) rfl rfl a
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_lower_1946, rule_inst_3512, ctor_put_in_reg ctx _ hx]
      rfl

include hp in
theorem rhs_1931_none {x : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1931.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_1931, rule_inst_3512, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem rhs_1937_none {x : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1937.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_1937, rule_inst_3512, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem rhs_1946_none {x w : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1946.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_1946, rule_inst_3512, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

end

/-! ## The rule theorems -/

include hp in
/-- **`bitrev.i8`** (`lower.isle:1931`). -/
theorem bitrev_i8_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1931 :=
  unary_ruleOk hp (cop := .bitrev) rfl hp.t2390 term_2390_kind variantNames_Bitrev rfl
    (fun _ x => env1 (.value x)) (fun w => w = 8) (fun _ _ => True) (fun _ _ => 2)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmShift .lsr .size32 (.vreg (b + 1) .int) (.vreg b .int) 24]) (fun _ _ b => b + 1)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases h8 : w = 8
      · subst h8
        rw [match_1931 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1931_ne hp ctx st tr m hi hty h8 hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1931 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1931_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u _ _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i8) hP (by decide)
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl) (prun_nil _)), ?_⟩
      have hu' : (ρ x).setWidth 8 = u := hu
      subst hu'
      wfix [Clif.Sem.unary, Clif.Sem.bitrev])

include hp in
/-- **`bitrev.i16`** (`lower.isle:1937`). -/
theorem bitrev_i16_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1937 :=
  unary_ruleOk hp (cop := .bitrev) rfl hp.t2390 term_2390_kind variantNames_Bitrev rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) (fun _ _ => True) (fun _ _ => 2)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmShift .lsr .size32 (.vreg (b + 1) .int) (.vreg b .int) 16]) (fun _ _ b => b + 1)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases h16 : w = 16
      · subst h16
        rw [match_1937 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1937_ne hp ctx st tr m hi hty h16 hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1937 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1937_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u _ _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i16) hP (by decide)
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl) (prun_nil _)), ?_⟩
      have hu' : (ρ x).setWidth 16 = u := hu
      subst hu'
      wfix [Clif.Sem.unary, Clif.Sem.bitrev])

include hp in
/-- **`bitrev.i32`/`bitrev.i64`** (`lower.isle:1946`): a single `rbit`. At i8/i16 the rules
`1931`/`1937`, earlier in `lower`'s order, match, so this rule is not selected there. -/
theorem bitrev_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1946 :=
  unary_ruleOk hp (cop := .bitrev) rfl hp.t2390 term_2390_kind variantNames_Bitrev rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun w => w ≠ 8 ∧ w ≠ 16) (fun _ _ => True)
    (fun _ _ => 1) (fun w _ b x => [.bitRR .rbit (szOf w) (.vreg b .int) (.vreg x .int)])
    (fun _ _ b => b)
    (fun ctx _ ii _ w _ st tr m _ _ hi hty _ hd hfirst h => by
      rw [match_1946 hp ctx st tr m hi hty hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      refine ⟨h.1.symm, h.2.symm, ?_, ?_⟩
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1946 hp) (lower_idx_1931 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1931 hp ctx st tr k hi hty hd] at h'; cases h'
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1946 hp) (lower_idx_1937 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1937 hp ctx st tr k hi hty hd] at h'; cases h')
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_1946 hp ctx hc st tr n hx hw
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1946_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ hP _ _ _ hu => by
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth ty.width = u := hu
      subst hu'
      revert hP
      wcases ty hety [Clif.Sem.unary, Clif.Sem.bitrev, Clif.Ty.width, ne_eq, not_true_eq_false,
        false_and, and_false, false_implies])

end Backend.Proof

import FV.Backend.Proof.IselPrgInv
import FV.Backend.Proof.IselPrgMono
import FV.Backend.Proof.IselFamALUAExtr

/-!
# Progress of the ISLE lowering (V7): the hand-checked rules

`handOk : HandOk f ctx program cfg tab handRules`: the right-hand sides of the two
`extr_32_or_64` rules of `lower` (`rule_lower_1501`, id 862; `rule_lower_1507`, id 863) return a
single-register output from fuel 60, from the environment of any successful match (on any
arguments, from any state, at any fuel).

The match is inverted as V2's rule proofs do (`IselFamALUAExtr`): it is lifted to a large fuel
(`monoAt`), the arguments are one instruction (`root_args`), whose data names the two looked-through
shifts by constants; the result type is `i32`/`i64` (else the match fails: `match_1501_ty`,
`match_*_invalid`); the if-lets hold (`ExtrOk`, else `match_1501_none`), and then the match's
environment is `match_1501`'s. The two shifted operands are operands of statements of `f`, so they
have types (`PInv.argsTyped`) and hence registers (`CtxInv.typedReg`); `rhs_1501` evaluates the
right-hand side from fuel 60. The rule ids 862/863 occur only in `lower`'s rule list
(`handIds_program`, a check over the rule lists' ids).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

/-! ## Generic inversion steps -/

private theorem matchRule_mono_le {ctx : Ctx} {cfg : Config} {m m' : Nat} (hm : m ≤ m')
    {r : Rule} {vs : List V} {s : LState × Array RuleId}
    {res : Option (Isle.Interp.Env V) × (LState × Array RuleId)}
    (h : (matchRule program (sem ctx) cfg m r vs).run s = .ok res) :
    (matchRule program (sem ctx) cfg m' r vs).run s = .ok res := by
  induction hm with
  | refl => exact h
  | step _ ih => exact (monoAt _).mrule _ _ _ _ ih

private theorem ext_inst_data_value_arg {ctx : Ctx} {w : V} {st : LState} {fs : List V}
    (h : externExtract ctx T.inst_data_value w st = .ok fs) : ∃ ii, w = .inst ii := by
  cases w <;> first | exact ⟨_, rfl⟩ | cases h

private theorem ext_value_array_2_arg {ctx : Ctx} {w : V} {st : LState} {fs : List V}
    (h : externExtract ctx T.value_array_2 w st = .ok fs) : ∃ a b, w = .values [a, b] := by
  cases w <;> try cases h
  rename_i xs
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, xs⟩⟩⟩ <;> first | exact ⟨_, _, rfl⟩ | cases h

/-- A rule whose pattern is one `inst_data_value` matched one instruction. -/
private theorem root_args {ctx : Ctx} {cfg : Config} {r : Rule} {qs : List Pattern}
    (hargs : r.args = [.term 18 209 qs]) {m : Nat} {args : List V} {s s1 : LState × Array RuleId}
    {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg (m + 1) r args).run s = .ok (some env, s1)) :
    ∃ ii, args = [.inst ii] := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv h
  rw [hargs] at ha
  cases args with
  | nil => exact (matchArgs_cons_nil ha).elim
  | cons w ws =>
    obtain ⟨e1, hp1, hn⟩ := matchArgs_cons_inv ha
    have := matchArgs_nil_inv hn
    subst this
    obtain ⟨fs, hx, -⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl hp1
    rw [sem_extract] at hx
    obtain ⟨ii, rfl⟩ := ext_inst_data_value_arg hx
    exact ⟨ii, rfl⟩

/-- The fields matched by a `value_array_2` pattern are one value pair. -/
private theorem values2_fields {ctx : Ctx} {st : LState} {qs : List Pattern} {fs : List V}
    {env env' : Isle.Interp.Env V}
    (h : matchArgs program (sem ctx) st [.term 147 1614 qs] fs env = .ok (some env')) :
    ∃ a b, fs = [.values [a, b]] := by
  cases fs with
  | nil => exact (matchArgs_cons_nil h).elim
  | cons w ws =>
    obtain ⟨e1, hp1, hn⟩ := matchArgs_cons_inv h
    have := matchArgs_nil_inv hn
    subst this
    obtain ⟨fs, hx, -⟩ := matchPat_extract_inv data_program.t1614 term_1614_kind rfl hp1
    rw [sem_extract] at hx
    obtain ⟨a, b, rfl⟩ := ext_value_array_2_arg hx
    exact ⟨a, b, rfl⟩

/-- An operand of a binary statement of the context has a register. -/
private theorem binary_operand_reg {f : Clif.Function} {ctx : Ctx} (hP : PInv f ctx) {j : Nat}
    {info : IInfo} {op : Clif.BinaryOp} {ty : Clif.Ty} {x z : Nat} (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.binary op ty x z)) :
    (∃ n, ctx.valueReg? x = some (.vreg n .int)) ∧ ∃ n, ctx.valueReg? z = some (.vreg n .int) := by
  have hof := hP.clifOf j info _ hi hcl
  have hx := hP.argsTyped _ hof x (by simp [Driver.instArgs])
  have hz := hP.argsTyped _ hof z (by simp [Driver.instArgs])
  obtain ⟨tx, htx⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨tz, htz⟩ := Option.isSome_iff_exists.mp hz
  exact ⟨hP.ctxInv.typedSome x tx htx, hP.ctxInv.typedSome z tz htz⟩

/-- The first result type of an instruction: none, or an E integer type. -/
private theorem head_cases {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvW f ctx) {ii : Nat}
    {info : IInfo} (hi : ctx.insts[ii]? = some info) :
    info.resTys.head? = none ∨ ∃ w, info.resTys.head? = some (.int w) := by
  cases hh : info.resTys.head? with
  | none => exact .inl rfl
  | some t =>
    have ht := hctx.resTysE ii info hi t (List.mem_of_head? hh)
    simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> exact .inr ⟨_, rfl⟩

/-! ## No result type -/

section Invalid
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (st : LState) (tr : Array RuleId)
  (n : Nat)

set_option maxRecDepth 20000 in
include hp in
theorem match_1501_invalid {i a b : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = none)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]]) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1501 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_none] at h0
  have h5 : externExtract ctx T.ty_32_or_64 (.ty .invalid) st = .fail := rfl
  cases hp
  isel_eval [*, rule_lower_1501]

set_option maxRecDepth 20000 in
include hp in
theorem match_1507_invalid {i a b : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = none)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]]) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1507 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_none] at h0
  have h5 : externExtract ctx T.ty_32_or_64 (.ty .invalid) st = .fail := rfl
  cases hp
  isel_eval [*, rule_lower_1507]

end Invalid

/-! ## The two rules -/

/-- The single-register output. -/
private theorem γ_regsVec1 {f : Clif.Function} {ctx : Ctx} (r : Reg) :
    γ f ctx (.regsVec (some 1)) (.regsVec [[r]]) :=
  ⟨[[r]], rfl, by simp, .inr rfl⟩

variable {f : Clif.Function} {ctx : Ctx} {cfg : Config}

set_option maxRecDepth 20000 in
/-- **`extr_32_or_64`** (`lower.isle:1501`, rule 862): from any successful match, the
right-hand side returns one single register from fuel 60. -/
theorem hand_1501 (hP : PInv f ctx) (hc : cfg.checkOverlap = false) {args : List V} {m : Nat}
    {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg m rule_lower_1501 args).run s = .ok (some env, s'))
    (n : Nat) (hn : 60 ≤ n) :
    ∃ v s'', (evalExpr program (sem ctx) cfg n rule_lower_1501.rhs env).run s' = .ok (some v, s'') ∧
      γ f ctx (.regsVec (some 1)) v := by
  have hp := data_program
  have hctx := hP.ctxInv
  obtain ⟨st, tr⟩ := s
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  have h' := matchRule_mono_le (m := m) (m' := (m + 1) + 20) (by omega) h
  clear h
  obtain ⟨ii, rfl⟩ := root_args (m := m + 20) rfl h'
  obtain ⟨info, fs, e0, e1, hi, hd, hrest, -⟩ :=
    root_match_inv hp ctx (m := m + 20) rfl hp.t2449 term_2449_kind hp.t2382 term_2382_kind h'
  obtain ⟨a, b, rfl⟩ := values2_fields hrest
  rcases head_cases hctx hi with hhead | ⟨w, hhead⟩
  · rw [match_1501_invalid hp ctx st tr (m + 1) hi hhead hd] at h'; cases h'
  cases Classical.em (w = 32 ∨ w = 64) with
  | inr hnw => rw [match_1501_ty hp ctx st tr (m + 1) hi hhead hnw hd] at h'; cases h'
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := hctx.clif hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, x, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := hctx.clif hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty3, k3, rfl, rfl⟩ := instData_iconst_inv hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := hctx.clif hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, y, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := hctx.clif hj4 hij4
  rw [hd4] at hdat4
  obtain ⟨ty4, k4, rfl, rfl⟩ := instData_iconst_inv hdat4
  cases Classical.em (ExtrOk w (u64 (imm64OfIconst ty3 k3)) (u64 (imm64OfIconst ty4 k4))) with
  | inr hnok =>
    rw [match_1501_none hp ctx st tr (m + 1) hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3
      hd3 hj4 hij4 hd4 hnok] at h'
    cases h'
  | inl hok =>
  rw [match_1501 hp ctx st tr (m + 1) hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4
    hij4 hd4 hok] at h'
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  obtain ⟨-, -, -, hY64, -, -⟩ := extrOk_nat (by omega) hok
  obtain ⟨_, hrx⟩ := (binary_operand_reg hP hij1 hcl1).1
  obtain ⟨_, hry⟩ := (binary_operand_reg hP hij3 hcl3).1
  obtain ⟨tr'', sh, -, he'⟩ := rhs_1501 hp ctx hc st tr n' hrx hry hw hY64
  exact ⟨_, _, he', γ_regsVec1 _⟩

set_option maxRecDepth 20000 in
/-- **`extr_32_or_64_2`** (`lower.isle:1507`, rule 863): from any successful match, the
right-hand side returns one single register from fuel 60. -/
theorem hand_1507 (hP : PInv f ctx) (hc : cfg.checkOverlap = false) {args : List V} {m : Nat}
    {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg m rule_lower_1507 args).run s = .ok (some env, s'))
    (n : Nat) (hn : 60 ≤ n) :
    ∃ v s'', (evalExpr program (sem ctx) cfg n rule_lower_1507.rhs env).run s' = .ok (some v, s'') ∧
      γ f ctx (.regsVec (some 1)) v := by
  have hp := data_program
  have hctx := hP.ctxInv
  obtain ⟨st, tr⟩ := s
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  have h' := matchRule_mono_le (m := m) (m' := (m + 1) + 20) (by omega) h
  clear h
  obtain ⟨ii, rfl⟩ := root_args (m := m + 20) rfl h'
  obtain ⟨info, fs, e0, e1, hi, hd, hrest, -⟩ :=
    root_match_inv hp ctx (m := m + 20) rfl hp.t2449 term_2449_kind hp.t2382 term_2382_kind h'
  obtain ⟨a, b, rfl⟩ := values2_fields hrest
  rcases head_cases hctx hi with hhead | ⟨w, hhead⟩
  · rw [match_1507_invalid hp ctx st tr (m + 1) hi hhead hd] at h'; cases h'
  cases Classical.em (w = 32 ∨ w = 64) with
  | inr hnw => rw [match_1507_ty hp ctx st tr (m + 1) hi hhead hnw hd] at h'; cases h'
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := hctx.clif hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, y, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := hctx.clif hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty4, k4, rfl, rfl⟩ := instData_iconst_inv hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := hctx.clif hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, x, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := hctx.clif hj4 hij4
  rw [hd4] at hdat4
  obtain ⟨ty3, k3, rfl, rfl⟩ := instData_iconst_inv hdat4
  cases Classical.em (ExtrOk w (u64 (imm64OfIconst ty3 k3)) (u64 (imm64OfIconst ty4 k4))) with
  | inr hnok =>
    rw [match_1507_none hp ctx st tr (m + 1) hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3
      hd3 hj4 hij4 hd4 hnok] at h'
    cases h'
  | inl hok =>
  rw [match_1507 hp ctx st tr (m + 1) hi hhead hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4
    hij4 hd4 hok] at h'
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  obtain ⟨-, -, -, hY64, -, -⟩ := extrOk_nat (by omega) hok
  obtain ⟨_, hrx⟩ := (binary_operand_reg hP hij3 hcl3).1
  obtain ⟨_, hry⟩ := (binary_operand_reg hP hij1 hcl1).1
  obtain ⟨tr'', sh, -, he'⟩ := rhs_1507 hp ctx hc st tr n' hrx hry hw hY64
  exact ⟨_, _, he', γ_regsVec1 _⟩

/-! ## The rule ids and `HandOk` -/

/-- No rule of `rs` has id 862 or 863. -/
def noHandIds (rs : List Rule) : Bool := rs.all fun r => !(r.id == 862 || r.id == 863)

/-- The rule lists from term `t` on: only `lower`'s (term 686) has rules 862/863. -/
def handIdsOk : Nat → List (List Rule) → Bool
  | _, [] => true
  | t, rs :: rss => (t == TId.lower || noHandIds rs) && handIdsOk (t + 1) rss

set_option maxRecDepth 100000 in
theorem handIds_program : handIdsOk 0 program.ruleLists.toList = true := by decide +kernel

private theorem handIdsOk_get : ∀ {k : Nat} {L : List (List Rule)}, handIdsOk k L = true →
    ∀ (i : Nat) (rs : List Rule), L[i]? = some rs → ∀ r ∈ rs, (r.id = 862 ∨ r.id = 863) →
      k + i = TId.lower
  | _, [], _, i, rs, hi, _, _, _ => by simp at hi
  | k, rs0 :: L, h, i, rs, hi, r, hr, hid => by
    simp only [handIdsOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rcases h.1 with h1 | h1
      · simpa using h1
      · have := List.all_eq_true.mp h1 r hr
        rcases hid with hid | hid <;> simp [hid] at this
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := handIdsOk_get h.2 i rs hi r hr hid
      omega

/-- Rules 862/863 belong to `lower` only. -/
theorem handIds_term {t : TermId} {r : Rule} (hr : r ∈ program.rulesOf t)
    (hid : r.id = 862 ∨ r.id = 863) : t = TId.lower := by
  unfold Program.rulesOf at hr
  cases ht : program.ruleLists[t]? with
  | none => rw [ht] at hr; cases hr
  | some rs =>
    rw [ht] at hr
    have h := handIdsOk_get handIds_program t rs (by rw [← Array.getElem?_toList] at ht; exact ht)
      r hr hid
    simpa using h

set_option maxRecDepth 100000 in
theorem lower_rule_862 :
    (program.rulesOf TId.lower).filter (fun r => r.id == 862) = [rule_lower_1501] := by
  rw [show TId.lower = 686 from rfl, program_rulesOf_686]; decide +kernel

set_option maxRecDepth 100000 in
theorem lower_rule_863 :
    (program.rulesOf TId.lower).filter (fun r => r.id == 863) = [rule_lower_1507] := by
  rw [show TId.lower = 686 from rfl, program_rulesOf_686]; decide +kernel

private theorem rule_of_id {t : TermId} {r : Rule} (hr : r ∈ program.rulesOf t) {k : Nat}
    {r0 : Rule} (hk : k = 862 ∨ k = 863)
    (hf : (program.rulesOf TId.lower).filter (fun r => r.id == k) = [r0]) (hid : r.id = k) :
    r = r0 := by
  have ht := handIds_term hr (by rw [hid]; exact hk)
  subst ht
  have hm : r ∈ (program.rulesOf TId.lower).filter (fun r => r.id == k) :=
    List.mem_filter.mpr ⟨hr, by simp [hid]⟩
  rw [hf] at hm
  exact List.mem_singleton.mp hm

/-- **The hand-checked rules return** (`HandOk`): `extr_32_or_64` and `extr_32_or_64_2`, from
fuel 60, return one single register (`handRules`), for every table. -/
theorem handOk (hP : PInv f ctx) (hc : cfg.checkOverlap = false) (tab : PTab) :
    HandOk f ctx program cfg tab handRules := by
  intro e _ r hr c a hh args _ m s env s' hmatch n hn
  simp only [handRules] at hh
  split at hh
  · rename_i hid
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp only [Bool.or_eq_true, beq_iff_eq] at hid
    rcases hid with hid | hid
    · obtain rfl := rule_of_id hr (.inl rfl) lower_rule_862 hid
      exact hand_1501 hP hc hmatch n hn
    · obtain rfl := rule_of_id hr (.inr rfl) lower_rule_863 hid
      exact hand_1507 hP hc hmatch n hn
  · cases hh

end Backend.Proof.Prg

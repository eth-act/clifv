module

public import FV.Backend.Proof.IselPrgHand
public import FV.Backend.Proof.IselPrgInvT
public import FV.Backend.Proof.IselFamALUATI
public import FV.Backend.Proof.IselFamALUALogic

@[expose] public section

/-!
# Progress of the ISLE lowering over the typed scope: V7's hand-checked rules

`hand_1501T`, `hand_1507T`: `hand_1501`/`hand_1507` (`IselPrgHand`) over the typed scope
(`PInvT`). The proofs are V7's, with two changes: the matched `bor`'s result type is an E integer
by its data (`head_borT`; a slot without CLIF instruction has none, `PInvT.noClifRes`), and the two
shifted operands are in integer positions (`intArgs` of a binary instruction), so their vregs are
X registers (`binary_operand_regT`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

private theorem matchRule_mono_leT {ctx : Ctx} {cfg : Config} {m m' : Nat} (hm : m ≤ m')
    {r : Rule} {vs : List V} {s : LState × Array RuleId}
    {res : Option (Isle.Interp.Env V) × (LState × Array RuleId)}
    (h : (matchRule program (sem ctx) cfg m r vs).run s = .ok res) :
    (matchRule program (sem ctx) cfg m' r vs).run s = .ok res := by
  induction hm with
  | refl => exact h
  | step _ ih => exact (monoAt _).mrule _ _ _ _ ih

private theorem ext_inst_data_value_argT {ctx : Ctx} {w : V} {st : LState} {fs : List V}
    (h : externExtract ctx T.inst_data_value w st = .ok fs) : ∃ ii, w = .inst ii := by
  cases w <;> first | exact ⟨_, rfl⟩ | cases h

private theorem ext_value_array_2_argT {ctx : Ctx} {w : V} {st : LState} {fs : List V}
    (h : externExtract ctx T.value_array_2 w st = .ok fs) : ∃ a b, w = .values [a, b] := by
  cases w <;> try cases h
  rename_i xs
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, xs⟩⟩⟩ <;> first | exact ⟨_, _, rfl⟩ | cases h

private theorem root_argsT {ctx : Ctx} {cfg : Config} {r : Rule} {qs : List Pattern}
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
    obtain ⟨ii, rfl⟩ := ext_inst_data_value_argT hx
    exact ⟨ii, rfl⟩

private theorem values2_fieldsT {ctx : Ctx} {st : LState} {qs : List Pattern} {fs : List V}
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
    obtain ⟨a, b, rfl⟩ := ext_value_array_2_argT hx
    exact ⟨a, b, rfl⟩

/-- An operand of a binary statement of the context is in an integer position: its vreg is an X
register. -/
private theorem binary_operand_regT {f : Clif.Function} {ctx : Ctx} (hP : PInvTB f ctx) {j : Nat}
    {info : IInfo} {op : Clif.BinaryOp} {ty : Clif.Ty} {x z : Nat} (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.binary op ty x z)) :
    ctx.valueReg? x = some (.vreg x .int) ∧ ctx.valueReg? z = some (.vreg z .int) := by
  have hof := hP.clifOf j info _ hi hcl
  have hx := hP.argsTyped _ hof x (by simp [Driver.instArgs])
  have hz := hP.argsTyped _ hof z (by simp [Driver.instArgs])
  obtain ⟨tx, htx⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨tz, htz⟩ := Option.isSome_iff_exists.mp hz
  have hix := hP.intArgsOf _ hof x (by simp [intArgs]) tx htx
  have hiz := hP.intArgsOf _ hof z (by simp [intArgs]) tz htz
  rw [hP.ctxInv.typedReg x tx htx, hP.ctxInv.typedReg z tz htz, valClass_of_eCTys hix,
    valClass_of_eCTys hiz]
  exact ⟨rfl, rfl⟩

/-- The first result type of a matched `bor` instruction of a float-capable context: none (a slot
without CLIF instruction) or an E integer (the `bor` is E's). -/
private theorem head_borT {f : Clif.Function} {ctx : Ctx} (hP : PInvTB f ctx) {ii : Nat}
    {info : IInfo} {a b : Nat} (hi : ctx.insts[ii]? = some info)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]]) :
    info.resTys.head? = none ∨ ∃ w, info.resTys.head? = some (.int w) := by
  cases hcl : info.clif with
  | none => left; rw [hP.noClifRes ii info hi hcl]; rfl
  | some c =>
    have hdat := hP.ctxInv.data ii info c hi hcl
    rw [hd] at hdat
    obtain ⟨ty, x, y, rfl, he, -⟩ := instData_binary_inv variantNames_Bor (cop := .bor) rfl hdat
    obtain ⟨tys, hrt, hres, -⟩ := hP.ctxInv.resTys ii info _ hi hcl
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at hrt
    subst hrt
    rw [hres]
    right
    cases ty <;> simp_all [eTy, Clif.Ty.isInt, CTy.ofClif]

/-! ## The two rules over the typed scope -/

/-- The single-register output. -/
private theorem γ_regsVec1T {f : Clif.Function} {ctx : Ctx} (r : Reg) :
    γ f ctx (.regsVec (some 1)) (.regsVec [[r]]) :=
  ⟨[[r]], rfl, by simp, .inr rfl⟩

variable {f : Clif.Function} {ctx : Ctx} {cfg : Config}

set_option maxRecDepth 20000 in
/-- **`extr_32_or_64`** (`lower.isle:1501`, rule 862) over a float-capable context: from any
successful match, the right-hand side returns one single register from fuel 60. -/
theorem hand_1501TB (hP : PInvTB f ctx) (hc : cfg.checkOverlap = false) {args : List V} {m : Nat}
    {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg m rule_lower_1501 args).run s = .ok (some env, s'))
    (n : Nat) (hn : 60 ≤ n) :
    ∃ v s'', (evalExpr program (sem ctx) cfg n rule_lower_1501.rhs env).run s' = .ok (some v, s'') ∧
      γ f ctx (.regsVec (some 1)) v := by
  have hp := data_program
  have hctx := hP.ctxInv
  obtain ⟨st, tr⟩ := s
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  have h' := matchRule_mono_leT (m := m) (m' := (m + 1) + 20) (by omega) h
  clear h
  obtain ⟨ii, rfl⟩ := root_argsT (m := m + 20) rfl h'
  obtain ⟨info, fs, e0, e1, hi, hd, hrest, -⟩ :=
    root_match_inv hp ctx (m := m + 20) rfl hp.t2449 term_2449_kind hp.t2382 term_2382_kind h'
  obtain ⟨a, b, rfl⟩ := values2_fieldsT hrest
  rcases head_borT hP hi hd with hhead | ⟨w, hhead⟩
  · rw [match_1501_invalid hp ctx st tr (m + 1) hi hhead hd] at h'; cases h'
  cases Classical.em (w = 32 ∨ w = 64) with
  | inr hnw => rw [match_1501_ty hp ctx st tr (m + 1) hi hhead hnw hd] at h'; cases h'
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clifTI hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, x, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clifTI hctx hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty3, k3, rfl, rfl⟩ := instData_iconst_inv hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := ctxInv_clifTI hctx hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, y, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := ctxInv_clifTI hctx hj4 hij4
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
  have hrx := (binary_operand_regT hP hij1 hcl1).1
  have hry := (binary_operand_regT hP hij3 hcl3).1
  obtain ⟨tr'', sh, -, he'⟩ := rhs_1501 hp ctx hc st tr n' hrx hry hw hY64
  exact ⟨_, _, he', γ_regsVec1T _⟩

set_option maxRecDepth 20000 in
/-- **`extr_32_or_64_2`** (`lower.isle:1507`, rule 863) over a float-capable context: from any
successful match, the right-hand side returns one single register from fuel 60. -/
theorem hand_1507TB (hP : PInvTB f ctx) (hc : cfg.checkOverlap = false) {args : List V} {m : Nat}
    {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg m rule_lower_1507 args).run s = .ok (some env, s'))
    (n : Nat) (hn : 60 ≤ n) :
    ∃ v s'', (evalExpr program (sem ctx) cfg n rule_lower_1507.rhs env).run s' = .ok (some v, s'') ∧
      γ f ctx (.regsVec (some 1)) v := by
  have hp := data_program
  have hctx := hP.ctxInv
  obtain ⟨st, tr⟩ := s
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  have h' := matchRule_mono_leT (m := m) (m' := (m + 1) + 20) (by omega) h
  clear h
  obtain ⟨ii, rfl⟩ := root_argsT (m := m + 20) rfl h'
  obtain ⟨info, fs, e0, e1, hi, hd, hrest, -⟩ :=
    root_match_inv hp ctx (m := m + 20) rfl hp.t2449 term_2449_kind hp.t2382 term_2382_kind h'
  obtain ⟨a, b, rfl⟩ := values2_fieldsT hrest
  rcases head_borT hP hi hd with hhead | ⟨w, hhead⟩
  · rw [match_1507_invalid hp ctx st tr (m + 1) hi hhead hd] at h'; cases h'
  cases Classical.em (w = 32 ∨ w = 64) with
  | inr hnw => rw [match_1507_ty hp ctx st tr (m + 1) hi hhead hnw hd] at h'; cases h'
  | inl hw =>
  obtain ⟨e2, hpa, hpb⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j1, info1, fs1, e3, hj1, hij1, hd1, hrest1⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2388 term_2388_kind hpa
  obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clifTI hctx hj1 hij1
  rw [hd1] at hdat1
  obtain ⟨ty1, y, c1, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ushr (cop := .ushr) rfl hdat1
  obtain ⟨e4, -, hpc1⟩ := values2_match_inv hp ctx hrest1
  obtain ⟨j2, info2, fs2, e5, hj2, hij2, hd2, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc1
  obtain ⟨cl2, hcl2, hdat2⟩ := ctxInv_clifTI hctx hj2 hij2
  rw [hd2] at hdat2
  obtain ⟨ty4, k4, rfl, rfl⟩ := instData_iconst_inv hdat2
  obtain ⟨j3, info3, fs3, e6, hj3, hij3, hd3, hrest3⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind hp.t2387 term_2387_kind hpb
  obtain ⟨cl3, hcl3, hdat3⟩ := ctxInv_clifTI hctx hj3 hij3
  rw [hd3] at hdat3
  obtain ⟨ty2, x, c2, rfl, -, rfl⟩ := instData_binary_inv variantNames_Ishl (cop := .ishl) rfl hdat3
  obtain ⟨e7, -, hpc2⟩ := values2_match_inv hp ctx hrest3
  obtain ⟨j4, info4, fs4, e8, hj4, hij4, hd4, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpc2
  obtain ⟨cl4, hcl4, hdat4⟩ := ctxInv_clifTI hctx hj4 hij4
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
  have hrx := (binary_operand_regT hP hij3 hcl3).1
  have hry := (binary_operand_regT hP hij1 hcl1).1
  obtain ⟨tr'', sh, -, he'⟩ := rhs_1507 hp ctx hc st tr n' hrx hry hw hY64
  exact ⟨_, _, he', γ_regsVec1T _⟩

/-- Rules 862/863 of `lower`, by id. -/
private theorem rule_of_idT {t : TermId} {r : Rule} (hr : r ∈ program.rulesOf t) {k : Nat}
    {r0 : Rule} (hk : k = 862 ∨ k = 863)
    (hf : (program.rulesOf TId.lower).filter (fun r => r.id == k) = [r0]) (hid : r.id = k) :
    r = r0 := by
  have ht := handIds_term hr (by rw [hid]; exact hk)
  subst ht
  have hm : r ∈ (program.rulesOf TId.lower).filter (fun r => r.id == k) :=
    List.mem_filter.mpr ⟨hr, by simp [hid]⟩
  rw [hf] at hm
  exact List.mem_singleton.mp hm

/-- **V7's hand-checked rules return over a float-capable context**: a rule `handRules` names,
from any successful match, returns its right-hand side's value from its fuel. -/
theorem handRules_okTB (hP : PInvTB f ctx) (hc : cfg.checkOverlap = false) {t : TermId} {r : Rule}
    (hr : r ∈ program.rulesOf t) {c : Nat} {a : PA} (hh : handRules r.id = some (c, a))
    {args : List V} {m : Nat} {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (hmatch : (matchRule program (sem ctx) cfg m r args).run s = .ok (some env, s'))
    (n : Nat) (hn : c ≤ n) :
    ∃ (v : V) (s'' : LState × Array RuleId),
      (evalExpr program (sem ctx) cfg n r.rhs env).run s' = .ok (some v, s'') ∧ γ f ctx a v := by
  simp only [handRules] at hh
  split at hh
  · rename_i hid
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp only [Bool.or_eq_true, beq_iff_eq] at hid
    rcases hid with hid | hid
    · obtain rfl := rule_of_idT hr (.inl rfl) lower_rule_862 hid
      exact hand_1501TB hP hc hmatch n hn
    · obtain rfl := rule_of_idT hr (.inr rfl) lower_rule_863 hid
      exact hand_1507TB hP hc hmatch n hn
  · cases hh

/-- `hand_1501TB` under `PInvT`. -/
theorem hand_1501T (hP : PInvT f ctx) (hc : cfg.checkOverlap = false) {args : List V} {m : Nat}
    {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg m rule_lower_1501 args).run s = .ok (some env, s'))
    (n : Nat) (hn : 60 ≤ n) :
    ∃ v s'', (evalExpr program (sem ctx) cfg n rule_lower_1501.rhs env).run s' = .ok (some v, s'') ∧
      γ f ctx (.regsVec (some 1)) v :=
  hand_1501TB hP.toB hc h n hn

/-- `hand_1507TB` under `PInvT`. -/
theorem hand_1507T (hP : PInvT f ctx) (hc : cfg.checkOverlap = false) {args : List V} {m : Nat}
    {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg m rule_lower_1507 args).run s = .ok (some env, s'))
    (n : Nat) (hn : 60 ≤ n) :
    ∃ v s'', (evalExpr program (sem ctx) cfg n rule_lower_1507.rhs env).run s' = .ok (some v, s'') ∧
      γ f ctx (.regsVec (some 1)) v :=
  hand_1507TB hP.toB hc h n hn

/-- **V7's hand-checked rules return over the typed scope** (`handRules_okTB` under `PInvT`). -/
theorem handRules_okT (hP : PInvT f ctx) (hc : cfg.checkOverlap = false) {t : TermId} {r : Rule}
    (hr : r ∈ program.rulesOf t) {c : Nat} {a : PA} (hh : handRules r.id = some (c, a))
    {args : List V} {m : Nat} {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (hmatch : (matchRule program (sem ctx) cfg m r args).run s = .ok (some env, s'))
    (n : Nat) (hn : c ≤ n) :
    ∃ (v : V) (s'' : LState × Array RuleId),
      (evalExpr program (sem ctx) cfg n r.rhs env).run s' = .ok (some v, s'') ∧ γ f ctx a v :=
  handRules_okTB hP.toB hc hr hh hmatch n hn

end Backend.Proof.Prg

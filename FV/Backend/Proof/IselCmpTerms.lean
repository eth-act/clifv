import FV.Backend.Proof.IselCmpBase

/-!
# Contracts of the small helper terms of the compare family

Each lemma: an internal constructor call that returned a value (`ApplyInternal`) returned
exactly this value and left the lowering state unchanged (only the trace grew). Proved by
inverse evaluation over every rule of the term (`applyTerm_internal_some`, `isel_inv`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hc in
/-- Split an internal-term call into its rules: the rule that fired, matched with fuel
`m' + 20` and evaluated with fuel `n' + 20`. -/
theorem internal_split {ty : TypeId} {t : TermId} {vs : List V} {term : Term} {flags : TermFlags}
    {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n ty t vs s v s') :
    ∃ r ∈ p.rulesOf t, ∃ m' n' env s1 st tr,
      (matchRule p (sem ctx) cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p (sem ctx) cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) := by
  obtain ⟨r, hr, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ := applyTerm_internal_some hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  exact ⟨r, hr, m', n', env, s1, st, tr, hmt, he, rfl⟩

include hc in
/-- `internal_split` with first-match selection: the rules before the committed one failed to
match (from the same start state). The right-hand side runs with the call's fuel
(`n = n' + 20`), so nested calls keep a known amount of fuel. -/
theorem internal_split_first {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p (sem ctx) cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p (sem ctx) cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p (sem ctx) cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) ∧ n = n' + 20 := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩

open Lean in
/-- `isel_split hp hc h t`: split the internal call `h : ApplyInternal … t …` into one goal per
rule of term `t`, with hypotheses `hm` (the match), `he` (the right-hand side) and `hpre`
(the earlier rules failed), after `cases hp` (data facts in context). -/
macro "isel_split " hp:ident hc:ident h:ident t:num : tactic => do
  let tN := mkIdent (hp.getId ++ Name.mkSimple s!"t{t.getNat}")
  let rN := mkIdent (hp.getId ++ Name.mkSimple s!"r{t.getNat}")
  let kN := mkIdent (Name.mkStr `Backend.Proof s!"term_{t.getNat}_kind")
  let hm := mkIdent `hm
  let he := mkIdent `he
  let hpre := mkIdent `hpre
  let hL := mkIdent `hL
  `(tactic| (
    obtain ⟨_, _, _, $hL, $hpre, _, _, _, _, _, _, $hm, $he, rfl, rfl⟩ := internal_split_first $hc $tN $kN rfl (by rw [$rN:ident]; simp; omega) $h
    rw [$rN:ident] at $hL:ident
    isel_rule_cases $hL
    all_goals cases $hp:ident))

open Lean in
/-- `isel_split'`: `isel_split` keeping `hp` (for `isel_inv'`). -/
macro "isel_split' " hp:ident hc:ident h:ident t:num : tactic => do
  let tN := mkIdent (hp.getId ++ Name.mkSimple s!"t{t.getNat}")
  let rN := mkIdent (hp.getId ++ Name.mkSimple s!"r{t.getNat}")
  let kN := mkIdent (Name.mkStr `Backend.Proof s!"term_{t.getNat}_kind")
  let hm := mkIdent `hm
  let he := mkIdent `he
  let hpre := mkIdent `hpre
  let hL := mkIdent `hL
  `(tactic| (
    obtain ⟨_, _, _, $hL, $hpre, _, _, _, _, _, _, $hm, $he, rfl, rfl⟩ := internal_split_first $hc $tN $kN rfl (by rw [$rN:ident]; simp; omega) $h
    clear $h
    rw [$rN:ident] at $hL:ident
    isel_rule_cases $hL))

/-! ## `operand_size` -/

include hp hc in
theorem operand_size_ok {n : Nat} (hn : 30 ≤ n) {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 93 305 [.ty t] s v s') :
    s'.1 = s.1 ∧ ((t.bits ≤ 32 ∧ v = .data 93 0 []) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ v = .data 93 1 [])) := by
  obtain ⟨pre, r, post, hL, hpre, m', n', env, s1, st, tr, hm, he, rfl, rfl⟩ :=
    internal_split_first hc hp.t305 term_305_kind rfl (by rw [hp.r305]; simp; omega) h
  rw [hp.r305] at hL
  isel_rule_cases hL
  all_goals cases hp
  · isel_inv [*, rule_inst_1592] at hm he
    exact .inl ‹_›
  · obtain ⟨k, s2, h2⟩ := hpre _ (List.mem_singleton_self _)
    isel_inv [*, rule_inst_1593] at hm he
    refine .inr ⟨Nat.lt_of_not_le fun h32 => ?_, ‹_›⟩
    revert h2
    isel_eval [*, rule_inst_1592, ext_fits_in_32', h32]
    simp

end Backend.Proof

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## Flag producers (`cmp`, `cmp_imm`, `cmp_extend`, `tst_imm`) and consumers (`cset`, `csel`) -/

include hp hc in
theorem cmp_ok {n : Nat} (hn : 30 ≤ n) {a b c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 47 390 [a, b, c] s v s') :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 2 [.data 59 10 [], a, .reg .xzr, b, c]] := by
  isel_split hp hc h 390
  isel_inv [*, rule_inst_2767] at hm he

include hp hc in
theorem cmp_imm_ok {n : Nat} (hn : 30 ≤ n) {a b c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 47 391 [a, b, c] s v s') :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 4 [.data 59 10 [], a, .reg .xzr, b, c]] := by
  isel_split hp hc h 391
  isel_inv [*, rule_inst_2774] at hm he

include hp hc in
theorem cmp_extend_ok {n : Nat} (hn : 30 ≤ n) {a b c d : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 47 393 [a, b, c, d] s v s') :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 8 [.data 59 10 [], a, .reg .xzr, b, c, d]] := by
  isel_split hp hc h 393
  isel_inv [*, rule_inst_2786] at hm he

include hp hc in
theorem cset_ok {n : Nat} (hn : 30 ≤ n) {c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 49 426 [c] s v s') :
    s'.1 = (s.1.fresh .int).2 ∧
      v = .data 49 3 [.data 58 33 [.reg (s.1.fresh .int).1, c], .reg (s.1.fresh .int).1] := by
  isel_split hp hc h 426
  isel_inv [*, rule_inst_3068] at hm he

include hp hc in
theorem csel_ok {n : Nat} (hn : 30 ≤ n) {c a b : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 49 425 [c, a, b] s v s') :
    s'.1 = (s.1.fresh .int).2 ∧
      v = .data 49 3 [.data 58 31 [.reg (s.1.fresh .int).1, c, a, b], .reg (s.1.fresh .int).1] := by
  isel_split hp hc h 425
  isel_inv [*, rule_inst_3059] at hm he

/-! ## `extend` and `put_in_reg_{s,z}ext32` -/

include hp hc in
theorem extend_ok {n : Nat} (hn : 30 ≤ n) {rn sg a b : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 417 [rn, sg, a, b] s v s') :
    v = .reg (s.1.fresh .int).1 ∧ ∃ m, MInst.ofV (.data 58 28 [.reg (s.1.fresh .int).1, rn, sg, a, b]) = some m ∧
      s'.1 = (s.1.fresh .int).2.emit m := by
  isel_split hp hc h 417
  isel_inv [*, rule_inst_2991] at hm he
  exact ⟨_, ‹_›, rfl⟩

theorem ofV_extend (rd rn : Reg) (sg : Bool) (a b : Nat) :
    MInst.ofV (.data 58 28 [.reg rd, .reg rn, .bool sg, .int (a : Int), .int (b : Int)]) =
      some (.extend rd rn sg a b) := rfl

theorem getAs_typed {fr : Clif.Frame} (hd : DFGCons ctx fr) {x : Nat} {t : CTy} {ty : Clif.Ty}
    {u : BitVec ty.width} (ht : ctx.valueType? x = some t) (hx : fr.getAs x ty = .ok u) :
    t = CTy.ofClif ty := (hd.2 x t _ ht (getAs_ok hx)).symm

theorem operands_extend (d x : Nat) (sg : Bool) (a b : Nat) :
    (MInst.extend (.vreg d .int) (.vreg x .int) sg a b).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] := rfl

theorem ofV_extend_32 (rd rn : Reg) (sg : Bool) (a : Nat) :
    MInst.ofV (.data 58 28 [.reg rd, .reg rn, .bool sg, .int (a : Int), .int 32]) =
      some (.extend rd rn sg a 32) := rfl

theorem opnd32_setWidth (a : CV) : opnd .size32 a = a.setWidth 32 := by
  simp only [opnd, lo64, OperandSize.bits, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]

theorem ty_width_le_32 {ty : Clif.Ty} (h : ty.width ≤ 32) :
    ty = .i8 ∨ ty = .i16 ∨ ty = .i32 := by
  cases ty <;> simp_all [Clif.Ty.width]

variable {F : BitVec 64 → Prop} {isem : Sem}

end Backend.Proof

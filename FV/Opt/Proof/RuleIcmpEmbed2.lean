import FV.Opt.Proof.RuleIcmpEmbed

/-!
# Template variants for `opts/icmp.isle` (part 2): signed immediates

`iconst_s` extractors bind `toInt` of the constant's bits; a variable bound twice gives
`a.toInt = b.toInt`, and `i64_lt`/`i64_gt_eq` if-lets compare it with `0`. `rule_bits_e` turns
both into `BitVec` facts (`toInt_inj`, the sign bit) before `bv_decide`. The `uextend_maybe`
multi-extractor (`extractMulti_uem`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

section
variable {σ : Type} (G : EGraph σ)

/-- `uextend` nodes are the only ones `maybeUnary` accepts for `Uextend`. -/
theorem uextHit (ct : CTy) (i : Inst) (fs : List V) :
    (∃ d, ofInst i = some d ∧ (match d with
      | .data _ VIdx.«InstructionData».«Unary» [.data _ o [], x] =>
          if o == VIdx.«Opcode».«Uextend» then some [V.ty ct, x] else none
      | _ => none) = some fs) ↔
    ∃ t' y, i = .extend .uextend t' y ∧ fs = [.ty ct, .value y] := by
  constructor
  · rintro ⟨d, hd, hm⟩
    cases i
    case iconst t imm =>
      cases t <;> simp [ofInst, idata, opcode] at hd <;> subst hd <;> simp at hm
    case unary op t x =>
      simp [ofInst, idata, opcode] at hd; subst hd; simp at hm
      exact absurd hm.1 (by cases op <;> decide)
    case extend op t x =>
      cases op <;> simp [ofInst, idata, opcode] at hd <;> subst hd <;> simp at hm
      exact ⟨t, x, rfl, hm.symm⟩
    all_goals (simp [ofInst, idata, opcode] at hd)
    all_goals (try subst hd)
    all_goals (try simp at hm)
    all_goals (exact absurd hm.1 (by decide))
  · rintro ⟨t', y, rfl, rfl⟩
    exact ⟨_, rfl, by simp [idata, opcode]⟩

/-- The hits of `maybeUnary` for `uextend` (as in `Isle.Opt.maybeUnary`). -/
def uextHits (st : St σ) (n : Nat) (t : Ty) : List (List V) :=
  ((G.enodes st.inner n).filterMap fun i => (ofInst i).map (CTy.ofClif t, ·)).filterMap
    fun (t, d) =>
      match d with
      | .data _ VIdx.«InstructionData».«Unary» [.data _ o [], x] =>
          if o == VIdx.«Opcode».«Uextend» then some [.ty t, x] else none
      | _ => none

theorem maybeUnary_uext_eq (st : St σ) (n : Nat) (t : Ty) (h : G.typeOf st.inner n = some t) :
    maybeUnary G st VIdx.«Opcode».«Uextend» (.value n) =
      .ok (if (uextHits G st n t).isEmpty then [[.ty (CTy.ofClif t), .value n]]
        else uextHits G st n t) := by
  unfold maybeUnary nodesOf valueType
  simp only [h, bind, Except.bind, pure, Except.pure]
  exact (apply_ite Except.ok _ _ _).symm

theorem mem_uextHits (st : St σ) (n : Nat) (t : Ty) (fs : List V) :
    fs ∈ uextHits G st n t ↔ ∃ t' y, Inst.extend .uextend t' y ∈ G.enodes st.inner n ∧
        fs = [.ty (CTy.ofClif t), .value y] := by
  simp only [uextHits, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨ct, d⟩, ⟨i, hi, d', hd, he⟩, hm⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨t', y, rfl, rfl⟩ := (uextHit (CTy.ofClif t) i fs).1 ⟨d', hd, hm⟩
    exact ⟨t', y, hi, rfl⟩
  · rintro ⟨t', y, hi, rfl⟩
    exact ⟨(CTy.ofClif t, _), ⟨_, hi, _, rfl, rfl⟩, by simp [idata, opcode]⟩

theorem maybeUnary_uext (st : St σ) (n : Nat) (t : Ty) (h : G.typeOf st.inner n = some t) :
    ∃ hits : List (List V), maybeUnary G st VIdx.«Opcode».«Uextend» (.value n) =
      .ok (if hits.isEmpty then [[.ty (CTy.ofClif t), .value n]] else hits) ∧
      ∀ fs, fs ∈ hits ↔ ∃ t' y, Inst.extend .uextend t' y ∈ G.enodes st.inner n ∧
        fs = [.ty (CTy.ofClif t), .value y] :=
  ⟨_, maybeUnary_uext_eq G st n t h, mem_uextHits G st n t⟩

/-- The `uextend_maybe` multi-extractor on an e-class: the operand of each `uextend` node, or
the class itself when it has none. -/
@[opt_match] theorem extractMulti_uem (n : Nat) (s : St σ) (Q : List V → Prop) :
    (∃ fss, (sem G).extractMulti T.«uextend_maybe_etor» (.value n) s = .ok fss ∧
      ∃ fs ∈ fss, Q fs) ↔
    ∃ t, G.typeOf s.inner n = some t ∧
      ((∃ t' y, Inst.extend .uextend t' y ∈ G.enodes s.inner n ∧
          Q [.ty (CTy.ofClif t), .value y]) ∨
        ((∀ t' y, Inst.extend .uextend t' y ∉ G.enodes s.inner n) ∧
          Q [.ty (CTy.ofClif t), .value n])) := by
  rw [sem_extractMulti]
  simp only [Term.externExtractor?, T.«uextend_maybe_etor», extractMultiFn]
  cases h : G.typeOf s.inner n with
  | none =>
    simp [maybeUnary, nodesOf, valueType, h, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  | some t =>
    obtain ⟨hits, he, hm⟩ := maybeUnary_uext G s n t h
    rw [he]
    simp only [ExtResult.ok.injEq, exists_eq_left', Option.some.injEq, exists_eq_left']
    by_cases hE : hits.isEmpty
    · have hnil : hits = [] := List.isEmpty_iff.1 hE
      subst hnil
      simp only [hE, ite_true, List.mem_singleton, exists_eq_left]
      have hno : ∀ t' y, Inst.extend .uextend t' y ∉ G.enodes s.inner n := by
        intro t' y hi
        exact absurd ((hm _).2 ⟨t', y, hi, rfl⟩) (by simp)
      constructor
      · intro hq; exact Or.inr ⟨hno, hq⟩
      · rintro (⟨t', y, hi, _⟩ | ⟨_, hq⟩)
        · exact absurd hi (hno t' y)
        · exact hq
    · simp only [hE, Bool.false_eq_true, ite_false]
      constructor
      · rintro ⟨fs, hfs, hq⟩
        obtain ⟨t', y, hi, rfl⟩ := (hm fs).1 hfs
        exact Or.inl ⟨t', y, hi, hq⟩
      · rintro (⟨t', y, hi, hq⟩ | ⟨hno, _⟩)
        · exact ⟨_, (hm _).2 ⟨t', y, hi, rfl⟩, hq⟩
        · exfalso
          apply hE
          cases hh : hits with
          | nil => rfl
          | cons fs _ =>
            obtain ⟨t', y, hi, _⟩ := (hm fs).1 (by simp [hh])
            exact absurd hi (hno t' y)

end

theorem toInt_nonneg_iff' {w : Nat} (x : BitVec w) : (0 ≤ x.toInt) ↔ x.msb = false := by
  have := BitVec.toInt_lt (x := x)
  have := BitVec.le_toInt (x := x)
  rw [BitVec.toInt_eq_msb_cond]
  have hx := x.isLt
  cases h : x.msb
  · simp
  · simp only [ite_true, Bool.true_eq_false, iff_false, Int.not_le]
    have : 2 ^ w = ((2 ^ w : Nat) : Int) := by simp
    omega

theorem toInt_neg_iff' {w : Nat} (x : BitVec w) : (x.toInt < 0) ↔ x.msb = true := by
  have := toInt_nonneg_iff' x
  constructor
  · intro h; cases hm : x.msb
    · exact absurd (this.2 hm) (by omega)
    · rfl
  · intro h; have : ¬ 0 ≤ x.toInt := by rw [toInt_nonneg_iff']; simp [h]
    omega

/-- The immediate `1` of `iconst_s ty 1`. -/
theorem toInt_eq_one {t : Ty} (x : BitVec t.width) : x.toInt = 1 ↔ x = 1#t.width := by
  have h : (1#t.width).toInt = 1 := by cases t <;> rfl
  rw [← BitVec.toInt_inj, h]

/-- The signed-immediate facts as `BitVec` facts. -/
macro "sint_simp" : tactic => `(tactic| (try simp only [BitVec.toInt_inj, ge_iff_le, gt_iff_lt,
  toInt_nonneg_iff', toInt_neg_iff', toInt_eq_one, decide_eq_true_eq, beq_true, beq_iff_eq] at *))

/-- `rule_bits_c` with `sint_simp` before `bv_decide`. -/
macro "rule_bits_e" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits, bne_iff_ne, ne_eq, toNat_eq_zero_iff] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | rfl
    | (first | apply some_val_congr | apply val_congr | skip
       first
         | (simp only [Clif.Sem.binary, Clif.Sem.unary, Clif.Sem.iadd, Clif.Sem.imul, Clif.Sem.band,
              Clif.Sem.bor, Clif.Sem.bxor]
            ac_rfl)
         | (sint_simp
            opt_cases_val <;> opt_cases_ty <;> opt_widths <;> sem_simp_b <;>
            (try simp only [Int.reducePow, Int.reduceSub, Int.reduceToNat, Nat.reducePow,
              Nat.reduceSub] at *) <;> sint_simp <;> first | ac_rfl | bv_decide))))

set_option hygiene false in
macro "rule_finish_e" : tactic => `(tactic| first
  | (try dsimp only
     apply Valuation.le_trans hle1 hle3
     opt_rw_lhs
     rule_bits_e)
  | (try dsimp only
     apply GraphOk.make_val hG (by opt_P)
     opt_node
     all_goals rule_bits_e))

syntax "rule_auto_e " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_e $r:ident) => `(tactic| rule_auto_e $r [])
  | `(tactic| rule_auto_e $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_c hG
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_e)))

syntax "rule_auto_ei " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_ei $r:ident) => `(tactic| rule_auto_ei $r [])
  | `(tactic| rule_auto_ei $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs_c hG
      all_goals rule_iflets_c [$ts,*]
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_e)))

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- Two facts `h1 : e = some a`, `h2 : e = some b` about the same class value (`den s x`): rewrite
`h2` to `some a = some b` and peel `some` (the merge `simp_all` would do). Fails if there is none. -/
elab "opt_den_merge" : tactic => withMainContext do
  let mut hs : Array (FVarId × Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, r) := t.eq? then
      if r.isAppOfArity ``Option.some 2 && l.isApp && !l.hasLooseBVars && !r.appArg!.isFVar then
        hs := hs.push (d.fvarId, l, r)
  for i in [0:hs.size] do
    for j in [i+1:hs.size] do
      let (f1, l1, _) := hs[i]!
      let (f2, l2, _) := hs[j]!
      if l1 == l2 then
        let h1 ← Term.exprToSyntax (mkFVar f1)
        let h2n := (← f2.getDecl).userName
        let h2 := mkIdent h2n
        try
          evalTactic (← `(tactic| (rw [$h1:term] at $h2:ident; simp only [Option.some.injEq] at $h2:ident)))
          return
        catch _ => pure ()
  throwError "opt_den_merge: nothing to merge"

end Opt.Proof

namespace Opt.Proof

set_option hygiene false in
/-- `rule_lhs_c` without `simp_all` (`lhs_step'` only): `simp_all` can rewrite a literal-match
fact (`asU64 imm = 0`, `i64_sextend_imm64 t imm = -1`) away with a copy of itself. -/
macro "rule_lhs_f " hG:ident : tactic => `(tactic|
  repeat (any_goals (first | (lhs_step'; opt_destruct; all_goals subst_vars) | opt_model $hG |
    (arr_step; opt_destruct; all_goals subst_vars))))

set_option hygiene false in
/-- `rule_lhs_f` that also opens the model facts guarded by `P s0` and merges two values of one
class (`opt_den_merge`). -/
macro "rule_lhs_g " hG:ident : tactic => `(tactic|
  repeat (any_goals (first | (lhs_step'; opt_destruct; all_goals subst_vars) | opt_model $hG |
    (arr_step; opt_destruct; all_goals subst_vars) |
    (simp (disch := assumption) only [forall_prop_of_true] at *; opt_destruct; all_goals subst_vars) |
    (opt_den_merge; opt_destruct; all_goals subst_vars))))

syntax "rule_auto_g " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_g $r:ident) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_g hG
      all_goals (rule_rhs_c []; opt_some_subst; rule_finish_e)))

syntax "rule_auto_f " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_f $r:ident) => `(tactic| rule_auto_f $r [])
  | `(tactic| rule_auto_f $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_f hG
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_e)))

syntax "rule_auto_fi " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_fi $r:ident) => `(tactic| rule_auto_fi $r [])
  | `(tactic| rule_auto_fi $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs_f hG
      all_goals rule_iflets_c [$ts,*]
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_e)))

/-- `rule_auto_f` / `rule_auto_fi` with every type split on `i128` before the right-hand side. -/
syntax "rule_auto_fz " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_fz $r:ident) => `(tactic| rule_auto_fz $r [])
  | `(tactic| rule_auto_fz $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_f hG
      all_goals opt_split_i128
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_e)))

syntax "rule_auto_fiz " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_fiz $r:ident) => `(tactic| rule_auto_fiz $r [])
  | `(tactic| rule_auto_fiz $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs_f hG
      all_goals rule_iflets_c [$ts,*]
      all_goals opt_split_i128
      all_goals (rule_rhs_c [$ts,*]; opt_some_subst; rule_finish_e)))

/-- `rule_auto_g` with every type split on `i128` before the right-hand side. -/
syntax "rule_auto_gz " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_gz $r:ident) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs_g hG
      all_goals opt_split_i128
      all_goals (rule_rhs_c []; opt_some_subst; rule_finish_e)))

end Opt.Proof

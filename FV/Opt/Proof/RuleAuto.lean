import FV.Opt.Proof.RuleImm

/-!
# The batching template: `rule_ok`

A `simplify` rule obligation (`RuleOk p r`) is proven in four mechanical phases:

1. `rule_intro r`: introduce the obligation, fix the fuel as `k + 1000`, unfold the rule's data.
2. `rule_lhs hG`: turn the left-hand side relation into e-graph facts — alternate `simp_all`
   over the embedding lemmas (`opt_match`, `opt_data`), `opt_destruct` and `subst`, and
   `opt_model hG` (the model's value/type facts for every matched node/class), to a fixpoint.
   Each matched node's value is then an explicit hypothesis `den s0.inner x = some ⟨t, b⟩`.
3. `opt_eval hil` / `opt_eval hev [helpers]`: evaluate the if-lets and the right-hand side.
4. `rule_finish`: the candidate is a matched class (`Valuation.Le` chain) or a made node
   (`GraphOk.make_val`), reducing the goal to an equation between bit vectors, closed per
   type by `simp` or `bv_decide` (`rule_bits`).
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

theorem toNat_eq_iff_ofNat {w : Nat} (b : BitVec w) (k : Nat) :
    b.toNat = k ↔ k < 2 ^ w ∧ b = BitVec.ofNat w k := by
  constructor
  · rintro rfl; exact ⟨b.isLt, by simp⟩
  · rintro ⟨hk, rfl⟩; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem val_some_eq {t : Ty} {b c : BitVec t.width} :
    (some (⟨t, b⟩ : Val) = some ⟨t, c⟩) ↔ b = c := by
  simp

/-- `Val` equations at one type (`Val.mk.injEq` would introduce a `HEq`; equations at two
types are split by `opt_destruct`). -/
theorem val_mk_same {t : Ty} {b c : BitVec t.width} : ((⟨t, b⟩ : Val) = ⟨t, c⟩) ↔ b = c := by
  simp

/-- One `simp_all` pass of the left-hand-side unfolding. -/
macro "lhs_step" : tactic => `(tactic| simp_all only [opt_match, opt_data, Except.ok.injEq,
  exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right', List.length_cons,
  List.length_nil, Nat.reduceAdd, ite_true, ite_false, Bool.false_eq_true, TermFlags.isMulti,
  reduceIte, V.data.injEq, V.ty.injEq, V.int.injEq, V.value.injEq, V.values.injEq,
  List.cons.injEq, reduceCtorEq, false_and, and_false, exists_false, or_false, false_or,
  true_and, and_true, Array.size_replicate, Array.set!_eq_setIfInBounds, Nat.lt_irrefl,
  Nat.reduceLT, Nat.zero_lt_succ, Nat.lt_add_one, Term.externExtractor?,
  Array.size_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_replicate, beq_iff_eq,
  Option.some.injEq, evalNode_unary, evalNode_binary_iff, evalNode_icmp, evalNode_iconst,
  BinaryOp.isShift, CTy.ofClif_inj, val_mk_same, forall_eq', forall_eq, unaryIdx_eq_iff,
  binaryIdx_eq_iff, unaryOfIdx?, binaryOfIdx?, true_implies, forall_const, heq_eq_eq, and_imp,
  forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, Nat.reduceEqDiff])

/-- Phase 2: the left-hand side to a fixpoint. -/
macro "rule_lhs " hG:ident : tactic => `(tactic|
  repeat (any_goals (first | (lhs_step; opt_destruct; all_goals subst_vars) | opt_model $hG)))

set_option hygiene false in
/-- Phase 1. -/
macro "rule_intro " r:ident : tactic => `(tactic| (
  intro σ G P den fr mem hG s0 v a hP hv env1 hrel n hn s1 tr1 envs2 s2 tr2 hP1 hle1 hil env2
    henv2 s3 tr3 ws s4 tr4 hP3 hle3 hev m hm
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1000 := ⟨n - 1000, by simp [fuelMin] at hn; omega⟩
  unfold $r:ident at hrel hil hev
  dsimp only at hrel hil hev))

set_option hygiene false in
/-- Phase 3 for rules without if-lets. -/
macro "rule_no_iflets" : tactic => `(tactic| (
  opt_eval hil
  simp only [Except.ok.injEq, Prod.mk.injEq] at hil
  obtain ⟨rfl, rfl, rfl⟩ := hil
  simp only [List.mem_singleton] at henv2
  subst henv2))

/-- Phase 3: the right-hand side, then the candidate. -/
syntax "rule_rhs" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_rhs) => `(tactic| rule_rhs [])
  | `(tactic| rule_rhs [$ts,*]) => `(tactic| (
      opt_eval hev [$ts,*]
      simp only [Except.ok.injEq, Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      simp only [List.mem_singleton, V.value.injEq] at hm
      subst hm))

/-- Semantics of the CLIF operations, unfolded for the bit-level goal. -/
macro "sem_simp" : tactic => `(tactic| simp only [val_some_eq, val_mk_same, Sem.binary, Sem.unary, Sem.iadd,
  Sem.isub, Sem.imul, Sem.band, Sem.bor, Sem.bxor, Sem.bnot, Sem.ineg, Sem.icmp, Sem.intcc,
  Sem.umin, Sem.umax, Sem.smin, Sem.smax, Sem.ishl, Sem.ushr, Sem.sshr, Sem.shift,
  Sem.shiftAmt, Sem.select, Sem.truthy, Sem.bitselect, Sem.bmask, Sem.bool8, Ty.width] at *)

/-- The bit-level goal: normalise immediates, split the type, decide. Only the goal and the
bit-vector facts matter; the context is not `simp_all`ed (it holds the whole e-graph model). -/
macro "rule_bits" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | rfl
    | (try simp only [val_some_eq, val_mk_same]
       opt_cases_ty <;> opt_widths <;> (try sem_simp) <;> bv_decide)))

set_option hygiene false in
/-- Phase 4 when the candidate is a class matched by the left-hand side. -/
macro "rule_finish_var" : tactic => `(tactic| (
  apply Valuation.le_trans hle1 hle3
  opt_rw_lhs
  rule_bits))


set_option hygiene false in
/-- `P` of a state reached by `make`s from `s3`. -/
macro "opt_P" : tactic => `(tactic| repeat (first | assumption | apply GraphOk.make_P hG))

/-- Prove `den X x = some c` (`c` possibly to be determined): an old class through the
`Valuation.Le` chain and the `make`s, or a made node by `GraphOk.make_val`. -/
syntax "opt_den" : tactic
/-- Prove `evalNode {fr with regs := den X} mem n = some c` operand by operand. -/
syntax "opt_node" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| opt_den) => `(tactic| first
      | (apply Valuation.le_trans hle1 hle3; assumption)
      | (apply GraphOk.make_val hG (by opt_P); opt_node)
      | (apply GraphOk.make_le hG (by opt_P); opt_den))

set_option hygiene false in
macro_rules
  | `(tactic| opt_node) => `(tactic| (
      simp only [evalNode_binary_iff, evalNode_unary, evalNode_icmp, evalNode_iconst,
        Clif.BinaryOp.isShift, Bool.false_eq_true, ite_false, ite_true, Clif.Frame.regs]
      repeat (first | (apply Exists.intro) | (apply And.intro) | opt_den)
      all_goals (try rfl)))

set_option hygiene false in
/-- Phase 4 when the candidate is a made node. -/
macro "rule_finish_make" : tactic => `(tactic| (
  try dsimp only
  apply GraphOk.make_val hG (by opt_P)
  opt_node
  all_goals rule_bits))

/-- Phase 4. -/
macro "rule_finish" : tactic => `(tactic| first | rule_finish_var | rule_finish_make)

/-- The whole template for a rule without if-lets. -/
syntax "rule_auto " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto $r:ident) => `(tactic| rule_auto $r [])
  | `(tactic| rule_auto $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs hG
      all_goals (rule_rhs [$ts,*]; rule_finish)))

end Opt.Proof

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
open Lean Elab Tactic

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
  binaryIdx_eq_iff, ccIdx_eq_iff, unaryOfIdx?, binaryOfIdx?, ccOfIdx?, evalNode_select,
  evalNode_bitselect, evalNode_bmask, evalNode_uextend, evalNode_sextend, evalNode_ireduce, true_implies, forall_const, heq_eq_eq, and_imp,
  forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, Nat.reduceEqDiff, eq_iff_iff, iff_false,
  iff_true, true_iff, false_iff, not_true_eq_false, not_false_eq_true])

/-- `lhs_step` without the hypotheses as rewrite rules (a fallback: `simp_all` can loop on the
contradictory hypotheses of a dead branch). -/
macro "lhs_step'" : tactic => `(tactic| simp (disch := assumption) only [opt_match, opt_data, Except.ok.injEq,
  exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right', List.length_cons,
  List.length_nil, Nat.reduceAdd, ite_true, ite_false, Bool.false_eq_true, TermFlags.isMulti,
  reduceIte, V.data.injEq, V.ty.injEq, V.int.injEq, V.value.injEq, V.values.injEq,
  List.cons.injEq, reduceCtorEq, false_and, and_false, exists_false, or_false, false_or,
  true_and, and_true, Array.size_replicate, Array.set!_eq_setIfInBounds, Nat.lt_irrefl,
  Nat.reduceLT, Nat.zero_lt_succ, Nat.lt_add_one, Term.externExtractor?,
  Array.size_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_replicate, beq_iff_eq,
  Option.some.injEq, evalNode_unary, evalNode_binary_iff, evalNode_icmp, evalNode_iconst,
  BinaryOp.isShift, CTy.ofClif_inj, val_mk_same, forall_eq', forall_eq, unaryIdx_eq_iff,
  binaryIdx_eq_iff, ccIdx_eq_iff, unaryOfIdx?, binaryOfIdx?, ccOfIdx?, evalNode_select,
  evalNode_bitselect, evalNode_bmask, evalNode_uextend, evalNode_sextend, evalNode_ireduce, true_implies, forall_const, heq_eq_eq, and_imp,
  forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, Nat.reduceEqDiff, eq_iff_iff, iff_false,
  iff_true, true_iff, false_iff, not_true_eq_false, not_false_eq_true] at *)

/-- Phase 2: the left-hand side to a fixpoint. -/
macro "rule_lhs " hG:ident : tactic => `(tactic|
  repeat (any_goals (first | (opt_guard lhs_step; opt_destruct; all_goals subst_vars) | opt_model $hG |
    (lhs_step'; opt_destruct; all_goals subst_vars))))

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

/-- See the `elab_rules` below. -/
syntax "opt_types" : tactic

/-- Phase 3: the right-hand side, then the candidate. -/
syntax "rule_rhs" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_rhs) => `(tactic| rule_rhs [])
  | `(tactic| rule_rhs [$ts,*]) => `(tactic| (
      opt_eval hev [$ts,*]
      repeat' (split at hev <;> try opt_norm hev)
      all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
      opt_destruct
      all_goals subst_vars
      all_goals (
        simp only [Except.ok.injEq, Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl, rfl⟩ := hev
        simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, V.value.injEq,
          reduceCtorEq] at hm <;>
        subst hm)
      all_goals opt_types))

/-- `if` on a `Bool` as `bif` (`bv_decide` reads `cond`, not `ite` on `b = true`). -/
theorem ite_eq_true_bif {α : Type} (b : Bool) (x y : α) :
    (if b = true then x else y) = bif b then x else y := by cases b <;> rfl

/-- The `Bool`-valued CLIF operations as `bif`, rewritten before their condition is unfolded
(the `Decidable` instance of an `if` would go stale under `simp`). -/
theorem bool8_bif (b : Bool) : Sem.bool8 b = bif b then 1#8 else 0#8 := by cases b <;> rfl
theorem select_bif {v w : Nat} (c : BitVec v) (x y : BitVec w) :
    Sem.select c x y = bif !(c == 0#v) then x else y := by
  unfold Sem.select Sem.truthy; cases h : (c == 0#v) <;> simp [bne, h]
/-- `Sem.intcc` per condition code (`!=` as `!(· == ·)`: `bv_decide` does not read `bne`). -/
theorem intcc_eq' {w : Nat} (x y : BitVec w) : Sem.intcc .eq x y = (x == y) := rfl
theorem intcc_ne' {w : Nat} (x y : BitVec w) : Sem.intcc .ne x y = (!(x == y)) := rfl
theorem intcc_slt' {w : Nat} (x y : BitVec w) : Sem.intcc .slt x y = (x.slt y) := rfl
theorem intcc_sge' {w : Nat} (x y : BitVec w) : Sem.intcc .sge x y = (y.sle x) := rfl
theorem intcc_sgt' {w : Nat} (x y : BitVec w) : Sem.intcc .sgt x y = (y.slt x) := rfl
theorem intcc_sle' {w : Nat} (x y : BitVec w) : Sem.intcc .sle x y = (x.sle y) := rfl
theorem intcc_ult' {w : Nat} (x y : BitVec w) : Sem.intcc .ult x y = (x.ult y) := rfl
theorem intcc_uge' {w : Nat} (x y : BitVec w) : Sem.intcc .uge x y = (y.ule x) := rfl
theorem intcc_ugt' {w : Nat} (x y : BitVec w) : Sem.intcc .ugt x y = (y.ult x) := rfl
theorem intcc_ule' {w : Nat} (x y : BitVec w) : Sem.intcc .ule x y = (x.ule y) := rfl
theorem smin_bif {w : Nat} (x y : BitVec w) : Sem.smin x y = bif x.sle y then x else y := by
  unfold Sem.smin; cases (x.sle y) <;> rfl
theorem smax_bif {w : Nat} (x y : BitVec w) : Sem.smax x y = bif y.sle x then x else y := by
  unfold Sem.smax; cases (y.sle x) <;> rfl
theorem umin_bif {w : Nat} (x y : BitVec w) : Sem.umin x y = bif x.ule y then x else y := by
  unfold Sem.umin; cases (x.ule y) <;> rfl
theorem umax_bif {w : Nat} (x y : BitVec w) : Sem.umax x y = bif y.ule x then x else y := by
  unfold Sem.umax; cases (y.ule x) <;> rfl
theorem bmask_bif {v w : Nat} (x : BitVec v) :
    (Sem.bmask x : BitVec w) = bif !(x == 0#v) then BitVec.allOnes w else 0#w := by
  unfold Sem.bmask Sem.truthy; cases h : (x == 0#v) <;> simp [bne, h]

/-- The goal `⟨t, b⟩ = ⟨t, c⟩` (up to `some`) as `b = c`, by unification (a `simp` lemma would not
see `BitVec 8` and `BitVec Ty.i8.width` as the same type). -/
theorem val_congr {t : Ty} {b c : BitVec t.width} (h : b = c) : (⟨t, b⟩ : Val) = ⟨t, c⟩ := h ▸ rfl
theorem some_val_congr {t : Ty} {b c : BitVec t.width} (h : b = c) :
    some (⟨t, b⟩ : Val) = some ⟨t, c⟩ := h ▸ rfl

/-- Semantics of the CLIF operations, unfolded for the bit-level goal. -/
macro "sem_simp" : tactic => `(tactic| simp (disch := decide) only [ishl_mask, ushr_mask, sshr_mask,
  rotl_mask, rotr_mask, val_some_eq, val_mk_same, Sem.binary, Sem.unary, Sem.iadd,
  Sem.isub, Sem.imul, Sem.band, Sem.bor, Sem.bxor, Sem.bnot, Sem.ineg, Sem.icmp,
  umin_bif, umax_bif, smin_bif, smax_bif, Sem.shift,
  select_bif, Sem.truthy, Sem.bitselect, bmask_bif, bool8_bif, Sem.uextend,
  ite_eq_true_bif, intcc_eq', intcc_ne', intcc_slt', intcc_sge', intcc_sgt', intcc_sle', intcc_ult', intcc_uge', intcc_ugt', intcc_ule',
  Sem.sextend, Sem.ireduce, Sem.clz, Sem.ctz, Rust.intccSwapArgs, Rust.intccComplement, Ty.width] at *)

/-- The bit-level goal: normalise immediates, split the type, decide. Only the goal and the
bit-vector facts matter; the context is not `simp_all`ed (it holds the whole e-graph model).
`bv_decide` gets a 120 s SAT timeout instead of the default 10 s: these goals take a few seconds
alone, but the default made full builds fail intermittently under load. -/
macro "rule_bits" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits, bne_iff_ne, ne_eq, toNat_eq_zero_iff] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | rfl
    | (first | apply some_val_congr | apply val_congr | skip
       first
         | (simp only [Sem.binary, Sem.unary, Sem.iadd, Sem.imul, Sem.band, Sem.bor, Sem.bxor]
            ac_rfl)
         | (opt_cases_ty <;> opt_widths <;> (try sem_simp) <;>
             first | ac_rfl | bv_decide (config := { timeout := 120 })))))

set_option hygiene false in
/-- Phase 4 when the candidate is a class matched by the left-hand side. -/
macro "rule_finish_var" : tactic => `(tactic| (
  try dsimp only
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
        evalNode_select, evalNode_bitselect, evalNode_bmask, evalNode_uextend, evalNode_sextend,
        evalNode_ireduce,
        Clif.BinaryOp.isShift, Bool.false_eq_true, ite_false, ite_true, Clif.Frame.regs]
      repeat (first | (apply Exists.intro) | (apply And.intro) | opt_den)
      all_goals (try rfl)))

set_option hygiene false in
/-- `opt_types`: for every hypothesis `G.typeOf st x = some xt` with `xt` a variable (the type
of an operand class read in a later state, when `toInst` builds an `icmp`), prove `xt` is the
type of the class's value (`GraphOk.typeOf_eq`, the value through `opt_den`) and substitute. -/
elab_rules : tactic
  | `(tactic| opt_types) => do
  let g ← getMainGoal
  let hyps ← g.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if let some (_, l, r) := t.eq? then
        if l.isAppOfArity `Isle.Opt.EGraph.typeOf 4 && r.isAppOfArity ``Option.some 2 &&
            r.appArg!.isFVar then
          out := out.push d.fvarId
    pure out
  for h in hyps do
    let g ← getMainGoal
    let ok ← g.withContext do
      let hs ← Term.exprToSyntax (mkFVar h)
      try
        evalTactic (← `(tactic| (
          have hty := GraphOk.typeOf_eq hG (by opt_P) $hs (by opt_den)
          simp only at hty
          subst hty)))
        pure true
      catch _ => pure false
    unless ok do pure ()

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

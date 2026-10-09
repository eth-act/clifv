import FV.Opt.Proof.RuleSkelEmbed

/-!
# Branch conditions made from leading/trailing zero counts

The four `icmp.isle` skeleton rules replace a count's truthiness by a test of
its input.  The optional `ireduce` preserves this truthiness: every supported
integer type has at least eight bits, and a count is at most 128.

During interpreter evaluation, name each made graph node before evaluating
the next constructor.  In particular the i128 constant constructors make an
i64 constant followed by `uextend`; repeatedly substituting the resulting
state into both projections of the next `make` otherwise duplicates the
entire evaluation prefix.  Local definitions retain the ordinary `opt_den`
proof and do not add any assumptions about the graph.
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

open Lean Meta Elab Tactic in
/-- Share one graph-constructor result by a definition, not a new premise. -/
elab "skel_count_share_one " h:ident : tactic => withMainContext do
  let hyp ← getFVarId h
  let ty ← instantiateMVars (← hyp.getType)
  let some e := ty.find? (fun e =>
      e.isAppOfArity ``Isle.Opt.EGraph.make 4 && !e.hasLooseBVars)
    | throwError "no graph constructor to share"
  let name ← mkFreshUserName `made
  let g ← (← getMainGoal).define name (← inferType e) e
  let (made, g) ← g.intro1P
  let ty' := ty.replace fun x => if x == e then some made.toExpr else none
  replaceMainGoal [← g.changeLocalDecl hyp ty']

macro "skel_count_share " h:ident : tactic =>
  `(tactic| repeat skel_count_share_one $h)

macro "skel_count_norm " h:ident : tactic => `(tactic| (
  opt_norm $h
  skel_count_share $h))

macro "skel_count_eval " h:ident : tactic => `(tactic| (
  skel_count_norm $h
  repeat (opt_unfold $h; skel_count_norm $h)))

set_option hygiene false in
/-- The ordinary skeleton RHS phase, sharing each made node between steps. -/
macro "skel_count_rhs" : tactic => `(tactic| (
  skel_count_eval hev
  repeat' (split at hev <;> try skel_count_norm hev)
  all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
  opt_destruct
  all_goals subst_vars
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw <;>
    subst hw)
  all_goals opt_types
  all_goals (try (exfalso; omega))))

set_option hygiene false in
macro "skel_count_rule " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals rule_no_iflets
  all_goals opt_split_i128
  all_goals (skel_count_rhs; skel_good; skel_br)))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_461 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_461 := by
  skel_count_rule rule_icmp_461

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_466 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_466 := by
  skel_count_rule rule_icmp_466

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_471 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_471 := by
  skel_count_rule rule_icmp_471

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem ok_rule_icmp_475 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_icmp_475 := by
  skel_count_rule rule_icmp_475

/-! Concrete nonzero and zero branch conditions, including the maximal count
128 after reduction to i8.  The integration smoke additionally exercises the
actual rule matches and rewritten branch targets. -/
example : (2#128).ctz ≠ 0 ∧ (2#128 &&& 1#128) = 0 := by decide
example : (1#128).ctz = 0 ∧ (1#128 &&& 1#128) ≠ 0 := by decide
example : (0#128).ctz.setWidth 8 = 128#8 ∧ (0#128 &&& 1#128) = 0 := by decide
example : (1#128).clz ≠ 0 ∧ (1#128).slt 0 = false := by decide
example : (BitVec.intMin 128).clz = 0 ∧ (BitVec.intMin 128).slt 0 = true := by decide
example : (0#128).clz.setWidth 8 = 128#8 ∧ (0#128).slt 0 = false := by decide

end Opt.Proof

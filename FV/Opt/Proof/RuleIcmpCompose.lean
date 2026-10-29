module

public import FV.Opt.Proof.RuleIcmpComposeGuard
public import FV.Opt.Proof.RuleIcmpComposeRhs
public import FV.Opt.Proof.RuleIcmpComposeWitness

@[expose] public section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

open Lean Meta Elab Tactic in
/-- Enumerate condition codes, but leave the operand type and width symbolic. -/
elab "icmp_compose_cases_cc" : tactic => do
  let rec go (g : MVarId) : Nat → MetaM (Array MVarId)
    | 0 => pure #[g]
    | fuel + 1 => g.withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if (← instantiateMVars d.type).isConstOf ``Clif.IntCC then
          let branches ← g.cases d.fvarId
          let mut result := #[]
          for branch in branches do
            for child in ← go branch.mvarId fuel do
              result := result.push child
          return result
      return #[g]
  replaceMainGoal (← go (← getMainGoal) 2).toList

open Lean Meta Elab Tactic in
/-- Separate equality from strict order so arithmetic sees numeric disequalities,
without global simplification rewriting unsigned comparisons back to `BitVec` order. -/
elab "icmp_compose_arith" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some cmp := target.find? (fun e => e.isAppOfArity ``Clif.Sem.icmp 4)
    | throwError "no comparison in the composition equation"
  let args := cmp.getAppArgs
  let x ← Term.exprToSyntax args[2]!
  let y ← Term.exprToSyntax args[3]!
  evalTactic (← `(tactic| (
    by_cases hxy : $x:term = $y:term
    · simp only [hxy]
      simp [Sem.binary, Sem.band, Sem.bor, Sem.icmp, Sem.intcc, Sem.bool8,
        BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule]
    · have hn : ($x:term).toNat ≠ ($y:term).toNat :=
        fun h => hxy (BitVec.toNat_inj.mp h)
      have hi : ($x:term).toInt ≠ ($y:term).toInt :=
        fun h => hxy (BitVec.toInt_inj.mp h)
      simp only [Sem.binary, Sem.band, Sem.bor, Sem.icmp, Sem.intcc, Sem.bool8,
        BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule]
      all_goals try simp only [bne_iff_ne, beq_iff_eq, Bool.not_eq_true',
        beq_eq_false_iff_ne, decide_eq_true_eq, decide_eq_false_iff_not,
        hxy, not_false_eq_true, ite_false, ite_true]
      all_goals repeat' (first | split | contradiction | (exfalso; omega) | decide))))

private theorem icmp_compose_bindAll_singleton {σ α β : Type} (f : α → Interp.M σ (List β)) (a : α) :
    Interp.bindAll f [a] = f a := by
  funext st
  change (Interp.bindAll f [a]).run st = (f a).run st
  rw [run_bindAll_cons]
  cases h : (f a).run st <;>
    simp only [run_bindAll_nil, except_ok_bind', except_error_bind', List.append_nil]

-- Keep the outer call opaque while evaluating its arguments. Otherwise the
-- general interpreter tactic expands all composition rules before the mask is known.
open Lean Meta Elab Tactic in
elab "icmp_compose_hide" : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? `hev | throwError "no hev"
  let ty ← instantiateMVars d.type
  let some call := ty.find? (fun e =>
    e.isAppOfArity ``Isle.Interp.applyTermN 9 && !e.appFn!.hasLooseBVars)
    | throwError "no composition function to hold opaque"
  let .lit (.natVal 251) ← whnf call.getAppArgs[7]!
    | throwError "unexpected outer composition term"
  let callSyntax ← Term.exprToSyntax call.appFn!
  evalTactic (← `(tactic| generalize $(mkIdent `hcompose):ident : $callSyntax:term =
    $(mkIdent `fcompose):ident at $(mkIdent `hev):ident))

set_option hygiene false in
macro "icmp_compose_prefix" : tactic => `(tactic| (
  opt_unfold hev
  icmp_compose_hide
  opt_eval hev [icmp_compose_bindAll_singleton, eval_icmp_decompose hd, icmpDecomposeValue, icmpDecomposeRule,
    Rust.band64, Rust.bor64, Rust.asU64, Rust.asI64, BitVec.reduceOfInt,
    BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceToNat, BitVec.reduceToInt,
    Int.reduceNatCast, Int.reduceNatCast', Int.reduceOfNat, Int.reduceBEq, Int.reduceBNe]
  rw [← hcompose] at hev
  clear hcompose fcompose))

set_option hygiene false in
macro "icmp_compose_apply " helper:ident : tactic => `(tactic| (
  have hresult := $helper hd hG hP3 hev
    (by apply hle3; apply hle1; assumption)
    (by apply hle3; apply hle1; assumption) hm
  rw [hresult]
  apply some_val_congr
  try simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals icmp_compose_arith))

open Lean Meta Elab Tactic in
elab "icmp_compose_rhs" : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? `hev | throwError "no RHS evaluation"
  let some call := (← instantiateMVars d.type).find? (fun e =>
      e.isAppOfArity ``Isle.Interp.applyTermN 9 && !e.hasLooseBVars)
    | throwError "no closed RHS composition call"
  let .lit (.natVal 251) ← whnf call.getAppArgs[7]!
    | throwError "unexpected RHS composition term"
  let args := call.getAppArgs[8]!
  let second := args.getAppArgs[2]!.getAppArgs[1]!
  unless second.isAppOfArity ``Isle.Opt.V.int 1 do throwError "non-integer composition mask"
  let maskExpr ← whnf second.appArg!
  unless maskExpr.isAppOfArity ``Int.ofNat 1 do throwError "negative composition mask"
  let .lit (.natVal mask) ← whnf maskExpr.appArg! | throwError "nonliteral composition mask"
  let helper ← match mask with
    | 0 => pure ``Opt.Proof.compose_rhs_false
    | 1 => pure ``Opt.Proof.compose_rhs_eq
    | 2 => pure ``Opt.Proof.compose_rhs_lt
    | 3 => pure ``Opt.Proof.compose_rhs_le
    | 4 => pure ``Opt.Proof.compose_rhs_gt
    | 5 => pure ``Opt.Proof.compose_rhs_ge
    | 6 => pure ``Opt.Proof.compose_rhs_ne
    | 7 => pure ``Opt.Proof.compose_rhs_true
    | _ => throwError "composition mask outside 0–7"
  evalTactic (← `(tactic| icmp_compose_apply $(mkIdent helper):ident))

set_option hygiene false in
macro "icmp_compose_rule " r:ident : tactic => `(tactic| (
  rule_intro $r:ident
  rule_lhs_g hG
  all_goals rule_iflets_c [eval_icmp_comparable hd, icmpComparable,
    Option.map_some, Option.map_none, Interp.matchAll.eq_1, Interp.matchAll.eq_2]
  all_goals icmp_compose_prefix
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals icmp_compose_cases_cc
  all_goals simp_all only [icmpClassValue, icmpDecomposeValue, Rust.band64, Rust.bor64,
    Rust.asU64, Rust.asI64, BitVec.reduceOfInt, BitVec.reduceAnd, BitVec.reduceOr,
    BitVec.reduceToNat, BitVec.reduceToInt, Int.reduceNatCast, Int.reduceNatCast',
    Int.reduceOfNat, Int.reduceBEq, Int.reduceBNe, Bool.false_beq, Bool.true_beq,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    not_false_eq_true, not_true_eq_false]
  all_goals icmp_compose_rhs))

-- The singleton law has a concrete successful run with a nonempty trace.
example :
    (Interp.bindAll (fun n : Nat => (pure [n, n + 1] : Interp.M Unit (List Nat))) [3]).run
      ((), #[7]) = .ok ([3, 4], ((), #[7])) := by
  rw [icmp_compose_bindAll_singleton]
  rfl

/-- `icmp.isle:180`: conjunction of comparable predicates. -/
theorem ok_rule_icmp_180 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_180 := by
  icmp_compose_rule rule_icmp_180

/-- `icmp.isle:184`: disjunction of comparable predicates. -/
theorem ok_rule_icmp_184 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_184 := by
  icmp_compose_rule rule_icmp_184

-- The roots have nonconstant, false-constant and true-constant inhabited cases.
example :
    Sem.band (Sem.icmp .sle (128#8) (127#8)) (Sem.icmp .ne (128#8) (127#8)) = 1#8 ∧
    Sem.band (Sem.icmp .sle (127#8) (128#8)) (Sem.icmp .ne (127#8) (128#8)) = 0#8 ∧
    Sem.band (Sem.icmp .sle (17#8) (17#8)) (Sem.icmp .ne (17#8) (17#8)) = 0#8 ∧
    Sem.band (Sem.icmp .eq (17#8) (17#8)) (Sem.icmp .ne (17#8) (17#8)) = 0#8 := by decide

example :
    Sem.bor (Sem.icmp .ult (0#8) (255#8)) (Sem.icmp .eq (0#8) (255#8)) = 1#8 ∧
    Sem.bor (Sem.icmp .ult (17#8) (17#8)) (Sem.icmp .eq (17#8) (17#8)) = 1#8 ∧
    Sem.bor (Sem.icmp .ult (255#8) (0#8)) (Sem.icmp .eq (255#8) (0#8)) = 0#8 ∧
    Sem.bor (Sem.icmp .eq (0#8) (255#8)) (Sem.icmp .ne (0#8) (255#8)) = 1#8 := by decide

example :
    Sem.band (Sem.icmp .eq (17#8) (17#8)) (Sem.icmp .sle (17#8) (17#8)) = 1#8 ∧
    Sem.band (Sem.icmp .ne (0#8) (255#8)) (Sem.icmp .ult (0#8) (255#8)) = 1#8 ∧
    Sem.band (Sem.icmp .ne (255#8) (0#8)) (Sem.icmp .sgt (255#8) (0#8)) = 0#8 ∧
    Sem.bor (Sem.icmp .eq (128#8) (127#8)) (Sem.icmp .slt (128#8) (127#8)) = 1#8 ∧
    Sem.bor (Sem.icmp .ne (17#8) (17#8)) (Sem.icmp .uge (17#8) (17#8)) = 1#8 ∧
    Sem.bor (Sem.icmp .eq (255#8) (0#8)) (Sem.icmp .ugt (255#8) (0#8)) = 1#8 := by decide

end Opt.Proof

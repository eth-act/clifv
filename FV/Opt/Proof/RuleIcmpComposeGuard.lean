module

public import FV.Opt.Proof.RuleIcmpComposeEval
public import FV.Opt.Proof.RuleRestEmbed

@[expose] public section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif

/-- The partial source helper rejects disjoint signed/unsigned classes. -/
def icmpComparable (cc1 cc2 : IntCC) : Option Bool :=
  let c := Rust.band64 (icmpClassValue cc1) (icmpClassValue cc2)
  if c == 0 then none else some (c == 2)

private theorem icmp_class_value_cases (cc : IntCC) :
    icmpClassValue cc = 1 ∨ icmpClassValue cc = 2 ∨ icmpClassValue cc = 3 := by
  cases cc <;> simp [icmpClassValue]

-- This finite range is inhabited by unsigned, signed and equality predicates.
example : icmpClassValue .ult = 1 ∧ icmpClassValue .slt = 2 ∧
    icmpClassValue .eq = 3 := by decide

-- Do not unfold ccIdx: the compiled class evaluator must see its original
-- condition-code argument. Only the two class values are specialized here.
set_option hygiene false in
local macro "compose_guard_pair" : tactic => `(tactic| (
  try simp (disch := assumption) only [opt_data, eval_icmp_class hd,
    hclass1, hclass2, Rust.band64, Rust.asU64, Rust.asI64,
    BitVec.reduceOfInt, BitVec.reduceAnd, BitVec.reduceOr,
    BitVec.reduceToNat, BitVec.reduceToInt, Int.reduceNatCast,
    Int.reduceNatCast', Int.reduceOfNat, Int.reduceBEq, Int.reduceBNe,
    Bool.false_beq, Bool.true_beq, Bool.not_true, Bool.not_false,
    panics_throw_bind, except_throw_bind, toExt_throw,
    Isle.Interp.bindAll, Isle.Interp.matchAllN.eq_1, Isle.Interp.matchAllN.eq_2,
    Isle.Interp.matchArgsN.eq_1, Isle.Interp.matchAll.eq_1,
    Isle.Interp.matchAll.eq_2] at hrun
  try simp (disch := assumption) only [opt_monad, opt_imm, eval_icmp_class hd,
    hclass1, hclass2, Rust.band64, Rust.asU64, Rust.asI64,
    BitVec.reduceOfInt, BitVec.reduceAnd, BitVec.reduceOr,
    BitVec.reduceToNat, BitVec.reduceToInt, Int.reduceNatCast,
    Int.reduceNatCast', Int.reduceOfNat, Int.reduceBEq, Int.reduceBNe,
    Bool.false_beq, Bool.true_beq, Bool.not_true, Bool.not_false,
    panics_throw_bind, except_throw_bind, toExt_throw,
    Isle.Interp.bindAll, Isle.Interp.matchAllN.eq_1, Isle.Interp.matchAllN.eq_2,
    Isle.Interp.matchArgsN.eq_1, Isle.Interp.matchAll.eq_1,
    Isle.Interp.matchAll.eq_2] at hrun))

set_option hygiene false in
local macro "compose_guard_step" : tactic => `(tactic| (
  first
  | compose_lookup_finish hrun
  | (opt_unfold hrun
     compose_guard_pair
     compose_guard_pair)))

open Lean Meta Elab Tactic in
elab "compose_guard_steps" : tactic => do
  for _ in [:256] do
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| compose_guard_step))

/-- Successful guards retain the two class-rule events and fire rule209;
failed guards restore the incoming trace as well as the graph state. -/
theorem eval_icmp_comparable {p : Isle.Program} (hd : Data p)
    {σ : Type} (G : Isle.Opt.EGraph σ) (n : Nat) (cc1 cc2 : IntCC)
    (s : St σ) (tr : Array RuleId) :
    (Interp.applyTerm p (sem G).toSem cfg (n + 32) 0 249
      [V.data 46 (ccIdx cc1) [], V.data 46 (ccIdx cc2) []]).run (s, tr) =
      .ok ((icmpComparable cc1 cc2).map V.bool,
        (s, match icmpComparable cc1 cc2 with
          | none => tr
          | some _ => ((tr.push (icmpClassRule cc1)).push (icmpClassRule cc2)).push rule_icmp_209.id)) := by
  rcases icmp_class_value_cases cc1 with hclass1 | hclass1 | hclass1
  all_goals rcases icmp_class_value_cases cc2 with hclass2 | hclass2 | hclass2
  all_goals
    simp only [icmpComparable, hclass1, hclass2, Rust.band64, Rust.asU64, Rust.asI64,
      BitVec.reduceOfInt, BitVec.reduceAnd, BitVec.reduceOr,
      BitVec.reduceToNat, BitVec.reduceToInt, Int.reduceNatCast,
      Int.reduceNatCast', Int.reduceOfNat, Int.reduceBEq, Int.reduceBNe,
      Bool.false_eq_true, reduceIte, Option.map_none, Option.map_some]
    generalize hrun : (Interp.applyTerm p (sem G).toSem cfg (n + 32) 0 249
      [V.data 46 (ccIdx cc1) [], V.data 46 (ccIdx cc2) []]).run (s, tr) = result
    compose_guard_pair
    compose_guard_pair
    compose_guard_steps
    all_goals exact hrun.symm

private def comparableWitnessGraph : Isle.Opt.EGraph Unit where
  enodes := fun _ _ => []
  typeOf := fun _ _ => none
  make := fun s _ => (0, s)

private def comparableWitnessState : St Unit := { inner := () }

-- Concrete compatible unsigned, signed and equality cases, followed by
-- incompatible orders. Every call starts with a nonempty trace and extra fuel.
example : (Interp.applyTerm program (sem comparableWitnessGraph).toSem cfg 64 0 249
    [V.data 46 (ccIdx .ult) [], V.data 46 (ccIdx .eq) []]).run (comparableWitnessState, #[42]) =
    .ok (some (V.bool false),
      (comparableWitnessState, #[42, rule_icmp_240.id, rule_icmp_248.id, rule_icmp_209.id])) := by
  exact eval_icmp_comparable data_program comparableWitnessGraph 32 .ult .eq comparableWitnessState #[42]

example : (Interp.applyTerm program (sem comparableWitnessGraph).toSem cfg 64 0 249
    [V.data 46 (ccIdx .ne) [], V.data 46 (ccIdx .slt) []]).run (comparableWitnessState, #[42]) =
    .ok (some (V.bool true),
      (comparableWitnessState, #[42, rule_icmp_249.id, rule_icmp_244.id, rule_icmp_209.id])) := by
  exact eval_icmp_comparable data_program comparableWitnessGraph 32 .ne .slt comparableWitnessState #[42]

example : (Interp.applyTerm program (sem comparableWitnessGraph).toSem cfg 64 0 249
    [V.data 46 (ccIdx .eq) [], V.data 46 (ccIdx .ne) []]).run (comparableWitnessState, #[42]) =
    .ok (some (V.bool false),
      (comparableWitnessState, #[42, rule_icmp_248.id, rule_icmp_249.id, rule_icmp_209.id])) := by
  exact eval_icmp_comparable data_program comparableWitnessGraph 32 .eq .ne comparableWitnessState #[42]

example : (Interp.applyTerm program (sem comparableWitnessGraph).toSem cfg 64 0 249
    [V.data 46 (ccIdx .ult) [], V.data 46 (ccIdx .slt) []]).run (comparableWitnessState, #[42]) =
    .ok (none, (comparableWitnessState, #[42])) := by
  exact eval_icmp_comparable data_program comparableWitnessGraph 32 .ult .slt comparableWitnessState #[42]

end Opt.Proof

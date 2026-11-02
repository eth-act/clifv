import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleInfraEval

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif

/-- `intcc_class`'s result and fired rule, in source rule order. -/
def icmpClassValue : IntCC → Int
  | .eq | .ne => 3
  | .slt | .sle | .sgt | .sge => 2
  | .ult | .ule | .ugt | .uge => 1

def icmpClassRule : IntCC → RuleId
  | .ult => rule_icmp_240.id | .ule => rule_icmp_241.id
  | .ugt => rule_icmp_242.id | .uge => rule_icmp_243.id
  | .slt => rule_icmp_244.id | .sle => rule_icmp_245.id
  | .sgt => rule_icmp_246.id | .sge => rule_icmp_247.id
  | .eq => rule_icmp_248.id | .ne => rule_icmp_249.id

/-- `decompose_intcc` uses one bit for each of equal, less and greater. -/
def icmpDecomposeValue : IntCC → Int
  | .eq => 1
  | .ult | .slt => 2
  | .ule | .sle => 3
  | .ugt | .sgt => 4
  | .uge | .sge => 5
  | .ne => 6

def icmpDecomposeRule : IntCC → RuleId
  | .eq => rule_icmp_214.id
  | .ult => rule_icmp_215.id | .slt => rule_icmp_216.id
  | .ule => rule_icmp_217.id | .sle => rule_icmp_218.id
  | .ugt => rule_icmp_219.id | .sgt => rule_icmp_220.id
  | .uge => rule_icmp_221.id | .sge => rule_icmp_222.id
  | .ne => rule_icmp_223.id

-- Keep evaluation local and bounded: one `simp` call per step that normalises only the head
-- computation of each `bind` (`opt_bind_head`, `RuleInfraEval.lean`) and exposes ccIdx's named
-- aliases before comparing tags. Two calls per step over the whole hypothesis, each run twice,
-- re-traversed every pending continuation (24 s per leaf on an orb, 96% of the module).
set_option hygiene false in
local macro "compose_lookup_norm" : tactic => `(tactic| (
  try simp (disch := assumption) only [↓opt_bind_head, opt_data, opt_monad, opt_imm, ccIdx,
    Nat.reduceBEq,
    VIdx.IntCC.Equal, VIdx.IntCC.NotEqual, VIdx.IntCC.SignedGreaterThan,
    VIdx.IntCC.SignedGreaterThanOrEqual, VIdx.IntCC.SignedLessThan,
    VIdx.IntCC.SignedLessThanOrEqual, VIdx.IntCC.UnsignedGreaterThan,
    VIdx.IntCC.UnsignedGreaterThanOrEqual, VIdx.IntCC.UnsignedLessThan,
    VIdx.IntCC.UnsignedLessThanOrEqual,
    Isle.Interp.matchAll.eq_1, Isle.Interp.matchAll.eq_2] at hrun))

open Lean Meta Elab Tactic in
elab "compose_lookup_finish " h:ident : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? h.getId
    | throwError "missing lookup evaluation"
  let some (_, lhs, _) := (← instantiateMVars d.type).eq?
    | throwError "lookup evaluation is not an equation"
  unless lhs.isAppOfArity ``Except.ok 3 do
    throwError "lookup evaluation has not returned"
  evalTactic (← `(tactic| exact ($h:ident).symm))

set_option hygiene false in
local macro "compose_lookup_step" : tactic => `(tactic| (
  first
  | compose_lookup_finish hrun
  | (opt_unfold_head hrun
     compose_lookup_norm)))

open Lean Meta Elab Tactic in
elab "compose_lookup_steps" : tactic => do
  for _ in [:256] do
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| compose_lookup_step))

set_option hygiene false in
local macro "compose_lookup " termId:num cc:term : tactic => `(tactic| (
  generalize hrun : (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 $termId
    [V.data 46 (ccIdx $cc:term) []]).run (s, tr) = result
  compose_lookup_norm
  compose_lookup_steps
  all_goals exact hrun.symm))

section Leaves
variable {p : Isle.Program} (hd : Data p)
  {σ : Type} (G : Isle.Opt.EGraph σ) (n : Nat) (s : St σ) (tr : Array RuleId)
include hd

private theorem eval_class_eq :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .eq) []]).run (s, tr) =
      .ok (some (V.int 3), (s, tr.push rule_icmp_248.id)) := by
  compose_lookup 252 .eq

private theorem eval_class_ne :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .ne) []]).run (s, tr) =
      .ok (some (V.int 3), (s, tr.push rule_icmp_249.id)) := by
  compose_lookup 252 .ne

private theorem eval_class_slt :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .slt) []]).run (s, tr) =
      .ok (some (V.int 2), (s, tr.push rule_icmp_244.id)) := by
  compose_lookup 252 .slt

private theorem eval_class_sle :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .sle) []]).run (s, tr) =
      .ok (some (V.int 2), (s, tr.push rule_icmp_245.id)) := by
  compose_lookup 252 .sle

private theorem eval_class_sgt :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .sgt) []]).run (s, tr) =
      .ok (some (V.int 2), (s, tr.push rule_icmp_246.id)) := by
  compose_lookup 252 .sgt

private theorem eval_class_sge :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .sge) []]).run (s, tr) =
      .ok (some (V.int 2), (s, tr.push rule_icmp_247.id)) := by
  compose_lookup 252 .sge

private theorem eval_class_ult :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .ult) []]).run (s, tr) =
      .ok (some (V.int 1), (s, tr.push rule_icmp_240.id)) := by
  compose_lookup 252 .ult

private theorem eval_class_ule :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .ule) []]).run (s, tr) =
      .ok (some (V.int 1), (s, tr.push rule_icmp_241.id)) := by
  compose_lookup 252 .ule

private theorem eval_class_ugt :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .ugt) []]).run (s, tr) =
      .ok (some (V.int 1), (s, tr.push rule_icmp_242.id)) := by
  compose_lookup 252 .ugt

private theorem eval_class_uge :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx .uge) []]).run (s, tr) =
      .ok (some (V.int 1), (s, tr.push rule_icmp_243.id)) := by
  compose_lookup 252 .uge

private theorem eval_decompose_eq :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .eq) []]).run (s, tr) =
      .ok (some (V.int 1), (s, tr.push rule_icmp_214.id)) := by
  compose_lookup 250 .eq

private theorem eval_decompose_ne :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .ne) []]).run (s, tr) =
      .ok (some (V.int 6), (s, tr.push rule_icmp_223.id)) := by
  compose_lookup 250 .ne

private theorem eval_decompose_slt :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .slt) []]).run (s, tr) =
      .ok (some (V.int 2), (s, tr.push rule_icmp_216.id)) := by
  compose_lookup 250 .slt

private theorem eval_decompose_sle :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .sle) []]).run (s, tr) =
      .ok (some (V.int 3), (s, tr.push rule_icmp_218.id)) := by
  compose_lookup 250 .sle

private theorem eval_decompose_sgt :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .sgt) []]).run (s, tr) =
      .ok (some (V.int 4), (s, tr.push rule_icmp_220.id)) := by
  compose_lookup 250 .sgt

private theorem eval_decompose_sge :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .sge) []]).run (s, tr) =
      .ok (some (V.int 5), (s, tr.push rule_icmp_222.id)) := by
  compose_lookup 250 .sge

private theorem eval_decompose_ult :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .ult) []]).run (s, tr) =
      .ok (some (V.int 2), (s, tr.push rule_icmp_215.id)) := by
  compose_lookup 250 .ult

private theorem eval_decompose_ule :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .ule) []]).run (s, tr) =
      .ok (some (V.int 3), (s, tr.push rule_icmp_217.id)) := by
  compose_lookup 250 .ule

private theorem eval_decompose_ugt :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .ugt) []]).run (s, tr) =
      .ok (some (V.int 4), (s, tr.push rule_icmp_219.id)) := by
  compose_lookup 250 .ugt

private theorem eval_decompose_uge :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx .uge) []]).run (s, tr) =
      .ok (some (V.int 5), (s, tr.push rule_icmp_221.id)) := by
  compose_lookup 250 .uge

end Leaves

/-- Evaluate the class helper once, independently of the surrounding graph proof. -/
theorem eval_icmp_class {p : Isle.Program} (hd : Data p)
    {σ : Type} (G : Isle.Opt.EGraph σ) (n : Nat) (cc : IntCC) (s : St σ) (tr : Array RuleId) :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 252 [V.data 46 (ccIdx cc) []]).run (s, tr) =
      .ok (some (V.int (icmpClassValue cc)), (s, tr.push (icmpClassRule cc))) := by
  cases cc with
  | eq => exact eval_class_eq hd G n s tr
  | ne => exact eval_class_ne hd G n s tr
  | slt => exact eval_class_slt hd G n s tr
  | sle => exact eval_class_sle hd G n s tr
  | sgt => exact eval_class_sgt hd G n s tr
  | sge => exact eval_class_sge hd G n s tr
  | ult => exact eval_class_ult hd G n s tr
  | ule => exact eval_class_ule hd G n s tr
  | ugt => exact eval_class_ugt hd G n s tr
  | uge => exact eval_class_uge hd G n s tr

/-- Evaluate the decomposition helper, preserving the exact state and trace. -/
theorem eval_icmp_decompose {p : Isle.Program} (hd : Data p)
    {σ : Type} (G : Isle.Opt.EGraph σ) (n : Nat) (cc : IntCC) (s : St σ) (tr : Array RuleId) :
    (Interp.applyTerm p (sem G).toSem cfg (n + 16) 4 250 [V.data 46 (ccIdx cc) []]).run (s, tr) =
      .ok (some (V.int (icmpDecomposeValue cc)), (s, tr.push (icmpDecomposeRule cc))) := by
  cases cc with
  | eq => exact eval_decompose_eq hd G n s tr
  | ne => exact eval_decompose_ne hd G n s tr
  | slt => exact eval_decompose_slt hd G n s tr
  | sle => exact eval_decompose_sle hd G n s tr
  | sgt => exact eval_decompose_sgt hd G n s tr
  | sge => exact eval_decompose_sge hd G n s tr
  | ult => exact eval_decompose_ult hd G n s tr
  | ule => exact eval_decompose_ule hd G n s tr
  | ugt => exact eval_decompose_ugt hd G n s tr
  | uge => exact eval_decompose_uge hd G n s tr

-- Concrete evaluations instantiate every leaf and both dispatchers. No graph
-- premises are needed: these helpers only inspect the condition-code tag.
private def lookupWitnessGraph : Isle.Opt.EGraph Unit where
  enodes := fun _ _ => []
  typeOf := fun _ _ => none
  make := fun s _ => (0, s)

private def lookupWitnessState : St Unit := { inner := () }

example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .eq) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 3), (lookupWitnessState, #[rule_icmp_248.id])) :=
  eval_class_eq data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .ne) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 3), (lookupWitnessState, #[rule_icmp_249.id])) :=
  eval_class_ne data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .slt) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 2), (lookupWitnessState, #[rule_icmp_244.id])) :=
  eval_class_slt data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .sle) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 2), (lookupWitnessState, #[rule_icmp_245.id])) :=
  eval_class_sle data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .sgt) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 2), (lookupWitnessState, #[rule_icmp_246.id])) :=
  eval_class_sgt data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .sge) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 2), (lookupWitnessState, #[rule_icmp_247.id])) :=
  eval_class_sge data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .ult) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 1), (lookupWitnessState, #[rule_icmp_240.id])) :=
  eval_class_ult data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .ule) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 1), (lookupWitnessState, #[rule_icmp_241.id])) :=
  eval_class_ule data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .ugt) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 1), (lookupWitnessState, #[rule_icmp_242.id])) :=
  eval_class_ugt data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 252
    [V.data 46 (ccIdx .uge) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 1), (lookupWitnessState, #[rule_icmp_243.id])) :=
  eval_class_uge data_program lookupWitnessGraph 0 lookupWitnessState #[]

example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .eq) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 1), (lookupWitnessState, #[rule_icmp_214.id])) :=
  eval_decompose_eq data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .ne) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 6), (lookupWitnessState, #[rule_icmp_223.id])) :=
  eval_decompose_ne data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .slt) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 2), (lookupWitnessState, #[rule_icmp_216.id])) :=
  eval_decompose_slt data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .sle) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 3), (lookupWitnessState, #[rule_icmp_218.id])) :=
  eval_decompose_sle data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .sgt) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 4), (lookupWitnessState, #[rule_icmp_220.id])) :=
  eval_decompose_sgt data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .sge) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 5), (lookupWitnessState, #[rule_icmp_222.id])) :=
  eval_decompose_sge data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .ult) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 2), (lookupWitnessState, #[rule_icmp_215.id])) :=
  eval_decompose_ult data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .ule) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 3), (lookupWitnessState, #[rule_icmp_217.id])) :=
  eval_decompose_ule data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .ugt) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 4), (lookupWitnessState, #[rule_icmp_219.id])) :=
  eval_decompose_ugt data_program lookupWitnessGraph 0 lookupWitnessState #[]
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 16 4 250
    [V.data 46 (ccIdx .uge) []]).run (lookupWitnessState, #[]) =
    .ok (some (V.int 5), (lookupWitnessState, #[rule_icmp_221.id])) :=
  eval_decompose_uge data_program lookupWitnessGraph 0 lookupWitnessState #[]

-- Nonempty traces and larger fuel also instantiate the public dispatchers.
example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 989 4 252
    [V.data 46 (ccIdx .ne) []]).run (lookupWitnessState, #[42]) =
    .ok (some (V.int 3), (lookupWitnessState, #[42, rule_icmp_249.id])) := by
  exact eval_icmp_class data_program lookupWitnessGraph 973 .ne lookupWitnessState #[42]

example : (Interp.applyTerm program (sem lookupWitnessGraph).toSem cfg 989 4 250
    [V.data 46 (ccIdx .slt) []]).run (lookupWitnessState, #[42]) =
    .ok (some (V.int 2), (lookupWitnessState, #[42, rule_icmp_216.id])) := by
  exact eval_icmp_decompose data_program lookupWitnessGraph 973 .slt lookupWitnessState #[42]

end Opt.Proof

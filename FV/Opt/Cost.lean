import FV.Opt.Basic

/-!
# Cost model (Cranelift 0.136.1 `egraph/cost.rs`)

Cranelift's extraction gives every value a cost and, among the equivalent forms of a value
(an e-class), keeps the one of least `(cost, value number)`:

* block parameters and skeleton results cost 0 (they are computed anyway);
* a pure node costs its opcode cost plus the costs of its operands (a *tree* cost: shared
  operands are counted once per use), saturating below `infinite`;
* opcode costs (`Cost::of_opcode`): constants 1; `uextend sextend ireduce iconcat isplit` 1;
  `iadd isub band bor bxor bnot ishl ushr sshr` 3; `imul` 10; everything else 4 (the pure
  nodes never get the trap/load/store surcharges).

`Cost.infinite` additionally marks nodes the pass may not emit (outside the backend's
subset E when the input is in E); such a form is never chosen.
-/

namespace Opt

open Clif

abbrev Cost := Nat

namespace Cost

def infinite : Cost := 2 ^ 32 - 1

/-- Saturating addition that stays finite for finite arguments (`Cost::add` + `finite`). -/
def add (a b : Cost) : Cost :=
  if a == infinite || b == infinite then infinite else min (a + b) (infinite - 1)

/-- `Cost::of_opcode` for the pure nodes. -/
def ofInst : Inst → Cost
  | .iconst .. => 1
  | .extend .. | .ireduce .. | .iconcat .. | .isplit .. => 1
  | .binary op _ _ _ => match op with
    | .iadd | .isub | .band | .bor | .bxor | .ishl | .ushr | .sshr => 3
    | .imul => 10
    | _ => 4
  | .unary .bnot _ _ => 3
  | _ => 4

end Cost

end Opt

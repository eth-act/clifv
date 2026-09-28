import FV.Opt.Basic

/-!
# The rewrite-rule interface

A rule set is Cranelift's `simplify` multi-constructor seen from the driver
(`FV/Opt/Simplify.lean`): given the value `v` of a freshly inserted pure node, return the
values equivalent to `v` that the rules produce. The graph is abstract (`σ`):

* `enodes st x`: the pure nodes defining `x` (`inst_data_value`; empty for block parameters
  and skeleton results). Operands are value ids.
* `typeOf st x`: the type of `x` (`value_type`; `i8` for `icmp`).
* `make st n`: `make_inst` — insert the pure node `n` (the driver hash-conses it and
  recursively simplifies it) and return its value.

Result: candidates `(value, subsume)` in rule order, the names of the rules that produced them,
and the new graph state. `.error` only for interpreter failures (an unmodelled extern, fuel).

Implementations: `Opt.HandRules.simplify` (a small hand-written stand-in) and the exported
Cranelift rules (`Opt.CraneliftRules`, via `Isle.Opt.simplify` — `docs/contracts/isle.md`).

**Proof obligation of a rule set** (`docs/contracts/midend.md`): every candidate `w` of `v`
evaluates, in every register file where the nodes reachable from `v` evaluate, to the same
value as `v` (and has the same type), and every node passed to `make` has operands among
the values reachable from `v` (or made earlier), so it can be placed where `v` is defined.
-/

namespace Opt

open Clif

abbrev SimplifyFn := {σ : Type} → (σ → ValueId → List Inst) → (σ → ValueId → Option Ty) →
  (σ → Inst → ValueId × σ) → σ → ValueId → Except String (List (ValueId × Bool) × List String × σ)

/-- The available rule sets (`Opt.RuleSetId.fn` in `FV/Opt/Optimize.lean`). -/
inductive RuleSetId where
  /-- `Opt.HandRules.simplify`. -/
  | hand
  deriving DecidableEq, Repr, Inhabited

def RuleSetId.name : RuleSetId → String
  | .hand => "hand"

def RuleSetId.all : List RuleSetId := [.hand]

end Opt

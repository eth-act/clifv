import FV.Opt.Basic
import FV.Isle.Opt.Simplify

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

Implementations: the exported Cranelift rules (`Isle.Opt.simplify`, `docs/contracts/isle.md`)
and `Opt.HandRules.simplify` (a small hand-written stand-in).

**Proof obligation of a rule set** (`docs/contracts/midend.md`): every candidate `w` of `v`
evaluates, in every register file where the nodes reachable from `v` evaluate, to the same
value as `v` (and has the same type), and every node passed to `make` has operands among
the values reachable from `v` (or made earlier), so it can be placed where `v` is defined.
-/

namespace Opt

open Clif

abbrev SimplifyFn := {σ : Type} → (σ → ValueId → List Inst) → (σ → ValueId → Option Ty) →
  (σ → Inst → ValueId × σ) → σ → ValueId → Except String (List (ValueId × Bool) × List String × σ)

/-- Cranelift's `simplify_skeleton`: simplifications of a side-effecting instruction or a
terminator (`Isle.Opt.SkelInst`), e.g. `udiv x, 8 ⇒ ushr x, 3` (`removeWithVal`),
`brif 1, b1, b2 ⇒ jump b1` (`replace`), `brif c, trap_block, b ⇒ trapnz c; jump b`
(`replaceWithTwo`). The extra callback is `just_trap_block`: the trap code of a block whose
body is pure and whose terminator is `trap`.

**Proof obligation:** each simplification is equivalent to the original instruction (same
results, same trap behaviour, same successor with the same arguments) in every state where
the nodes reachable from its operands evaluate. -/
abbrev SkeletonFn := {σ : Type} → (σ → ValueId → List Inst) → (σ → ValueId → Option Ty) →
  (σ → Inst → ValueId × σ) → (σ → BlockId → Option TrapCode) → σ → Isle.Opt.SkelInst →
  Except String (List Isle.Opt.SkelSimp × List String × σ)

/-- The available rule sets (`Opt.RuleSetId.fn` in `FV/Opt/Optimize.lean`). -/
inductive RuleSetId where
  /-- Cranelift 0.136.1's `simplify` rules, exported (`Isle.Opt.program`) and run by the ISLE
  multi-term interpreter (`Isle.Opt.simplify`, `docs/contracts/isle.md`). -/
  | cranelift
  /-- `Opt.HandRules.simplify`. -/
  | hand
  deriving DecidableEq, Repr, Inhabited

def RuleSetId.name : RuleSetId → String
  | .cranelift => "cranelift"
  | .hand => "hand"

def RuleSetId.all : List RuleSetId := [.cranelift, .hand]

end Opt

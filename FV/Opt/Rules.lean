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

/-- Ids (`Isle.Rule.id`) of the exported `simplify` rules whose correctness is proven
(`Opt.Proof.simplifyRulesCorrect_proven`, `FV/Opt/Proof/RuleAll.lean`): the rules proven in
`FV/Opt/Proof/RuleArith.lean` and `RuleCprop.lean`. -/
def provenSimplifyRules : List Nat :=
  [65, 66, 67, 68, 69, 70, 71, 72, 78, 111, 113, 114, 115, 116, 117, 126, 127, 128, 129, 130, 131,
   132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 152, 153, 154, 155,
   157, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
   176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 203, 222, 223, 224, 225,
   226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243,
   244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261,
   262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279,
   280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297,
   298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315,
   316, 317, 318, 319, 320, 321, 334, 819, 820, 821, 822, 823, 828, 829, 830, 831, 837, 838,
   839, 840, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860,
   861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 895,
   896, 897, 898, 899, 945]

/-- Which exported rules may contribute candidates (`Isle.Opt.simplify`'s allow-list); the other
rules still run, their candidates are dropped. -/
inductive RuleAllow where
  /-- Every rule (default; not yet proven). -/
  | all
  /-- Only `provenSimplifyRules` (no skeleton rule is proven yet, so none contributes). -/
  | proven
  /-- An explicit list of rule ids. -/
  | ids (l : List Nat)
  deriving DecidableEq, Repr, Inhabited

def RuleAllow.pred : RuleAllow → Nat → Bool
  | .all => fun _ => true
  | .proven => fun r => provenSimplifyRules.contains r
  | .ids l => fun r => l.contains r

end Opt

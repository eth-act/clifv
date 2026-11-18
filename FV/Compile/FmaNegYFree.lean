import FV.Clif.Syntax

/-!
# `fma` whose second operand is an `fneg` (#35)

Cranelift folds an `fneg` into the scalar `fma` roots (`lower.isle:608-641`). The folds of an
`fneg` on the first operand (`fmadd` rule 2 → `fmsub`; `fnmsub` rule 2 → `fnmadd`) and on the
addend (`rule_lower_609` → `fnmsub`) place the sign flip where CLIF has it, so they are exact,
NaN operands included. The fold of an `fneg` on the **second** operand (`fmadd`/`fnmsub` rule 3,
the highest priority) emits `fmsub`/`fnmadd` of the un-negated operands, which negate the
*first* multiplicand instead: `FPMulAdd(z, −x, y)` against CLIF's `FPMulAdd(z, x, −y)`. Both
round the same real number, but when `x` or `y` is a NaN the result NaN's sign differs
(`FVTest/Backend/FloatFmaWitness.lean`, `fmsub_negY_nan_differs`). CLIF's semantics here are
deterministic (`FPProcessNaNs`), so such a function is outside the verified scope.

`fmaNegYFree f`: no `fma` statement of `f` has a second operand that is a result of an `fneg`
statement of `f`. Soundness against `buildCtx`'s context:
`Backend.Proof.fmaNegYFree_of_buildCtx` (`FV/Backend/Proof/FmaNegYFreeCtx.lean`).
-/

namespace Compile

open Clif

/-- The results of the `fneg` statements of `f`. -/
def fnegDefs (f : Function) : List ValueId :=
  f.blocks.flatMap fun b => b.body.flatMap fun s => match s.inst with
    | .float .fneg _ _ => s.results
    | _ => []

/-- **No `fma` of `f` has an `fneg`-defined second operand** (decided). -/
def fmaNegYFree (f : Function) : Bool :=
  let nd := fnegDefs f
  f.blocks.all fun b => b.body.all fun s => match s.inst with
    | .float .fma _ [_, y, _] => !nd.contains y
    | _ => true

/-- **Soundness of `fmaNegYFree`**: the second operand of an `fma` statement is no result of an
`fneg` statement. -/
theorem fmaNegYFree_sound {f : Function} (h : fmaNegYFree f = true) {b : Block}
    (hb : b ∈ f.blocks) {s : Stmt} (hs : s ∈ b.body) {ty : Ty} {x y z : ValueId}
    (hi : s.inst = .float .fma ty [x, y, z]) {b' : Block} (hb' : b' ∈ f.blocks) {s' : Stmt}
    (hs' : s' ∈ b'.body) {ty' : Ty} {args : List ValueId}
    (hi' : s'.inst = .float .fneg ty' args) : y ∉ s'.results := by
  intro hy
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h b hb) s hs
  rw [hi] at h1
  have hm : y ∈ fnegDefs f := by
    simp only [fnegDefs, List.mem_flatMap]
    exact ⟨b', hb', s', hs', by rw [hi']; exact hy⟩
  simp [List.contains_iff_mem, hm] at h1

end Compile

import FV.Clif.Parse
import FV.Opt.ConstPhi
import FV.Opt.MidVal

/-! # `Opt.MidVal.check` on the hand-made pairs of `FVTest/Opt/midval/` (#1119)

Regression witnesses of the executable validator (no soundness theorem yet): every `pos_*` pair
is accepted and every `neg_*` pair rejected, decided by `native_decide` (test module). The
negative pairs are the counterexamples of the design (issuecomment-7009592817): a dead trapping
load dropped, forwarding across a call, a join with a store on one path, another byte order,
another type, a `can_move` load hoisted above its guard, `readonly` loads merged across a store,
and a pure node that can be `stuck` (an ill-typed `fadd`) evaluated where `f` does not. -/

namespace Opt.MidVal.Pairs

open Clif

/-- The first function of a CLIF text, if it parses. -/
def fn? (s : String) : Option Function := do
  let p ← (parseFile s).funcs[0]?
  p.func.toOption

/-- The verdict the checker gives the pair `(f, g)` (after constant-phi removal of `f`); `none`
if a text does not parse (so no witness holds vacuously). -/
def accepts (f g : String) : Option Bool := do
  pure (check (ConstPhi.run (← fn? f)) (← fn? g)).isOk

theorem neg_call : accepts "function %f(i64, i64) -> i64 {\n    fn0 = %g()\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    call fn0()\n    v2 = load.i64 v0\n    return v2\n}"
    "function %f(i64, i64) -> i64 {\n    fn0 = %g()\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    call fn0()\n    return v1\n}" = some false := by native_decide

theorem neg_deadload : accepts "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = load.i64 v0\n    return v0\n}"
    "function %f(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}" = some false := by native_decide

theorem neg_endian : accepts "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    v2 = load.i64 big v0\n    return v2\n}"
    "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    return v1\n}" = some false := by native_decide

theorem neg_hoist : accepts "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    brif v1, block1, block2\nblock1:\n    v2 = load.i64 notrap readonly can_move v0\n    return v2\nblock2:\n    return v0\n}"
    "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = load.i64 notrap readonly can_move v0\n    brif v1, block1, block2\nblock1:\n    return v2\nblock2:\n    return v0\n}" = some false := by native_decide

theorem neg_merge : accepts "function %f(i64, i64, i64) -> i64 {\nblock0(v0: i64, v1: i64, v2: i64):\n    store.i64 v1, v0\n    brif v2, block1, block2\nblock1:\n    store.i64 v2, v0\n    jump block3\nblock2:\n    jump block3\nblock3:\n    v3 = load.i64 v0\n    return v3\n}"
    "function %f(i64, i64, i64) -> i64 {\nblock0(v0: i64, v1: i64, v2: i64):\n    store.i64 v1, v0\n    brif v2, block1, block2\nblock1:\n    store.i64 v2, v0\n    jump block3\nblock2:\n    jump block3\nblock3:\n    return v1\n}" = some false := by native_decide

theorem neg_readonly : accepts "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = load.i64 notrap readonly v0\n    store.i64 v1, v0\n    v3 = load.i64 notrap readonly v0\n    v4 = iadd v2, v3\n    return v4\n}"
    "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = load.i64 notrap readonly v0\n    store.i64 v1, v0\n    v4 = iadd v2, v2\n    return v4\n}" = some false := by native_decide

theorem neg_stuckpure : accepts "function %f(f64, i8) -> f64 {\nblock0(v0: f64, v1: i8):\n    brif v1, block1, block2\nblock1:\n    return v0\nblock2:\n    return v0\n}"
    "function %f(f64, i8) -> f64 {\nblock0(v0: f64, v1: i8):\n    v9 = fadd.f64 v0, v1\n    brif v1, block1, block2\nblock1:\n    return v0\nblock2:\n    return v0\n}" = some false := by native_decide

theorem neg_type : accepts "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    v2 = load.i32 v0\n    v3 = uextend.i64 v2\n    return v3\n}"
    "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    v2 = ireduce.i32 v1\n    v3 = uextend.i64 v2\n    return v3\n}" = some false := by native_decide

theorem pos_deadnotrap : accepts "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = load.i64 notrap v0\n    return v0\n}"
    "function %f(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}" = some true := by native_decide

theorem pos_fwd : accepts "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    v2 = load.i64 v0\n    return v2\n}"
    "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    return v1\n}" = some true := by native_decide

theorem pos_merge : accepts "function %f(i64, i64, i64) -> i64 {\nblock0(v0: i64, v1: i64, v2: i64):\n    store.i64 v1, v0\n    brif v2, block1, block2\nblock1:\n    v9 = iconst.i64 0\n    jump block3\nblock2:\n    jump block3\nblock3:\n    v3 = load.i64 v0\n    return v3\n}"
    "function %f(i64, i64, i64) -> i64 {\nblock0(v0: i64, v1: i64, v2: i64):\n    store.i64 v1, v0\n    brif v2, block1, block2\nblock1:\n    v9 = iconst.i64 0\n    jump block3\nblock2:\n    jump block3\nblock3:\n    return v1\n}" = some true := by native_decide

theorem pos_rle : accepts "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = load.i64 v0+8\n    v2 = iconst.i64 1\n    v3 = load.i64 v0+8\n    v4 = iadd v1, v3\n    v5 = iadd v4, v2\n    return v5\n}"
    "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = load.i64 v0+8\n    v4 = iadd v1, v1\n    v9 = iconst.i64 1\n    v5 = iadd v4, v9\n    return v5\n}" = some true := by native_decide

end Opt.MidVal.Pairs

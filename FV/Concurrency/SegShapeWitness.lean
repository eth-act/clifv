module

public import FV.Concurrency.SegShape
public import FV.Clif.Parse

@[expose] public section

/-!
# Non-vacuity of layer 2c (T2h, #311)

`atomics_segShape`: the driver's lowering of a function with `atomic_load`, `atomic_store`,
`atomic_rmw`, `atomic_cas`, `fence`, `load` and `store` passes `segShapeCheck` (evaluated with
`native_decide`).
-/

namespace Concurrency.SegShape.Witness

/-- A function with every memory statement of the multi-threaded scope. -/
def src : String := "function %atomics(i64, i64, i64) -> i64 {
block0(v0: i64, v1: i64, v2: i64):
    v3 = atomic_load.i64 v0
    atomic_store.i64 v1, v0
    v4 = atomic_rmw.i64 add v0, v1
    v5 = atomic_cas.i64 v0, v1, v2
    fence
    v6 = load.i64 v0
    store.i64 v2, v0
    v7 = iadd v3, v4
    v8 = iadd v5, v6
    v9 = iadd v7, v8
    return v9
}
"

/-- The parsed function. -/
def fA : Clif.Function :=
  match Clif.parse src with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- **Non-vacuity of `segShapeCheck`**: the function has the seven memory statements (`fA` is
the parsed function, not the default), and its lowering passes the check. -/
theorem atomics_segShape :
    (fA.blocks.headD default).body.length = 10 ∧ segShapeCheck fA = true := by
  native_decide

end Concurrency.SegShape.Witness

import FV.Opt.Proof.ConstPhiSimU

/-!
# Non-vacuity of constant-phi removal's theorems (#990)

`fwd`: `block0(v0)` jumps to `block1(v0)`, which returns its parameter `v1`. The parameter `v1`
can only hold `v0`: `cpOk` accepts the solution `[(1, 0)]` (`fwd_ok`) and the rewrite changes
the function (`fwd_changed`), so `Opt.ConstPhi.cpOk_simU` relates two different functions
(`fwd_simU`); the pass itself finds the solution and keeps the result (`fwd_run`), so
`Opt.ConstPhi.run_simU` does too.
-/

namespace Opt.ConstPhi.Witness

open Clif

/-- `block0(v0: i64): jump block1(v0)`; `block1(v1: i64): return v1`. -/
def fwd : Function where
  name := "fwd"
  sig := { params := [{ ty := .i64 }], returns := [{ ty := .i64 }] }
  blocks := [
    { id := 0, params := [(0, .i64)], term := .jump ⟨1, [0]⟩ },
    { id := 1, params := [(1, .i64)], term := .ret [1] }]

/-- The function without the parameter: `block1` returns `v0`. -/
def fwd' : Function :=
  { fwd with blocks := [
    { id := 0, params := [(0, .i64)], term := .jump ⟨1, []⟩ },
    { id := 1, params := [], term := .ret [0] }] }

theorem fwd_ok : cpOk fwd [(1, 0)] = true := by decide +kernel

theorem fwd_apply : apply fwd [(1, 0)] = fwd' := by decide +kernel

theorem fwd_changed : fwd' ≠ fwd := by decide +kernel

theorem fwd_run : run fwd = fwd' := by decide +kernel

/-- **`cpOk_simU` relates two different functions.** -/
theorem fwd_simU : FunSimU fwd fwd' := fwd_apply ▸ cpOk_simU fwd_ok

/-- **`run_simU` relates two different functions.** -/
theorem fwd_run_simU : FunSimU fwd fwd' := fwd_run ▸ run_simU fwd

end Opt.ConstPhi.Witness

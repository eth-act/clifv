import FV.Opt.RetypeVec
import FV.Opt.Proof.RetypeSim

/-!
# Non-vacuity of the vector retyping (S12e, #36)

`sha2Shape`: the shape of the measured sha2 functions (`docs/plans/simd.md` §1) is in the domain
of `Opt.Retype.vecInt` and changed by it (`sha2Shape_retyped`), so `Opt.Retype.retype_simX`
relates it to its retyping (`sha2Shape_sim`).
-/

namespace Opt.Retype.Witness

open Clif

/-- The shape of the measured sha2 functions: two vector loads into a stack slot, a shim call
on the slot, the result reloaded and stored to the return place. -/
def sha2Shape : Function where
  name := "sha2_shape"
  sig := { params := [{ ty := .i64 }, { ty := .i64 }, { ty := .i64 }] }
  slots := [(0, { size := 32 })]
  externs := [(0, { name := "shim", sig := { params := [{ ty := .i64 }] } })]
  blocks := [{
    id := 0
    params := [(0, .i64), (1, .i64), (2, .i64)]
    body := [⟨[3], .load .load (.vec .i64x2) default 1 0⟩,
      ⟨[4], .load .load (.vec .i64x2) default 2 0⟩,
      ⟨[5], .stackAddr .i64 0 0⟩,
      ⟨[], .store .store (.vec .i64x2) default 3 5 0⟩,
      ⟨[], .store .store (.vec .i64x2) default 4 5 16⟩,
      ⟨[], .call 0 [5]⟩,
      ⟨[9], .load .load (.vec .i64x2) default 5 0⟩,
      ⟨[], .store .store (.vec .i64x2) default 9 0 0⟩]
    term := .ret [] }]

/-- In the domain, changed by the retyping: `retypeVec` retypes it. -/
theorem sha2Shape_retyped : okB vecInt sha2Shape = true ∧ retypeVec sha2Shape ≠ sha2Shape := by
  decide +kernel

/-- **`retype_simX` applies to the sha2 shape at `vecInt`.** -/
theorem sha2Shape_sim : FunSimX sha2Shape (retype vecInt sha2Shape) := by
  exact retype_simX sha2Shape sha2Shape_retyped.1

end Opt.Retype.Witness

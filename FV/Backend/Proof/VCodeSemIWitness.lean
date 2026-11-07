import FV.Backend.Proof.VCodeSemI

/-!
# Witnesses for the counted VCode semantics (`FV/Backend/Proof/VCodeSemI.lean`)

`XW`: call number `n` returns the value `n` and keeps the world. Under `csemI` the same `call`
from the same Arm world gives `0` as the activation's first call and `1` as its second, and
bumps the counter (`csemI_call`); a `jump` keeps it (`csemI_noncall`). Under `ExtSemI.const`
both calls give the same result (`csemI_const_projW`: today's `csem`).
-/

namespace Backend.Proof.VCodeSemIWitness

open Backend Backend.Proof

/-- Call number `n` returns `n`, the world unchanged. -/
def XW : ExtSemI :=
  { call := fun n _ _ w => some ([BitVec.ofNat 128 n], w), sym := fun _ _ => 0, tp := 0,
    tlsFlags := fun _ w => Arm.read_pstate w }

/-- A call with one def (`csem` keeps one result per def, #587). -/
def c1 : CallInfo := { (default : CallInfo) with defs := [(.x 0, .x 0)] }

/-- The first call of the activation returns `0`, the second `1`: the counter decides. -/
theorem call_counted (F : BitVec 64 → Prop) (ctx : FnCtx) (w : Arm.ArmState) :
    csemI F ctx XW (.call c1) [] (w, 0) = some ([0#128], (w, 1), .next) ∧
    csemI F ctx XW (.call c1) [] (w, 1) = some ([1#128], (w, 2), .next) :=
  ⟨rfl, rfl⟩

/-- The same call at counters `0` and `1` gives different results. -/
theorem call_counted_ne (F : BitVec 64 → Prop) (ctx : FnCtx) (w : Arm.ArmState) :
    csemI F ctx XW (.call c1) [] (w, 0) ≠ csemI F ctx XW (.call c1) [] (w, 1) := by
  rw [(call_counted F ctx w).1, (call_counted F ctx w).2]
  intro h
  simp at h

/-- `csemI_call`'s instance: a `call` is `csem` at its own index, the counter bumped. -/
theorem call_eq (F : BitVec 64 → Prop) (ctx : FnCtx) (w : Arm.ArmState) :
    csemI F ctx XW (.call default) [] (w, 5) =
      (csem F ctx (XW.at 5) (.call default) [] w).map fun r => (r.1, (r.2.1, 6), r.2.2) :=
  csemI_call F ctx XW rfl [] w 5

/-- `csemI_noncall`'s instance: a `jump` keeps the counter. -/
theorem jump_keeps (F : BitVec 64 → Prop) (ctx : FnCtx) (w : Arm.ArmState) :
    csemI F ctx XW (.jump default) [] (w, 3) = some ([], (w, 3), .goto 0) := by
  rw [csemI_noncall F ctx XW rfl [] w 3 0]
  rfl

/-- With one `ExtSem` for every call the result does not depend on the counter
(`csemI_const_projW` applied to the first call at counter `7`). -/
theorem const_proj (F : BitVec 64 → Prop) (ctx : FnCtx) (w : Arm.ArmState) :
    csem F ctx (XW.at 0) (.call c1) [] w = some ([0#128], w, .next) :=
  csemI_const_projW F ctx (XW.at 0) (.call c1) [] (w, 7) [0#128] (w, 8) .next rfl

end Backend.Proof.VCodeSemIWitness

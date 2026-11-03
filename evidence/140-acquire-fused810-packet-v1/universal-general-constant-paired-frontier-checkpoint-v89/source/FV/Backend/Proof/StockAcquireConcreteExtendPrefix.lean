import FV.Backend.Proof.StockAcquireConcreteExtendTotal
import FV.E2E.RegLevelSim

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The existing machine relation supplies the reference world's error and alignment facts internally. -/
theorem stRel_world_error_aligned {R : RL} {physical world : Arm.ArmState} {values : Loc → CV}
    (related : StRel R physical values world) :
    Arm.r .ERR world = .None ∧ Arm.CheckSPAlignment world := by
  have errors := related.world.1 .ERR (by simp [Masked])
  have stack := related.world.1 (.GPR 31#5) (by simp [Masked])
  constructor
  · rw [← errors]
    exact related.err
  · rw [checkSP_iff]
    have original := related.align
    rw [checkSP_iff] at original
    change (Arm.r (.GPR 31#5) world).toNat % 16 = 0
    rw [← stack]
    exact original

/-- A legal concrete extension prefix needs no future source step or extra caller world condition.
Its original register-level relation supplies the machine facts; every other virtual register is preserved. -/
theorem regLevel_unsigned_small_extend_prefix {R : RL}
    {physical world : Arm.ArmState} {values : Loc → CV}
    (related : StRel R physical values world)
    {dest pointer fromB toB : Nat} (width : fromB = 8 ∨ fromB = 16) (regs : Nat → CV) :
    ∃ nextRegs nextWorld,
      seqRun (csem R.F R.ctx R.X) [MInst.extend (.vreg dest .int) (.vreg pointer .int) false fromB toB]
        regs world = some (.fall nextRegs nextWorld) ∧
      SameWorld R.F nextWorld world ∧ (∀ key,key ≠ dest → nextRegs key = regs key) := by
  obtain ⟨errorFree,aligned⟩ := stRel_world_error_aligned related
  obtain ⟨nextWorld,executed,same⟩ := csem_unsigned_small_extend_total (ctx := R.ctx) (X := R.X)
    (dest := dest) (pointer := pointer) (toB := toB) width (regs pointer) errorFree aligned
  let value := ofX ((((lo64 (regs pointer)).setWidth fromB).setWidth 32).setWidth 64)
  refine ⟨upd regs dest value,nextWorld,?_,same,?_⟩
  · simp only [seqRun,operands_extend']
    have uses : vuses #[⟨dest,.int,.def,.late,.reg⟩,⟨pointer,.int,.use,.early,.reg⟩] regs = [regs pointer] := rfl
    rw [uses,executed]
    rfl
  · intro key different
    simp only [upd,different,ite_false]

end Backend.Stock.Proof.Acquire810

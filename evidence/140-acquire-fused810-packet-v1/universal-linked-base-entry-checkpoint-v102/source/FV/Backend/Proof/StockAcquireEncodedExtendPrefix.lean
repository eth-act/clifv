import FV.Backend.Proof.StockAcquireExtendEncoding

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual emitted lines derive encoding legality; the original machine relation derives world facts.
All 25 encoded scalar cases execute without evaluating a later source instruction. -/
theorem regLevel_encoded_extend_prefix {R : RL} {physical world : Arm.ArmState} {values : Loc → CV}
    (related : StRel R physical values world)
    {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    {env : Backend.Env} {machineDest machinePointer : Reg} {state next : PState} {lines : List Line}
    (expanded : (MInst.extend machineDest machinePointer signed fromB toB).lines R.ctx state = .ok (lines,next))
    (encoded : ∀ instruction trap,Line.ins instruction trap ∈ lines →
      ∃ arm,instruction.armFields env = .ok arm) (regs : Nat → CV) :
    ∃ nextRegs nextWorld,
      seqRun (csem R.F R.ctx R.X) [MInst.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB]
        regs world = some (.fall nextRegs nextWorld) ∧ SameWorld R.F nextWorld world ∧
      (∀ key,key ≠ dest → nextRegs key = regs key) := by
  have legal := extend_encoded_lines_widths sourceWidth targetWidth expanded encoded
  obtain ⟨errorFree,aligned⟩ := stRel_world_error_aligned related
  obtain ⟨output,nextWorld,executed,same⟩ := csem_extend_encoded_total (ctx := R.ctx) (X := R.X)
    (dest := dest) (pointer := pointer) sourceWidth targetWidth legal (regs pointer) errorFree aligned
  refine ⟨upd regs dest output,nextWorld,?_,same,?_⟩
  · simp only [seqRun,operands_extend']
    have uses : vuses #[⟨dest,.int,.def,.late,.reg⟩,⟨pointer,.int,.use,.early,.reg⟩] regs = [regs pointer] := rfl
    rw [uses,executed]
    rfl
  · intro key different
    simp only [upd,different,ite_false]

end Backend.Stock.Proof.Acquire810

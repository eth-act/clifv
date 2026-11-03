import FV.Backend.Proof.StockAcquireEncodedExtendPrefix
import FV.E2E.Pair
import FV.E2E.Lockstep

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The identical canonical instruction has one exact output in every world. -/
theorem encoded_extend_canonical_output {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    (encoded : fromB ≤ 32 ∨ (signed = true ∧ toB = 64)) (value : CV) (world : Arm.ArmState) :
    ispec (concreteExtendCanonical signed fromB toB dest pointer) [value] world =
      some ([concreteExtendOutput signed fromB toB value],world,.next) := by
  rcases sourceWidth with rfl | rfl | rfl | rfl <;>
    rcases targetWidth with rfl | rfl | rfl | rfl <;> cases signed
  all_goals simp at encoded
  all_goals rfl

/-- Concrete extension produces that exact output without a source instruction step. -/
theorem csem_encoded_extend_output {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    (encoded : fromB ≤ 32 ∨ (signed = true ∧ toB = 64))
    (value : CV) {world : Arm.ArmState}
    (errorFree : Arm.r .ERR world = .None) (aligned : Arm.CheckSPAlignment world) :
    ∃ nextWorld,csem F ctx X (.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB) [value] world =
      some ([concreteExtendOutput signed fromB toB value],nextWorld,.next) ∧ SameWorld F nextWorld world := by
  obtain ⟨nextWorld,executed,same⟩ := refines_csem F ctx X _ _ _ _ _
    (encoded_extend_canonical_output (dest := dest) (pointer := pointer) sourceWidth targetWidth encoded value world)
  have control : (MInst.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB).isCtl = false := rfl
  have wellFormed : csemWF ctx (.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB) [value] = true := rfl
  have canonicalControl : (concreteExtendCanonical signed fromB toB dest pointer).isCtl = false := by
    unfold concreteExtendCanonical
    split <;> rfl
  have canonicalWf : csemWF ctx (concreteExtendCanonical signed fromB toB dest pointer) [value] = true := by
    unfold concreteExtendCanonical
    split <;> rfl
  rw [csem_of_wf canonicalControl canonicalWf errorFree aligned] at executed
  refine ⟨nextWorld,?_,same⟩
  rw [csem_of_wf control wellFormed errorFree aligned,straight_extend_canonical sourceWidth targetWidth value world]
  exact executed

/-- Original machine relations and actual encoded lines derive one paired concrete prefix.
Every other virtual register and the original world agreement remain unchanged. -/
theorem regLevel_encoded_extend_paired_prefix {R : RL}
    {physicalLeft physicalRight : Arm.ArmState} {valuesLeft valuesRight : Loc → CV} {worlds : W2}
    (left : StRel R physicalLeft valuesLeft worlds.1) (right : StRel R physicalRight valuesRight worlds.2)
    {Z : BitVec 64 → Prop} (includes : ∀ a,R.F a → Z a) (agreement : SameWorld Z worlds.1 worlds.2)
    {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32 ∨ fromB = 64)
    (targetWidth : toB = 8 ∨ toB = 16 ∨ toB = 32 ∨ toB = 64)
    {env : Backend.Env} {machineDest machinePointer : Reg} {state next : PState} {lines : List Line}
    (expanded : (MInst.extend machineDest machinePointer signed fromB toB).lines R.ctx state = .ok (lines,next))
    (encoded : ∀ instruction trap,Line.ins instruction trap ∈ lines →
      ∃ arm,instruction.armFields env = .ok arm) (regs : Nat → CV) :
    ∃ nextRegs nextWorlds,
      seqRun (pairSem (csem R.F R.ctx R.X))
        [MInst.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB] regs worlds =
          some (.fall nextRegs nextWorlds) ∧
      SameWorld R.F nextWorlds.1 worlds.1 ∧ SameWorld R.F nextWorlds.2 worlds.2 ∧
      SameWorld Z nextWorlds.1 nextWorlds.2 ∧
      (∀ key,key ≠ dest → nextRegs key = regs key) := by
  have legal := extend_encoded_lines_widths sourceWidth targetWidth expanded encoded
  obtain ⟨leftError,leftAligned⟩ := stRel_world_error_aligned left
  obtain ⟨rightError,rightAligned⟩ := stRel_world_error_aligned right
  obtain ⟨nextLeft,leftRun,leftFrame⟩ := csem_encoded_extend_output (F := R.F) (ctx := R.ctx) (X := R.X)
    (dest := dest) (pointer := pointer) sourceWidth targetWidth legal (regs pointer) leftError leftAligned
  obtain ⟨nextRight,rightRun,rightFrame⟩ := csem_encoded_extend_output (F := R.F) (ctx := R.ctx) (X := R.X)
    (dest := dest) (pointer := pointer) sourceWidth targetWidth legal (regs pointer) rightError rightAligned
  have paired := pairSem_eq leftRun rightRun
  refine ⟨upd regs dest (concreteExtendOutput signed fromB toB (regs pointer)),(nextLeft,nextRight),?_,leftFrame,rightFrame,?_,?_⟩
  · simp only [seqRun,operands_extend']
    have uses : vuses #[⟨dest,.int,.def,.late,.reg⟩,⟨pointer,.int,.use,.early,.reg⟩] regs = [regs pointer] := rfl
    rw [uses,paired]
    rfl
  · exact SameWorld.trans (SameWorld.mono includes leftFrame)
      (SameWorld.trans agreement (SameWorld.symm (SameWorld.mono includes rightFrame)))
  · intro key different
    simp only [upd,different,ite_false]

end E2E.StockAcquirePending

import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockJumpBodyRefines
import FV.Backend.Proof.StockMaskBlockWitness

namespace Backend.Stock.Proof.ControlWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.lower Stock.runTerm

private abbrev function := QuietBlockWitness.function
private def zero : Clif.Val := ⟨.i64,0⟩
private def frame : Clif.Frame := {
  func := function
  regs := (Clif.Regs.empty.set 1 zero).set 6 ⟨.i64,1⟩
  slots := []
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
    decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)

/-- An actual returning two-block source run executes the complete first core,
including its jump. The guarded input is derived from executable source entry;
this virtual-register witness does not assume a machine body execution. -/
theorem executable_jump_return_witness (X : ExtSem) :
    ∃ result, ∃ (spec : Control.JumpBodySpec function result function.blocks[0]! 0 0 ⟨10,[1,6]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ t left ρ' w',
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [zero,⟨.i64,1⟩] Clif.Mem.empty = .ok (frame,Clif.Mem.empty) ∧
      left+2 = 6 ∧ Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [zero] Clif.Mem.empty ∧
      t.frame.body = [] ∧ t.frame.term = .jump ⟨10,[1,6]⟩ ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx frame) Arm.ArmState.default =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ' w' [] w' (.goto 0)) ∧
      GuardedScanRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
        spec.term.output.state (2,t.frame,t.mem) ρ' w' := by
  obtain ⟨result,event,term,body,run,scope,dominated,rest⟩ :=
    MaskBlockWitness.actual_family_records_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag
    (b := function.blocks[0]!) rfl (bc := ⟨10,[1,6]⟩) rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X)
    (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable Clif.Env.empty {funcs := []}
  have entered : Clif.enterFunc function [zero,⟨.i64,1⟩] Clif.Mem.empty =
      .ok (frame,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 6 ⟨frame,[],Clif.Mem.empty⟩ =
      .returned [zero] Clif.Mem.empty := rfl
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  obtain ⟨t,left,ρ',w',total,continued,empty,frameEq,jump,executed,post⟩ :=
    spec.returns 6 ⟨frame,[],Clif.Mem.empty⟩ [zero] Clif.Mem.empty rfl rfl returned
      (entrySeed spec.core.scan.ctx frame) Arm.ArmState.default held
  exact ⟨result,spec,t,left,ρ',w',run,scope,dominated,entered,total,continued,empty,jump,executed,post⟩

end Backend.Stock.Proof.ControlWitness

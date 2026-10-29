module

public import FV.Backend.Proof.StockJumpEdgeParameters
public import FV.Backend.Proof.StockJumpBodyWitness

@[expose] public section

namespace Backend.Stock.Proof.ControlWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := QuietBlockWitness.function

/-- The real entered-source returning run supplies both emitted jump execution
and all outgoing argument values for that very core. Neither a demand premise
nor a machine-value certificate is supplied by the witness. -/
theorem executable_jump_argument_values_witness (X : ExtSem) :
    ∃ result, ∃ (spec : Control.JumpBodySpec function result function.blocks[0]! 0 0 ⟨10,[1,6]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ initial t left ρ w,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,0⟩,⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      left+2 = 6 ∧ Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [⟨.i64,0⟩] Clif.Mem.empty ∧
      t.frame.body = [] ∧ t.frame.term = .jump ⟨10,[1,6]⟩ ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ w [] w (.goto 0)) ∧
      (∀ x ∈ ([1,6] : List Nat),Demanded spec.term.output.state x) ∧
      ValuesHeld (fun x => x ∈ ([1,6] : List Nat)) result.ctx t.frame
        (fun k => ρ (aliasNum result.final.alias k)) := by
  obtain ⟨result,spec,t,left,ρ,w,run,scope,dominated,entered,total,continued,empty,jump,executed,post⟩ :=
    executable_jump_return_witness X
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (by with_unfolding_all rfl))
  have targetValue : spec.target = 1 := by
    have labels := spec.targets
    rw [order] at labels
    exact (List.cons.inj labels).1.symm
  have target : result.order.nodes[spec.target]? = some (.original 1) := by
    rw [order,targetValue]
    rfl
  have demanded := Control.stock_jump_body_arguments_demanded run scope spec rfl target
  have values := Control.stock_jump_body_argument_values run scope dominated spec rfl target post
  exact ⟨result,spec,_,t,left,ρ,w,run,scope,dominated,entered,total,continued,empty,jump,executed,
    demanded,values⟩


/-- Actual original source entry, body/jump execution and successor binding
execute the retained per-edge copies and establish the target parameter values. -/
theorem executable_jump_parameter_copies_witness (X : ExtSem) :
    ∃ result, ∃ (spec : Control.JumpBodySpec function result function.blocks[0]! 0 0 ⟨10,[1,6]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ initial t left ρ w fr' ρ',
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,0⟩,⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      left+2 = 6 ∧ Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [⟨.i64,0⟩] Clif.Mem.empty ∧
      t.frame.body = [] ∧ t.frame.term = .jump ⟨10,[1,6]⟩ ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ w [] w (.goto 0)) ∧
      Clif.enterBlock t.frame ⟨10,[1,6]⟩ = .ok fr' ∧
      edgeEnvAt result.code result.edgeArgs 0 spec.target 0 ρ = some ρ' ∧
      ValuesHeld (fun x => x ∈ ([2,3] : List Nat)) result.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨result,spec,t,left,ρ,w,run,scope,dominated,entered,total,continued,empty,jump,executed,post⟩ :=
    executable_jump_return_witness X
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (by with_unfolding_all rfl))
  have targetValue : spec.target = 1 := by
    have labels := spec.targets
    rw [order] at labels
    exact (List.cons.inj labels).1.symm
  have target : result.order.nodes[spec.target]? = some (.original 1) := by
    rw [order,targetValue]
    rfl
  have crossing : ∃ fr',Clif.enterBlock t.frame ⟨10,[1,6]⟩ = .ok fr' := by
    cases call : Clif.enterBlock t.frame ⟨10,[1,6]⟩ with
    | ok fr' => exact ⟨fr',rfl⟩
    | trap code =>
      have leftEq : left = 4 := by omega
      rw [leftEq,Clif.runLoop_succ] at continued
      simp only [Clif.step,empty,jump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
      cases continued
    | stuck message =>
      have leftEq : left = 4 := by omega
      rw [leftEq,Clif.runLoop_succ] at continued
      simp only [Clif.step,empty,jump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
      cases continued
  obtain ⟨fr',crossed⟩ := crossing
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨ρ',copied,parameters⟩ := Control.stock_jump_body_direct_parameter_values run scope dominated
    spec tag rfl target rfl (targetBlock := function.blocks[1]!) rfl crossed post
  exact ⟨result,spec,_,t,left,ρ,w,fr',ρ',run,scope,dominated,entered,total,continued,empty,jump,
    executed,crossed,copied,parameters⟩

end Backend.Stock.Proof.ControlWitness

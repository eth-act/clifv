import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockConditionalBodyRefines
import FV.Backend.Proof.StockConditionalCallsWitness
import FV.Backend.Proof.StockEntrySeed
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.ConditionalValues.BodyWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private abbrev function := ConditionalCalls.sourceFunction
private def zero : Clif.Val := ⟨.i64,0⟩
private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 zero,slots := [],
  body := [],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ }
private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  intro b member stm present
  simp only [function,ConditionalCalls.sourceFunction,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> cases present

/-- An executable original conditional source and entered machine seed inhabit
the retained body contract. Its real source continuation returns through the
false successor, with exact fuel and the guarded terminator post-frame. -/
theorem executable_conditional_body_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ t left ρ' w',
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [zero] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      left+function.blocks[0]!.body.length = 2 ∧
      Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [zero] Clif.Mem.empty ∧
      t.frame.body = [] ∧ t.frame.term = .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default = some (.fall ρ' w') ∧
      GuardedScanRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
        spec.term.output.state (function.blocks[0]!.body.length,t.frame,t.mem) ρ' w' := by
  obtain ⟨result,out,next,trace,run,scope,dominated,_⟩ := ConditionalCalls.source_calls_fixture_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag
    (b := function.blocks[0]!) rfl (c := 7) (yes := ⟨1,[7]⟩) (no := ⟨2,[7]⟩) rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  have entered : Clif.enterFunc function [zero] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [zero] Clif.Mem.empty := rfl
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  obtain ⟨t,left,ρ',w',total,continued,empty,frameEq,term,executed,post⟩ :=
    spec.returns 2 ⟨initial,[],Clif.Mem.empty⟩ [zero] Clif.Mem.empty rfl rfl returned
      (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default held
  exact ⟨result,spec,t,left,ρ',w',run,scope,dominated,entered,total,continued,empty,term,executed,post⟩

end Backend.Stock.Proof.ConditionalValues.BodyWitness

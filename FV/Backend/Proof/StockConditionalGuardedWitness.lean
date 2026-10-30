import FV.Backend.Proof.StockTermAvailability
import FV.Backend.Proof.StockConditionalGuardedValues
import FV.Backend.Proof.StockConditionalCallsWitness
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.ConditionalValues.GuardedWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := ConditionalCalls.sourceFunction
private def initial (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,word⟩,slots := [],
  body := [],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ }
private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  intro b member stm present
  simp only [function,ConditionalCalls.sourceFunction,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> cases present
private theorem empty_state {exec : Nat → State → Except String Scan}
    {before : State} {body : BlockScan} (scanned : ScansSpec exec [] before body) : body.state = before := by
  cases scanned
  rfl
private theorem source_return (word : BitVec 64) :
    Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial word,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,word⟩] Clif.Mem.empty := by
  cases choice : Clif.Sem.truthy (⟨.i64,word⟩ : Clif.Val).bits
  all_goals
    dsimp [Clif.runLoop,Clif.step,Clif.stepTerm,initial,Clif.Frame.get,
      Clif.Res.ofOption,Clif.StepResult.ofRes,Clif.Regs.set,Clif.Regs.empty]
    rw [choice]
    rfl

/-- For every64-bit input, the complete original source enters and returns on
its chosen edge. Its actual retained branch executes under csem using the real
final alias table, with the source-derived entry seed and guarded post-frame.
No selected-rule, helper-code, value, alias-bound or machine-run input is given. -/
theorem executable_parameter_branch_witness (X : ExtSem) (word : BitVec 64) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ index inst ops regs prefixWorld endWorld,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial word,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,word⟩] Clif.Mem.empty ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.origin.emission.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx (initial word)) Arm.ArmState.default =
          some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if word != 0 then 0 else 1))) ∧
      GuardedScanRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
        spec.term.output.state (0,initial word,Clif.Mem.empty) regs endWorld ∧
      inst.targets = result.order.successors[0]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨result,out,next,trace,run,scope,dominated,_⟩ := ConditionalCalls.source_calls_fixture_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag
    (b := function.blocks[0]!) rfl (c := 7) (yes := ⟨1,[7]⟩) (no := ⟨2,[7]⟩) rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  let built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx function = .ok built := rfl
  have same := Except.ok.inj (spec.build.symm.trans build)
  have context : result.ctx = built.1 := congrArg Prod.fst same
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have entered : Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) := rfl
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  have bodyState : spec.body.state = spec.term.output.state := empty_state (by
    change ScansSpec _ [] _ _
    exact spec.split.scanned)
  have states := bodyState.symm.trans spec.split.state
  have post : GuardedScanRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
      spec.term.output.state (0,initial word,Clif.Mem.empty)
      (entrySeed spec.core.scan.ctx (initial word)) Arm.ArmState.default := by
    simpa only [states] using held
  have available : 7 ∈ availOf function (availIn function result.ctx) spec.core.scan.block 0 := by
    rw [spec.atBlock]
    exact buildCtx_term_available spec.build dominated (b := function.blocks[0]!) rfl 7
      (by simp [abiTerm,Backend.Proof.Driver.termArgs,function,ConditionalCalls.sourceFunction])
  have getC : (restrict (initial word) (availOf function (availIn function result.ctx)
      spec.core.scan.block 0)).getAs 7 .i64 = .ok word := by
    exact (getAs_congr (fr := initial word) (x := 7) (ty := .i64) (restrict_regs_of_mem available)).trans rfl
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,guarded,targets,terminal⟩ :=
    spec.parameter_branch_values run scope (refines_csem (fun _ => False) ⟨0,0⟩ X) stable
      rfl rfl parameter getC (Or.inr rfl) post
  exact ⟨result,spec,index,inst,ops,regs,prefixWorld,endWorld,run,scope,dominated,entered,
    source_return word,machine,guarded,targets,terminal⟩

end Backend.Stock.Proof.ConditionalValues.GuardedWitness

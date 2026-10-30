import FV.Backend.Proof.StockConditionalTrapFixture
import FV.Backend.Proof.StockConditionalSourceTrap
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.ConditionalValues.TrapWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private abbrev function := TrapFixture.function
private abbrev initial := TrapFixture.initial 0
private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  intro b member stm present
  simp only [function,TrapFixture.function,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> cases present
private theorem empty_steps {S : Type} {step : Nat → S → S → Prop} {before next : S}
    (steps : SourceSteps step [] before next) : before = next := by cases steps; rfl

/-- A complete original source has a reachable trapping successor. Actual
source entry/trapping and the whole retained core inhabit the first-body-trap
or later-selected-trap contract under csem and the real final alias table. -/
theorem trapping_parameter_core_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ = .trapped (.user 9) ∧
      (TrapRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default (.user 9) ∨
       ∃ index inst ops regs prefixWorld endWorld,
        index+1 = spec.origin.emission.code.size ∧
        seqRun (csem (fun _ => False) ⟨0,0⟩ X)
          (spec.core.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
          (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
            some (.stop (spec.body.code.size+index) inst ops regs prefixWorld [] endWorld (.goto 1)) ∧
        GuardedScanRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
          spec.term.output.state (0,initial,Clif.Mem.empty) regs endWorld ∧
        inst.targets = result.order.successors[0]!.toList ∧ inst.isTerminator = true) := by
  obtain ⟨result,run,scope,dominated,entered,trapped⟩ := TrapFixture.driver_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag
    (b := function.blocks[0]!) rfl (c := 7) (yes := ⟨1,[7]⟩) (no := ⟨2,[7]⟩) rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  let built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have conditionTy : result.ctx.valueType? 7 = some (.int 32) ∨ result.ctx.valueType? 7 = some (.int 64) := by
    right
    rw [context]
    rfl
  have entered : Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have trapped : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ = .trapped (.user 9) := rfl
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  have defined : SourceDefinedAt function result.ctx spec.core.scan.block 0 initial := by
    rw [spec.atBlock]
    exact source_defined_enterFunc dominated result.ctx entered
  have execution := spec.trapping_parameter_core run scope dominated family
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable rfl parameter conditionTy rfl rfl defined trapped held
  refine ⟨result,spec,run,scope,dominated,entered,trapped,?_⟩
  rcases execution with failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,guarded,targets,terminal⟩
  · exact Or.inl failed
  · right
    have sourceEq : (0,initial,Clif.Mem.empty) = (0,t.frame,t.mem) := by
      change SourceSteps _ [] (0,initial,Clif.Mem.empty) (0,t.frame,t.mem) at steps
      exact empty_steps steps
    have frameEq : t.frame = initial := (congrArg (fun p => p.2.1) sourceEq).symm
    have memEq : t.mem = Clif.Mem.empty := (congrArg (fun p => p.2.2) sourceEq).symm
    have valueEq : value = ⟨.i64,0⟩ := by
      rw [frameEq] at read
      change Clif.Res.ok (⟨.i64,0⟩ : Clif.Val) = .ok value at read
      exact (Clif.Res.ok.inj read).symm
    rw [valueEq] at machine
    rw [frameEq,memEq] at guarded
    exact ⟨index,inst,ops,regs,prefixWorld,endWorld,last,machine,guarded,targets,terminal⟩

end Backend.Stock.Proof.ConditionalValues.TrapWitness

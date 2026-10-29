module

public import FV.Backend.Proof.StockConditionalSourceReturn
public import FV.Backend.Proof.StockConditionalGuardedWitness

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues.ReturnWitness
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

private theorem empty_steps {S : Type} {step : Nat → S → S → Prop} {before next : S}
    (steps : SourceSteps step [] before next) : before = next := by
  cases steps
  rfl

/-- A complete source enters and returns for every64-bit input; its entire
retained core executes the correct source branch and stops at the real final
instruction under csem/result.final.alias, with the real entry seed. -/
theorem returning_parameter_core_witness (X : ExtSem) (word : BitVec 64) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ index inst ops regs prefixWorld endWorld,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial word,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,word⟩] Clif.Mem.empty ∧
      index+1 = spec.origin.emission.code.size ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx (initial word)) Arm.ArmState.default =
          some (.stop (spec.body.code.size+index) inst ops regs prefixWorld [] endWorld
            (.goto (if Clif.Sem.truthy (⟨.i64,word⟩ : Clif.Val).bits then 0 else 1))) ∧
      GuardedScanRel function result spec.core.scan.ctx spec.core.scan.block (fun _ _ _ => True)
        spec.term.output.state (0,initial word,Clif.Mem.empty) regs endWorld ∧
      inst.targets = result.order.successors[0]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨result,spec,oldIndex,oldInst,oldOps,oldRegs,oldPrefix,oldWorld,
    run,scope,dominated,entered,returned,oldMachine,oldGuarded,oldTargets,oldTerminal⟩ :=
    GuardedWitness.executable_parameter_branch_witness X word
  change Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) at entered
  change Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial word,[],Clif.Mem.empty⟩ =
    .returned [⟨.i64,word⟩] Clif.Mem.empty at returned
  let built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have conditionTy : result.ctx.valueType? 7 = some (.int 32) ∨ result.ctx.valueType? 7 = some (.int 64) := by
    right
    rw [context]
    rfl
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  have defined : SourceDefinedAt function result.ctx spec.core.scan.block 0 (initial word) := by
    rw [spec.atBlock]
    exact source_defined_enterFunc dominated result.ctx entered
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,
    read,crossed,nextReturned,tDefined,last,machine,guarded,targets,terminal⟩ :=
    spec.returning_parameter_core run scope dominated family
      (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
      stable rfl parameter conditionTy rfl rfl defined returned held
  have sourceEq : (0,initial word,Clif.Mem.empty) = (0,t.frame,t.mem) := by
    change SourceSteps _ [] (0,initial word,Clif.Mem.empty) (0,t.frame,t.mem) at steps
    exact empty_steps steps
  have frameEq : t.frame = initial word := (congrArg (fun p => p.2.1) sourceEq).symm
  have memEq : t.mem = Clif.Mem.empty := (congrArg (fun p => p.2.2) sourceEq).symm
  have valueEq : value = ⟨.i64,word⟩ := by
    rw [frameEq] at read
    change Clif.Res.ok (⟨.i64,word⟩ : Clif.Val) = .ok value at read
    exact (Clif.Res.ok.inj read).symm
  rw [valueEq] at machine
  rw [frameEq,memEq] at guarded
  exact ⟨result,spec,index,inst,ops,regs,prefixWorld,endWorld,run,scope,dominated,entered,returned,
    last,machine,guarded,targets,terminal⟩

end Backend.Stock.Proof.ConditionalValues.ReturnWitness

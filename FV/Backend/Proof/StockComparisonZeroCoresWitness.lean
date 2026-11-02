import FV.Backend.Proof.StockComparisonZeroCores
import FV.Backend.Proof.StockComparisonZeroFactsWitness
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.ConditionalValues.ComparisonZeroCoreWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := ComparisonBranch.ZeroWitness.function

/-- The entered frame of `block0(v0)` for the input `v0 = 0`. -/
private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,0⟩,slots := [],
  body := [⟨[1],.iconst .i64 0⟩,⟨[2],.icmp .eq .i64 0 1⟩],term := .brif 2 ⟨1,[0]⟩ ⟨2,[0]⟩ }

private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  intro b member stm present
  simp only [function,ComparisonBranch.ZeroWitness.function,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    · simp [MaskBody.Family,HighMulBody.Family,CmpBody.Family,MinMaxBody.Family,PopcountBody.Family,
        BitBody.Family,CastBody.Family,ShiftBody.Family,MulBody.Family,BnotBody.Family,ConstantBody.Family]
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨.eq,.i64,0,1,rfl⟩)))
  all_goals cases present

-- witness: native_decide (dominatedB of the fixed fixture, as in the other Stock fixtures)
private theorem dominated : Dominated function := dominated_of (by native_decide)

private theorem entered :
    Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl

private theorem returned :
    Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,0⟩] Clif.Mem.empty := rfl

/-- The complete source `v1 = iconst.i64 0; v2 = icmp eq v0, v1;
brif v2, block1(v0), block2(v0)` enters and returns for the input 0. Its actual
entry body spec and entered frame instantiate `returning_comparison_zero_core`:
the retained core runs the body and the real one-instruction branch
(`cbz v0`), and stops at it on the source-chosen edge. -/
theorem returning_comparison_zero_core_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 2
      ⟨1,[0]⟩ ⟨2,[0]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ (t : Clif.State) (left : Nat) (value : Clif.Val) (fr : Clif.Frame),
      ∃ index inst ops regs prefixWorld endWorld,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,0⟩] Clif.Mem.empty ∧
      t.frame.get 2 = .ok value ∧
      Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then ⟨1,[0]⟩ else ⟨2,[0]⟩) = .ok fr ∧
      Clif.runLoop Clif.Env.empty {funcs := []} left {t with frame := fr} =
        .returned [⟨.i64,0⟩] Clif.Mem.empty ∧
      spec.origin.emission.code.size = 1 ∧ index+1 = spec.origin.emission.code.size ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.core.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
          some (.stop (spec.body.code.size+index) inst ops regs prefixWorld [] endWorld
            (.goto (if Clif.Sem.truthy value.bits then 0 else 1))) ∧
      inst.targets = result.order.successors[0]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨result,_,_,_,run,scope,_⟩ := ComparisonBranch.ZeroWitness.comparison_zero_calls_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag
    (b := function.blocks[0]!) rfl (c := 2) (yes := ⟨1,[0]⟩) (no := ⟨2,[0]⟩) rfl
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable Clif.Env.empty {funcs := []}
  let built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have origin : result.ctx.defClif? 2 = some (.icmp .eq .i64 0 1) := by rw [context]; rfl
  have typeX : result.ctx.valueType? 0 = some (.int (if true then 64 else 32)) := by rw [context]; rfl
  have parameterX : result.ctx.defInst? 0 = none := by rw [context]; rfl
  have constY : result.ctx.defClif? 1 = some (.iconst .i64 0) := by rw [context]; rfl
  have equality : Clif.IntCC.eq = .eq ∨ Clif.IntCC.eq = .ne := Or.inl rfl
  have zero : (0 : BitVec Clif.Ty.i64.width) = 0 := rfl
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  have defined : SourceDefinedAt function result.ctx spec.core.scan.block 0 initial := by
    rw [spec.atBlock]
    exact source_defined_enterFunc dominated result.ctx entered
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,_,_,_,_,
    read,crossed,nextReturned,_,last,machine,_,targets,terminal⟩ :=
    spec.returning_comparison_zero_core run scope dominated family
      (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
      stable rfl origin true typeX parameterX constY equality zero rfl rfl defined returned held
  have size := spec.comparison_zero_emission_size run scope rfl rfl origin true typeX parameterX constY equality zero
  exact ⟨result,spec,t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,run,scope,dominated,
    entered,returned,read,crossed,nextReturned,size,last,machine,targets,terminal⟩

end Backend.Stock.Proof.ConditionalValues.ComparisonZeroCoreWitness

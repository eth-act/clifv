import FV.Backend.Proof.StockConditionalArgsAt
import FV.Backend.Proof.StockConditionalLeaf
import FV.Backend.Proof.StockConditionalGuardedWitness
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.Proof.ConditionalValues.ArgsAtWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := ConditionalCalls.sourceFunction
private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have checked : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp checked b member) stm present)

private theorem terminal_successor {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (X : ExtSem) {vals : List Clif.Val} {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block}
    {xs : List Nat}
    (lookup : blockIdx? function bc.block = some tl) (found : function.block? bc.block = some b)
    (source : function.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (ret : b.term = .ret xs) (nonentry : tl ≠ 0) (forward : 0 < targetLabel) :
    Nonempty (SuccessorReturn function result 0 bc (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []} vals Clif.Mem.empty) := by
  have abi : sigAbiOk function.sig = true := rfl
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  exact SuccessorReturn.of_return_block run scope dominated abi family
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    stable lookup found source tag ret nonentry forward

/-- Both successors of a real conditional receive the entry parameter as a block argument
and return it. From the actual entry seed, the per-successor composition reaches the source
return through the actual selected copy of the nonempty vector. -/
theorem returning_original_parameter_at_witness (X : ExtSem) (word : BitVec 64) :
    ∃ result,∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ fr : Clif.Frame,Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (fr,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,word⟩] Clif.Mem.empty ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) fr.slots
        ⟨0,spec.preludeCode.size,entrySeed spec.core.scan.ctx fr,Arm.ArmState.default⟩
        (.returned [⟨.i64,word⟩] Clif.Mem.empty) := by
  obtain ⟨result,spec,_,_,_,_,_,_,run,scope,dominated,entered,returned,_,_,_,_⟩ :=
    GuardedWitness.executable_parameter_branch_witness X word
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  let built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have conditionTy : result.ctx.valueType? 7 = some (.int 32) ∨ result.ctx.valueType? 7 = some (.int 64) := by
    right
    rw [context]
    rfl
  have ordered : blockOrder function =
      .ok ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ := by cbv
  have orderEq := Except.ok.inj ((stock_lower_order run).symm.trans ordered)
  have successorLabels : result.order.successors[0]! = #[2,1] := by rw [orderEq]; rfl
  have firstTag : result.order.nodes[2]? = some (.original 1) := by rw [orderEq]; rfl
  have secondTag : result.order.nodes[1]? = some (.original 2) := by rw [orderEq]; rfl
  have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests function.blocks[0]!.term)[index]? = some bc →
      Nonempty (SuccessorReturn function result 0 bc (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) Clif.Env.empty {funcs := []} [⟨.i64,word⟩] Clif.Mem.empty) := by
    intro index bc selected
    cases index with
    | zero =>
      change some ⟨1,[7]⟩ = some bc at selected
      cases Option.some.inj selected
      exact terminal_successor run scope dominated X (tl := 1) (targetLabel := 2)
        (b := function.blocks[1]!) rfl rfl rfl firstTag rfl (by decide) (by decide)
    | succ index =>
      cases index with
      | zero =>
        change some ⟨2,[7]⟩ = some bc at selected
        cases Option.some.inj selected
        exact terminal_successor run scope dominated X (tl := 2) (targetLabel := 1)
          (b := function.blocks[2]!) rfl rfl rfl secondTag rfl (by decide) (by decide)
      | succ index => cases selected
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  exact ⟨result,spec,_,run,entered,returned,
    spec.returning_original_parameter_at run scope dominated family
      (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
      stable tag rfl parameter conditionTy successorLabels firstTag secondTag successors
      rfl rfl rfl (by rw [spec.atBlock]; exact source_defined_enterFunc dominated result.ctx entered)
      returned held⟩

end Backend.Stock.Proof.ConditionalValues.ArgsAtWitness

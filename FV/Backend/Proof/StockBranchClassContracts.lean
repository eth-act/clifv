import FV.Backend.Proof.StockScanClassContracts
import FV.Backend.Proof.StockCoreFormContracts

namespace Backend.Stock.Proof.BranchClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.OperandClassDraft Backend.Stock.Proof.ClassGrowthDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem branchCode_classes {f : Clif.Function} {t : Clif.Terminator} {targets : Array Nat}
    {input output : Array MInst} {classes : Array RegClass}
    (original : ∀ i ∈ input.toList,RegsFrom (RegCls classes) i)
    (run : branchCode f t targets input = .ok output) :
    ∀ i ∈ output.toList,RegsFrom (RegCls classes) i := by
  unfold branchCode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    first
      | exact original
      | (intro i member
         simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
         rcases member with old | rfl
         · exact original i (List.dropLast_subset _ (by simpa only [Array.toList_pop] using old))
         · have last := original _ (by simpa using (Array.mem_of_back? (by assumption)))
           intro g keeps
           have fixed := last g keeps
           simp only [MInst.mapRegs,MInst.call.injEq] at fixed
           simpa only [MInst.mapRegs] using congrArg (fun c => MInst.tryCall c _) fixed)

/-- Actual branch emission derives all operand classes, including replacement
of the final actual call by the exception-table terminator. -/
theorem stock_emitBranch_classes {f : Clif.Function} {ctx : Ctx}
    (clean : Clean ctx) {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat}
    {input : State} (invariant : ClsIs ctx input.base input.base) {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    ClassGrowth input output.state ∧ ClsIs ctx output.state.base output.state.base ∧
      ∀ i ∈ output.code.toList,RegsFrom (RegCls output.state.base.classes) i ∧
        InstCls output.state.base.classes i := by
  unfold emitBranch at run
  dsimp only at run
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  change ((do
    let (out,next,fired) ← Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next,code,⟨bi,ti,.emitted,before,next,[],fired,code⟩,fired⟩) :
      Except String BranchEmission) = .ok output at run
  have beforeClasses : ClsIs ctx before.base before.base :=
    ⟨invariant.sz,invariant.vals,invariant.try1,invariant.try2,⟨[],by simp,by simp⟩⟩
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before with
  | error e => simp only [root,bind,Except.bind] at run; cases run
  | ok answer =>
    rcases answer with ⟨out,next,fired⟩
    simp only [root,bind,Except.bind] at run
    split at run
    · cases run
    · cases call : branchCode f t targets next.base.emitted with
      | error e => simp only [call] at run; cases run
      | ok code =>
        simp only [call,pure,Except.pure] at run
        cases run
        have classed := stock_branch_classes clean root beforeClasses
        have growth := stock_named_classGrowth root
        obtain ⟨fragment,emitted,covered⟩ := classed.emitted
        have original : ∀ i ∈ next.base.emitted.toList,RegsFrom (RegCls next.base.classes) i := by
          rw [emitted]
          simpa only [before,Array.empty_append,List.toList_toArray] using covered
        refine ⟨growth,⟨classed.sz,classed.vals,classed.try1,classed.try2,⟨[],by simp,by simp⟩⟩,?_⟩
        intro i member
        have raw := branchCode_classes original call i member
        exact ⟨raw,instCls_of raw⟩
end Backend.Stock.Proof.BranchClassDraft

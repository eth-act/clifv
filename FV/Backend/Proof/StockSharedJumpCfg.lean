import FV.Backend.Proof.StockJumpCfg
import FV.Backend.Proof.StockSharedSource
import FV.Backend.Proof.StockCriticalCode

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem singleton_selected {ss : Array Nat} {j target chosen : Nat}
    (same : ss = #[chosen]) (edge : ss[j]? = some target) : j = 0 ∧ chosen = target := by
  subst ss
  have bound : j < 1 := (Array.getElem?_eq_some_iff.mp edge).1
  have zero : j = 0 := by omega
  subst j
  exact ⟨rfl,Option.some.inj edge⟩

/-- Every actual Stock predecessor of a shared graph target ends in the exact
operandless jump to that target. Source-kind classification, original jump
selection/assembly/aliasing and critical-node code are derived internally;
no supplied jump, target-kind or source-node certificate is required. -/
theorem stock_lower_shared_jump_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {targetLabel b j b₂ j₂ : Nat} {ss ss₂ : Array Nat}
    (row : result.order.successors[b]? = some ss) (edge : ss[j]? = some targetLabel)
    (otherRow : result.order.successors[b₂]? = some ss₂) (otherEdge : ss₂[j₂]? = some targetLabel)
    (distinct : b ≠ b₂ ∨ j ≠ j₂) :
    ∃ block,result.code.blocks[b]? = some block ∧ block.insts.back? = some (.jump targetLabel) ∧
      result.order.successors[b]? = some #[targetLabel] ∧ j = 0 := by
  obtain ⟨target,targetNode,kind⟩ := stock_lower_shared_source_kind run scope row edge otherRow otherEdge distinct
  rcases kind with ⟨bi,sourceBlock,dest,sourceNode,atSource,jump⟩ | ⟨bi,k,sourceNode⟩
  · obtain ⟨chosen,block,placed,back,singleton⟩ := stock_lower_original_jump_cfg run scope sourceNode atSource jump
    obtain ⟨zero,same⟩ := singleton_selected (Option.some.inj (row.symm.trans singleton)) edge
    subst chosen
    exact ⟨block,placed,back,singleton,zero⟩
  · obtain ⟨input,next,args,chosen,call,singleton,chosenNode,placed⟩ := stock_lower_critical_code run sourceNode
    obtain ⟨zero,same⟩ := singleton_selected (Option.some.inj (row.symm.trans singleton)) edge
    subst chosen
    exact ⟨_,placed,rfl,singleton,zero⟩

end Backend.Stock.Proof

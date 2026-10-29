module

public import FV.Backend.Proof.StockCriticalCode
public import FV.Backend.Proof.StockEdgeValuesWitness
public import FV.Backend.Proof.StockTerminalDriverWitness

@[expose] public section

namespace Backend.Stock.Proof.OrderGraphWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- A complete existing critical-edge driver inhabits the general successor
classification with actual original and synthetic nodes. -/
theorem stock_critical_order_witness :
    ∃ (f : Clif.Function) (result : Result) (label pred k target targetLabel : Nat),
      Stock.lower f = .ok result ∧ LowerScope f ∧
      result.order.nodes[label]? = some (.edge pred k target) ∧
      result.order.successors[label]? = some #[targetLabel] ∧
      result.order.nodes[targetLabel]? = some (.original target) := by
  obtain ⟨f,result,run,scope,_,_,⟨pred,k,target,member⟩,_⟩ :=
    TerminalDriverWitness.stock_critical_driver_unsunk_witness
  obtain ⟨label,tag⟩ := List.getElem?_of_mem member
  have node : result.order.nodes[label]? = some (.edge pred k target) := by simpa using tag
  obtain ⟨targetLabel,successors,original⟩ := stock_lower_edge_successor run node
  exact ⟨f,result,label,pred,k,target,targetLabel,run,scope,node,successors,original⟩
/-- The complete nonempty alias/copy source witness also inhabits actual
whole-driver jump successor classification; no CFG premise is supplied. -/
theorem stock_jump_order_witness : ∃ (f : Clif.Function) (result : Result),
    Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
    result.order.nodes[0]? = some (.original 0) ∧
    ∃ target targetLabel,f.blocks.findIdx? (·.id == 1) = some target ∧ target ≠ 0 ∧
      result.order.successors[0]? = some #[targetLabel] ∧
      (result.order.nodes[targetLabel]? = some (.original target) ∨
       result.order.nodes[targetLabel]? = some (.edge 0 0 target)) := by
  obtain ⟨result,run,scope,dominated,_⟩ := EdgeValuesWitness.stock_jump_edge_env_witness 0
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (by cbv))
  have tag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
  exact ⟨_,result,run,scope,dominated,tag,
    stock_lower_jump_nonentry_successor run scope tag (bi := 0) (bc := ⟨1,[17]⟩) (by rfl) (by rfl)⟩
/-- A complete actual driver with synthetic edges inhabits the exact
returned jump/argument block and its derived original target. -/
theorem stock_critical_code_witness :
    ∃ (f : Clif.Function) (result : Result) (label pred k target : Nat)
      (input next : State) (args : Array Reg) (targetLabel : Nat),
      Stock.lower f = .ok result ∧ LowerScope f ∧
      result.order.nodes[label]? = some (.edge pred k target) ∧
      branchArgs result.ctx input pred k = .ok (args,next) ∧
      result.order.successors[label]? = some #[targetLabel] ∧
      result.order.nodes[targetLabel]? = some (.original target) ∧
      result.code.blocks[label]? = some {label,insts := #[.jump targetLabel],branchArgs := args.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} := by
  obtain ⟨f,result,label,pred,k,target,targetLabel,run,scope,node,_,_⟩ := stock_critical_order_witness
  obtain ⟨input,next,args,targetLabel,call,successors,targetTag,placed⟩ := stock_lower_critical_code run node
  exact ⟨f,result,label,pred,k,target,input,next,args,targetLabel,run,scope,node,call,successors,targetTag,placed⟩
end Backend.Stock.Proof.OrderGraphWitness

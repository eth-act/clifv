import FV.Backend.Proof.StockSelectedGraph
import FV.Backend.Proof.StockCriticalValuesWitness
namespace Backend.Stock.Proof.SelectedGraphWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- The complete real conditional/critical-edge driver inhabits general
selected-successor classification for either original source successor. -/
theorem stock_selected_graph_witness (word : BitVec 64) (index : Nat) (bound : index < 2)
    (world : Arm.ArmState) : ∃ (f : Clif.Function) (result : Result),
    Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
    result.order.nodes[0]? = some (.original 0) ∧
    ∃ target targetLabel,blockIdx? f 1 = some target ∧ target ≠ 0 ∧
      result.order.successors[0]![index]? = some targetLabel ∧
      (result.order.nodes[targetLabel]? = some (.original target) ∨
       result.order.nodes[targetLabel]? = some (.edge 0 index target)) := by
  obtain ⟨result,run,scope,dominated,_⟩ := CriticalValuesWitness.stock_critical_edge_env_witness word index bound world
  have order : result.order =
      ⟨#[.original 0,.edge 0 0 1,.edge 0 1 1,.original 1],#[#[1,2],#[3],#[3],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (by cbv))
  have tag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
  have cases : index = 0 ∨ index = 1 := by omega
  exact ⟨_,result,run,scope,dominated,tag,
    stock_lower_selected_successor run scope tag (bi := 0) (bc := ⟨1,[17]⟩) (by rfl)
      (by rcases cases with rfl | rfl <;> rfl)⟩
end Backend.Stock.Proof.SelectedGraphWitness

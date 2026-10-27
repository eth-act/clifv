import FV.Backend.Proof.StockCfgTraversalScans
import FV.Backend.Proof.StockLinearCfgFixture
import FV.Backend.Proof.StockTerminalDriverWitness

namespace Backend.Stock.Proof.CfgTraceWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A real complete three-block compiler run inhabits generic scan order,
uniqueness and adjacent-state coupling with a nonempty traversal suffix. -/
theorem actual_chain_scan_witness :
    ∃ (result : Result) (ranges : Array (Nat × Nat)) (input : State)
      (first second : LoweredBlockCore) (firstData secondData : Backend.V),
      Stock.lower LinearCfgWitness.function = .ok result ∧ LowerScope LinearCfgWitness.function ∧
      result.blockScans.toList.map (·.block) = [2,1,0] ∧
      (result.blockScans.toList.map (·.block)).Nodup ∧
      Stock.buildCtx LinearCfgWitness.function = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order LinearCfgWitness.function LinearCfgWitness.function.blocks[2]!
        2 ranges[2]!.1 ranges[2]!.2 firstData result.order.successors[2]! input = .ok first ∧
      lowerBlockCore result.ctx result.order LinearCfgWitness.function LinearCfgWitness.function.blocks[1]!
        1 ranges[1]!.1 ranges[1]!.2 secondData result.order.successors[1]! first.state = .ok second ∧
      first.scan ∈ result.blockScans.toList ∧ second.scan ∈ result.blockScans.toList ∧
      (∀ a ∈ result.blockScans.toList,∀ b ∈ result.blockScans.toList,a.block = b.block → a = b) := by
  obtain ⟨result,run,scope,dominated,order⟩ := LinearCfgWitness.actual_linear_driver_witness
  have labels : (Array.range result.order.nodes.size).reverse.toList = ([] : List Nat) ++ 2 :: 1 :: [0] := by
    rw [order]; decide +kernel
  obtain ⟨ranges,input,first,second,fd,sd,build,fr,sr,fm,sm⟩ := CfgTrace.actual_adjacent_original_cores run labels
    (by simp [order] : result.order.nodes[2]! = .original 2)
    (by simp [order] : result.order.nodes[1]! = .original 1)
  have sequence : result.blockScans.toList.map (·.block) = [2,1,0] := by
    rw [CfgTrace.actual_scan_blocks run,order]
    decide +kernel
  exact ⟨result,ranges,input,first,second,fd,sd,run,scope,sequence,CfgTrace.actual_scan_blocks_nodup run scope,
    build,fr,sr,fm,sm,fun a am b bm same => CfgTrace.actual_scan_unique run scope am bm same⟩

/-- Nonempty intervening compilation is witnessed by the real middle block,
with both endpoint cores and their exact shared traversal states retained. -/
theorem actual_intervening_scan_witness :
    ∃ (result : Result) (ranges : Array (Nat × Nat)) (params : List Nat) (input : State)
      (afterFirst beforeSecond : DriverState) (first second : LoweredBlockCore)
      (firstData secondData : Backend.V),
      Stock.lower LinearCfgWitness.function = .ok result ∧ LowerScope LinearCfgWitness.function ∧
      Stock.buildCtx LinearCfgWitness.function = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order LinearCfgWitness.function LinearCfgWitness.function.blocks[2]!
        2 ranges[2]!.1 ranges[2]!.2 firstData result.order.successors[2]! input = .ok first ∧
      lowerBlockCore result.ctx result.order LinearCfgWitness.function LinearCfgWitness.function.blocks[0]!
        0 ranges[0]!.1 ranges[0]!.2 secondData result.order.successors[0]! beforeSecond.state = .ok second ∧
      afterFirst.state = first.state ∧
      ([1] : List Nat).foldlM (fun d k => lowerNode result.ctx ranges result.order LinearCfgWitness.function params k d)
        afterFirst = .ok beforeSecond ∧
      first.scan ∈ result.blockScans.toList ∧ second.scan ∈ result.blockScans.toList := by
  obtain ⟨result,run,scope,dominated,order⟩ := LinearCfgWitness.actual_linear_driver_witness
  have labels : (Array.range result.order.nodes.size).reverse.toList =
      ([] : List Nat) ++ 2 :: ([1] ++ 0 :: []) := by rw [order]; decide +kernel
  obtain ⟨ranges,params,input,afterFirst,beforeSecond,first,second,fd,sd,build,fr,sr,state,gap,fm,sm⟩ :=
    CfgTrace.actual_ordered_original_cores run labels
      (by simp [order] : result.order.nodes[2]! = .original 2)
      (by simp [order] : result.order.nodes[0]! = .original 0)
  exact ⟨result,ranges,params,input,afterFirst,beforeSecond,first,second,fd,sd,
    run,scope,build,fr,sr,state,gap,fm,sm⟩

/-- Actual synthetic edge transitions coexist with original scans in a real
four-node driver run, while the generic retained source projection is unique. -/
theorem actual_critical_scan_witness : ∃ (f : Clif.Function) (result : Result),
    Stock.lower f = .ok result ∧ LowerScope f ∧ f.blocks.length = 2 ∧ result.order.nodes.size = 4 ∧
    (∃ pred k target,.edge pred k target ∈ result.order.nodes.toList) ∧
    result.blockScans.toList.map (·.block) = (stockOriginals result.order.nodes).reverse ∧
    (result.blockScans.toList.map (·.block)).Nodup ∧
    (∀ a ∈ result.blockScans.toList,∀ b ∈ result.blockScans.toList,a.block = b.block → a = b) := by
  obtain ⟨f,result,run,scope,blocks,nodes,edge,terminal,records⟩ :=
    TerminalDriverWitness.stock_critical_driver_unsunk_witness
  exact ⟨f,result,run,scope,blocks,nodes,edge,CfgTrace.actual_source_scan_order run,
    CfgTrace.actual_scan_blocks_nodup run scope,
    fun a am b bm same => CfgTrace.actual_scan_unique run scope am bm same⟩

end Backend.Stock.Proof.CfgTraceWitness

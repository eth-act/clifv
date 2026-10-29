module

public import FV.Backend.Proof.StockCfgTraversalDemand
public import FV.Backend.Proof.StockCfgTraversalScansWitness

@[expose] public section

namespace Backend.Stock.Proof.CfgDemandWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The real three-block compiler carries successor demand through the nonempty
middle-block traversal to the entry terminator, with its actual retained split. -/
theorem nonempty_gap_demand_witness :
    ∃ (result : Result) (first second : BlockScanEvent) (b : Clif.Block)
      (term : ScanRecord) (body : BlockScan),
      Stock.lower LinearCfgWitness.function = .ok result ∧ LowerScope LinearCfgWitness.function ∧
      (Array.range result.order.nodes.size).reverse.toList = ([] : List Nat) ++ 2 :: ([1] ++ 0 :: []) ∧
      first.block = 2 ∧ second.block = 0 ∧ first ∈ result.blockScans.toList ∧ second ∈ result.blockScans.toList ∧
      SourceBodySplit LinearCfgWitness.function second b term body ∧
      (∀ (x : Nat),first.output.state.demand[x]! ≤ term.output.state.demand[x]!) := by
  obtain ⟨result,run,scope,dominated,order⟩ := LinearCfgWitness.actual_linear_driver_witness
  have labels : (Array.range result.order.nodes.size).reverse.toList =
      ([] : List Nat) ++ 2 :: ([1] ++ 0 :: []) := by rw [order]; decide +kernel
  obtain ⟨ranges,params,input,afterFirst,beforeSecond,fc,sc,fd,sd,
    build,fr,sr,state,gap,fm,sm⟩ := CfgTrace.actual_ordered_original_cores run labels
      (by simp [order] : result.order.nodes[2]! = .original 2)
      (by simp [order] : result.order.nodes[0]! = .original 0)
  have fb := (stock_lowerBlockCore_scanOrigin fr).2.2.1
  have sb := (stock_lowerBlockCore_scanOrigin sr).2.2.1
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope sm
  refine ⟨result,fc.scan,sc.scan,b,term,body,run,scope,labels,fb,sb,fm,sm,split,?_⟩
  exact CfgDemand.ordered_scan_demand run scope labels
    (by simp [order,fb]) (by simp [order,sb]) fm sm split

/-- A real four-node compilation with synthetic critical edges inhabits the
whole-traversal demand theorem; no edge-only replay or assumed state is used. -/
theorem critical_traversal_demand_witness :
    ∃ (f : Clif.Function) (result : Result) (ranges : Array (Nat × Nat)) (params : List Nat)
      (starting finishing : DriverState),
      Stock.lower f = .ok result ∧ LowerScope f ∧ result.order.nodes.size = 4 ∧
      (∃ pred k target,.edge pred k target ∈ result.order.nodes.toList) ∧
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧ starting.state = result.initial ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d) starting = .ok finishing ∧
      (∀ (x : Nat),starting.state.demand[x]! ≤ finishing.state.demand[x]!) := by
  obtain ⟨f,result,run,scope,blocks,nodes,edge,terminal,records⟩ :=
    TerminalDriverWitness.stock_critical_driver_unsunk_witness
  obtain ⟨ranges,params,starting,finishing,build,ordered,initial,empty,folded,events⟩ :=
    LinearCfg.actual_traversal run
  exact ⟨f,result,ranges,params,starting,finishing,run,scope,nodes,edge,build,initial,folded,
    CfgDemand.traversal_demand_mono folded⟩

end Backend.Stock.Proof.CfgDemandWitness

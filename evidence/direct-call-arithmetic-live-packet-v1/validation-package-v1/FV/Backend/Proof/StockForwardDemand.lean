import FV.Backend.Proof.StockForwardSourceOrder
import FV.Backend.Proof.StockCfgTraversalDemand

namespace Backend.Stock.Proof.ForwardSource
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A ranked original source edge transfers the actual successor scan's demands
to its predecessor terminator. Source ranking supplies the order; the successful
Stock run supplies all scans and intervening states, including synthetic nodes. -/
theorem successor_demand {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ranked : Ranked f rank)
    {source : Array (Array Nat)} (computed : stockSourceTable f = .ok source)
    {predecessorLabel successorLabel : Nat} {predecessor successor : BlockScanEvent}
    (predecessorTag : result.order.nodes[predecessorLabel]? = some (.original predecessor.block))
    (successorTag : result.order.nodes[successorLabel]? = some (.original successor.block))
    (edge : successor.block ∈ source[predecessor.block]!.toList)
    (pe : predecessor ∈ result.blockScans.toList) (se : successor ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f predecessor b term body) :
    ∀ (x : Nat),successor.output.state.demand[x]! ≤ term.output.state.demand[x]! := by
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have before := successor_labels (stock_lower_order run) nonempty ranked computed predecessorTag successorTag edge
  exact CfgDemand.ordered_scan_demand_of_labels run scope
    (Array.getElem?_eq_some_iff.mp successorTag).1 before
    (by simp only [getElem!_def,successorTag,Option.getD_some])
    (by simp only [getElem!_def,predecessorTag,Option.getD_some]) se pe split

end Backend.Stock.Proof.ForwardSource

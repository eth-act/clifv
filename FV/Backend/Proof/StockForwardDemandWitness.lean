module

public import FV.Backend.Proof.StockForwardDemand
public import FV.Backend.Proof.LowerDecide

@[expose] public section

namespace Backend.Stock.Proof.ForwardDemandWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

private def function : Clif.Function := {
  name := "stock_forward_critical_demand"
  sig := {params := [{ty := .i64},{ty := .i64}],returns := [{ty := .i64}]}
  blocks := [
    {id := 0,params := [(0,.i64),(1,.i64)],term := .brif 0 ⟨10,[1]⟩ ⟨20,[1]⟩},
    {id := 10,params := [(2,.i64)],term := .jump ⟨20,[2]⟩},
    {id := 20,params := [(3,.i64)],term := .ret [3]}] }
private def order : Order := ⟨#[.original 0,.edge 0 1 2,.original 1,.original 2],
  #[#[2,1],#[3],#[3],#[]]⟩
private def source : Array (Array Nat) := #[#[1,2],#[2],#[]]

private theorem ranked : ForwardSource.Ranked function (fun b => b) := by
  intro bi b ti destination found present target
  change bi < ti
  cases bi with
  | zero =>
    simp only [function,List.getElem?_cons_zero,Option.some.injEq] at found
    subst b
    simp only [destinations,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl <;> simp [function,List.findIdx?_cons] at target <;> omega
  | succ bi =>
    cases bi with
    | zero =>
      simp only [function,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at found
      subst b
      simp only [destinations,List.map_cons,List.map_nil,List.mem_singleton] at present
      subst destination
      simp [function,List.findIdx?_cons] at target
      omega
    | succ bi =>
      cases bi with
      | zero =>
        simp only [function,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at found
        subst b
        cases present
      | succ bi => simp [function] at found

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem computed : stockSourceTable function = .ok source := by cbv
private theorem ordered : blockOrder function = .ok order := by cbv
private theorem compiled : (Stock.lower function).isOk = true := by decide +kernel

/-- A real conditional source edge crosses an ordinary middle block and a
synthetic critical node in the reverse traversal. Its endpoint labels and demand
transfer are derived from original source ranking and actual compilation. -/
theorem critical_source_demand_witness :
    ∃ (f : Clif.Function) (result : Result) (predecessor successor : BlockScanEvent)
      (b : Clif.Block) (term : ScanRecord) (body : BlockScan),
      Stock.lower f = .ok result ∧ LowerScope f ∧ ForwardSource.Ranked f (fun bi => bi) ∧
      result.order.nodes = #[.original 0,.edge 0 1 2,.original 1,.original 2] ∧
      predecessor.block = 0 ∧ successor.block = 2 ∧
      predecessor ∈ result.blockScans.toList ∧ successor ∈ result.blockScans.toList ∧
      SourceBodySplit f predecessor b term body ∧
      (∀ (x : Nat),successor.output.state.demand[x]! ≤ term.output.state.demand[x]!) := by
  have success := compiled
  cases run : Stock.lower function with
  | error message => rw [run] at success; cases success
  | ok result =>
    have resultOrder : result.order = order := Except.ok.inj ((stock_lower_order run).symm.trans ordered)
    have labels : (Array.range result.order.nodes.size).reverse.toList =
        ([] : List Nat) ++ 3 :: ([2,1] ++ 0 :: []) := by rw [resultOrder]; decide +kernel
    obtain ⟨ranges,params,input,afterFirst,beforeSecond,fc,sc,fd,sd,
      build,fr,sr,state,gap,fm,sm⟩ := CfgTrace.actual_ordered_original_cores run labels
        (by simp [resultOrder,order] : result.order.nodes[3]! = .original 2)
        (by simp [resultOrder,order] : result.order.nodes[0]! = .original 0)
    have fb := (stock_lowerBlockCore_scanOrigin fr).2.2.1
    have sb := (stock_lowerBlockCore_scanOrigin sr).2.2.1
    obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope sm
    refine ⟨function,result,sc.scan,fc.scan,b,term,body,run,scope,ranked,?_,sb,fb,sm,fm,split,?_⟩
    · simp only [resultOrder,order]
    · exact ForwardSource.successor_demand run scope ranked computed
        (by simp [resultOrder,order,sb] : result.order.nodes[0]? = some (.original sc.scan.block))
        (by simp [resultOrder,order,fb] : result.order.nodes[3]? = some (.original fc.scan.block))
        (by simp [fb,sb,source]) sm fm split

end Backend.Stock.Proof.ForwardDemandWitness

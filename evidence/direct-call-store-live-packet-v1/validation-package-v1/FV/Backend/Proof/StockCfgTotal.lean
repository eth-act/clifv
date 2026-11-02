import FV.Backend.Proof.StockTryCfg
import FV.Backend.Proof.StockNodeCoverage
import FV.Backend.Proof.StockOrdinaryCfg
import FV.Backend.Proof.StockPrepareTotal

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- The complete actual Stock output satisfies the computed emitted-CFG
specification under the original scope. All ordinary/terminal/TryCall/synthetic
cases are proved internally, with no caller graph or rule certificate. -/
theorem stock_lower_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    Prep.CfgSpec result.code.blocks result.order.successors := by
  obtain ⟨count,bounds⟩ := stock_lower_graph_bounds run
  refine ⟨count,?_⟩
  intro label vb atBlock
  have blockBound := (Array.getElem?_eq_some_iff.mp atBlock).1
  have nodeBound : label < result.order.nodes.size := by
    rw [← (stock_prepare_dimensions run).2.1,(stock_prepare_dimensions run).1]
    exact blockBound
  have clause : ∃ (block : VBlock) (last : MInst) (row : Array Nat),
      result.code.blocks[label]? = some block ∧ block.insts.back? = some last ∧
      last.isTerminator = true ∧ result.order.successors[label]? = some row ∧
      row.size = last.targets.length ∧
      ∀ (j : Nat) (l : Label),last.targets[j]? = some l →
        ∃ k,row[j]? = some k ∧ Prep.lab result.code.blocks l = some k := by
    cases tag : result.order.nodes[label] with
    | edge pred index target =>
      have node : result.order.nodes[label]? = some (.edge pred index target) := by
        rw [Array.getElem?_eq_getElem nodeBound,tag]
      exact stock_lower_critical_cfg run scope node
    | original bi =>
      have node : result.order.nodes[label]? = some (.original bi) := by
        rw [Array.getElem?_eq_getElem nodeBound,tag]
      have projected : bi ∈ stockOriginals result.order.nodes := by
        unfold stockOriginals
        exact List.mem_filterMap.mpr ⟨.original bi,Array.mem_toList_iff.mpr (Array.mem_of_getElem? node),rfl⟩
      have biBound := (stock_blockOrder_originals_nodup (stock_lower_order run)
        (fun h => scope.nonempty (List.length_eq_zero_iff.mp h))).2 bi projected
      have block : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
      have source : f.blocks[bi]! = f.blocks[bi] := by simp only [getElem!_def,block,Option.getD_some]
      have subset := scope.subsetE
      simp only [Compile.functionE,Bool.and_eq_true,List.all_eq_true] at subset
      have termE := (subset.2 f.blocks[bi] (List.mem_of_getElem? block)).2
      cases term : f.blocks[bi].term with
      | jump dest =>
        exact OrdinaryCfg.stock_lower_ordinary_cfg run scope node (by simp [source,term,OrdinaryCfg.ordinary])
      | brif c td ed =>
        exact OrdinaryCfg.stock_lower_ordinary_cfg run scope node (by simp [source,term,OrdinaryCfg.ordinary])
      | brTable x dest tbl =>
        exact OrdinaryCfg.stock_lower_ordinary_cfg run scope node (by simp [source,term,OrdinaryCfg.ordinary])
      | ret vals =>
        obtain ⟨block,last,placed,back,ends,targets,row⟩ := stock_lower_terminal_cfg_at run scope node
          (b := f.blocks[bi]) block (by simp [term,retOrTrap])
        refine ⟨block,last,#[],placed,back,ends,row,?_,?_⟩
        · simp [targets]
        · intro j l atTarget
          simp [targets] at atTarget
      | trap code =>
        obtain ⟨block,last,placed,back,ends,targets,row⟩ := stock_lower_terminal_cfg_at run scope node
          (b := f.blocks[bi]) block (by simp [term,retOrTrap])
        refine ⟨block,last,#[],placed,back,ends,row,?_,?_⟩
        · simp [targets]
        · intro j l atTarget
          simp [targets] at atTarget
      | returnCall fn args =>
        simp only [term,Compile.termE] at termE
        contradiction
      | tryCall fn args et =>
        exact stock_lower_try_cfg run scope node (by simp [source,term,Clif.Terminator.isTry])
      | tryCallIndirect callee args et =>
        exact stock_lower_try_cfg run scope node (by simp [source,term,Clif.Terminator.isTry])
  obtain ⟨block,last,row,placed,back,ends,atRow,arity,targets⟩ := clause
  rw [atBlock] at placed
  cases placed
  exact ⟨last,row,back,ends,atRow,arity,targets⟩

/-- Actual Stock output always passes raw indexed preparation and its internal
checker under the unchanged original source scope. The earlier graph-premise
variant is retained; this variant derives that premise from the actual driver. -/
theorem stock_prepare_total {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    ∃ prepared,prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  exact stock_prepare_total_of_graph run scope (stock_lower_cfg run scope)

end Backend.Stock.Proof

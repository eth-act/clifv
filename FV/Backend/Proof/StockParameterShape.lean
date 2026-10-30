import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockEntryCode
import FV.Backend.Proof.StockPrepareInputs
import FV.Backend.SpillAlloc
import FV.Backend.Proof.StockCriticalCode

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Internal allocator metadata: parameters are virtual integer registers with
pairwise distinct virtual numbers. This is derived from original source SSA. -/
def ParameterShape (params : Array Reg) : Prop :=
  (∀ r ∈ params.toList,∃ n,r = .vreg n .int) ∧
  (params.toList.map Reg.homeNum).Nodup

private theorem empty_shape : ParameterShape #[] := ⟨by simp,by simp⟩
private theorem numbers_shape {numbers : List Nat} (distinct : numbers.Nodup) :
    ParameterShape ((numbers.map (fun n => Reg.vreg n .int)).toArray) := by
  constructor
  · intro r member
    simp only [List.toList_toArray,List.mem_map] at member
    obtain ⟨n,_,rfl⟩ := member
    exact ⟨n,rfl⟩
  · simpa [List.map_map,Function.comp_def,Reg.homeNum] using distinct

private theorem built_context {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩

private theorem parameter_mapped {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b) {x : Nat}
    (parameter : x ∈ b.params.map (·.1)) : ∃ key,result.ctx.valueReg? x = some (.vreg key .int) := by
  obtain ⟨ranges,build⟩ := built_context run
  obtain ⟨original,st0,sourceBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨q,member,rfl⟩ := List.mem_map.mp parameter
  have old := (spec.facts.types ssa).2 b (List.mem_of_getElem? block) q member
  have typed : result.ctx.valueType? q.1 = some (CTy.ofClif q.2) := by
    simpa only [Ctx.valueType?,view.valTy] using old
  exact (buildCtx_mappedInv scope build).typedReg q.1 _ typed

/-- Actual original source parameters remain distinct after final aliasing.
Scope and original SSA supply mapping, alias terminality and injectivity. -/
theorem stock_parameter_numbers_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b) : (edgeParamNumbers result b).Nodup := by
  obtain ⟨ranges,build⟩ := built_context run
  have original := (List.nodup_append.mp (block_nodup ssa block)).1
  change List.Pairwise (fun a b : Nat => a ≠ b)
    ((b.params.map (·.1)).map (fun x => aliasNum result.final.alias (edgeValueNum result.ctx x)))
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem ?_ original
  intro x y hx hy different equal
  obtain ⟨nx,mx⟩ := parameter_mapped run scope ssa block hx
  obtain ⟨ny,my⟩ := parameter_mapped run scope ssa block hy
  have number_eq {x n : Nat} (mapped : result.ctx.valueReg? x = some (.vreg n .int)) :
      edgeValueNum result.ctx x = n := by simp only [edgeValueNum,mapped]
  rw [number_eq mx,number_eq my,stock_lower_parameter_resolves run ssa block hx mx,
    stock_lower_parameter_resolves run ssa block hy my] at equal
  subst ny
  exact different ((buildCtx_allocated build).2.1 x y nx mx my)

/-- Every block of the actual Stock output has virtual-int, distinct parameter
metadata. Entry and real synthetic nodes are included, without a caller-supplied
node/origin/parameter certificate or a new accepted-source condition. -/
theorem stock_lower_parameter_shape {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) :
    ∀ (label : Nat) (vb : VBlock),result.code.blocks[label]? = some vb → ParameterShape vb.params := by
  intro label vb placed
  by_cases entry : label = 0
  · subst label
    obtain ⟨_,block,atBlock,_,params⟩ := stock_lower_entry_code run scope
    rw [placed] at atBlock
    cases atBlock
    rw [params]
    exact empty_shape
  have blockBound := (Array.getElem?_eq_some_iff.mp placed).1
  have nodeBound : label < result.order.nodes.size := by
    rw [← (stock_prepare_dimensions run).2.1,(stock_prepare_dimensions run).1]
    exact blockBound
  cases tag : result.order.nodes[label] with
  | edge pred index target =>
    have node : result.order.nodes[label]? = some (.edge pred index target) := by
      rw [Array.getElem?_eq_getElem nodeBound,tag]
    obtain ⟨input,next,args,targetLabel,_,_,_,atBlock⟩ := stock_lower_critical_code run node
    rw [placed] at atBlock
    cases atBlock
    exact empty_shape
  | original bi =>
    have node : result.order.nodes[label]? = some (.original bi) := by
      rw [Array.getElem?_eq_getElem nodeBound,tag]
    have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
    have projected : bi ∈ stockOriginals result.order.nodes := by
      unfold stockOriginals
      exact List.mem_filterMap.mpr ⟨.original bi,Array.mem_toList_iff.mpr (Array.mem_of_getElem? node),rfl⟩
    have biBound := (stock_blockOrder_originals_nodup (stock_lower_order run) nonempty).2 bi projected
    have source : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
    have nonentry : bi ≠ 0 := by
      intro zero
      rw [zero] at node
      have equal := stock_blockOrder_original_unique (stock_lower_order run) nonempty node
        (stock_blockOrder_entry (stock_lower_order run) scope.nonempty)
      exact entry equal
    obtain ⟨block,atBlock,_,params⟩ := stock_lower_original_block_params run scope ssa node source nonentry
    rw [placed] at atBlock
    cases atBlock
    rw [params]
    exact numbers_shape (stock_parameter_numbers_nodup run scope ssa source)

end Backend.Stock.Proof

import FV.Backend.Proof.PerEdgePrepareComplete
import FV.Backend.Proof.PerEdgePrepareSound
import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.StockSourceOrder
import FV.Backend.Proof.IselExtern

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

private theorem assembled_label {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.label = label := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; rfl

private theorem node_install {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ block,output.blocks = input.blocks.set! label block ∧ block.label = label := by
  unfold lowerNode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    refine ⟨_,rfl,?_⟩
    first | rfl | exact assembled_label (by assumption)

private theorem nodes_labels {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.blocks.size = input.blocks.size ∧
    ∀ (k : Nat) (hk : k < output.blocks.size),
      (k ∈ labels ∨ input.blocks[k]!.label = k) → output.blocks[k].label = k := by
  induction labels generalizing input with
  | nil =>
    cases run
    refine ⟨rfl,?_⟩
    intro k hk source
    simpa only [getElem!_pos output.blocks k hk] using source.resolve_left (by simp)
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases step : lowerNode ctx ranges order f params label input with
    | error e => simp only [step,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [step,bind,Except.bind] at run
      obtain ⟨block,installed,labelled⟩ := node_install step
      have size : middle.blocks.size = input.blocks.size := by rw [installed]; simp
      obtain ⟨later,keeps⟩ := ih run
      refine ⟨later.trans size,?_⟩
      intro k hk source
      have hm : k < middle.blocks.size := by rw [← later]; exact hk
      apply keeps k hk
      by_cases future : k ∈ rest
      · exact .inl future
      · right
        by_cases same : label = k
        · have bound : k < input.blocks.size := by rw [← size]; exact hm
          have atBlock : middle.blocks[k]? = some block := by
            rw [installed,same,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
          rw [getElem!_pos middle.blocks k hm]
          simpa only [Array.getElem?_eq_getElem hm,Option.map_some,Option.some.injEq,labelled,same]
            using congrArg (Option.map VBlock.label) atBlock
        · have inherited : input.blocks[k]!.label = k := by
            rcases source with member | source
            · simp only [List.mem_cons] at member
              rcases member with same' | member
              · exact False.elim (same same'.symm)
              · exact False.elim (future member)
            · exact source
          have unchanged : middle.blocks[k]? = input.blocks[k]? := by
            rw [installed]
            simp [Array.set!,same]
          have bound : k < input.blocks.size := by rw [← size]; exact hm
          rw [Array.getElem?_eq_getElem hm,Array.getElem?_eq_getElem bound] at unchanged
          rw [getElem!_pos input.blocks k bound] at inherited
          rw [getElem!_pos middle.blocks k hm]
          exact congrArg VBlock.label (Option.some.inj unchanged) |>.trans inherited

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

private theorem code_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      blockOrder f = .ok result.order ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d)
        (startDriver result.initial result.order.nodes.size) = .ok driver ∧
      result.code.blocks = driver.blocks.map (fun b => {b with
        insts := b.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := b.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := b.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))}) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,by assumption,by assumption,rfl⟩

/-- Stock's actual traversal installs the dense numeric label at every returned
block. The original scope's nonempty source derives the complete preparation
graph domain internally, without a supplied CFG/label certificate. -/
theorem stock_prepare_domain {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    0 < result.code.blocks.size ∧ Prep.Lbls result.code.blocks := by
  obtain ⟨ranges,params,driver,ordered,folded,code⟩ := code_origin run
  obtain ⟨size,labels⟩ := nodes_labels folded
  have count : result.code.blocks.size = result.order.nodes.size := by
    rw [code,Array.size_map,size]
    simp [startDriver]
  have dense : ∀ (k : Nat) (hk : k < result.code.blocks.size), result.code.blocks[k].label = k := by
    intro k hk
    have hd : k < driver.blocks.size := by rw [code,Array.size_map] at hk; exact hk
    have member : k ∈ (Array.range result.order.nodes.size).reverse.toList := by
      simpa using (show k < result.order.nodes.size by rw [← count]; exact hk)
    have label := labels k hd (.inl member)
    have atIndex : (result.code.blocks[k]?.map VBlock.label) = some k := by
      rw [code]
      simp [Array.getElem?_map,Array.getElem?_eq_getElem hd,label]
    simpa only [Array.getElem?_eq_getElem hk,Option.map_some,Option.some.injEq] using atIndex
  have nodup : Prep.Lbls result.code.blocks := by
    unfold Prep.Lbls
    rw [List.nodup_iff_eq_of_getElem_eq]
    intro j k hj hk equal
    simp only [List.length_map,Array.length_toList] at hj hk
    simpa [dense j hj,dense k hk] using equal
  obtain ⟨source,computed,projection⟩ := stock_blockOrder_originals ordered
  obtain ⟨sourceSize,bounds⟩ := stock_sourceTable_bounds computed
  have nonzero : source.size ≠ 0 := by
    rw [sourceSize]
    exact fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have first := (Prep.rpo_spec bounds nonzero).2.2.1
  have member : 0 ∈ stockOriginals result.order.nodes := by
    rw [projection]
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? first)
  unfold stockOriginals at member
  obtain ⟨node,inside,_⟩ := List.mem_filterMap.mp member
  obtain ⟨k,hk,_⟩ := List.getElem_of_mem inside
  have positive : 0 < result.order.nodes.size := by simp only [Array.length_toList] at hk; omega
  exact ⟨by rw [count]; exact positive,nodup⟩

/-- The actual Stock output cannot be rejected by the indexed preparation
relation after successful preparation, under the original source scope alone. -/
theorem stock_prepCheckAt_complete {f : Clif.Function} {result : Result} {prepared : EdgeVCode}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f)
    (preparedRun : prepareAt result.code result.edgeArgs = .ok prepared) :
    PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain lowered scope
  exact PerEdgePrep.prepCheckAt_complete preparedRun nonempty labels

/-- The real internal checked wrapper preserves every successful Stock
preparation; no extra numeric-label or checker premise is supplied by callers. -/
theorem stock_prepareCheckedAt_complete {f : Clif.Function} {result : Result} {prepared : EdgeVCode}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f)
    (preparedRun : prepareAt result.code result.edgeArgs = .ok prepared) :
    prepareCheckedAt result.code result.edgeArgs = .ok prepared := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain lowered scope
  exact PerEdgePrep.prepareCheckedAt_complete preparedRun nonempty labels

/-- Actual Stock preparation preserves complete returns under the original
source scope; the internal indexed checker verdict is derived, not supplied. -/
theorem stock_prepare_return {W : Type} {f : Clif.Function} {result : Result} {prepared : EdgeVCode}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f)
    (preparedRun : prepareAt result.code result.edgeArgs = .ok prepared)
    {sem : ISem CV W} (semantics : DriverSemG sem) {ρ : Nat → CV} {w w' : W} {values : List CV}
    (source : Star (VStepAt result.code result.edgeArgs sem) (VConf.init ρ w) (.ret values w')) :
    Star (VStepAt prepared.code prepared.edges sem) (VConf.init ρ w) (.ret values w') :=
  PerEdgePrep.prep_ret semantics (stock_prepCheckAt_complete lowered scope preparedRun) source

/-- Actual Stock preparation preserves complete halts, with no caller checker
verdict or numeric graph certificate. -/
theorem stock_prepare_halt {W : Type} {f : Clif.Function} {result : Result} {prepared : EdgeVCode}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f)
    (preparedRun : prepareAt result.code result.edgeArgs = .ok prepared)
    {sem : ISem CV W} (semantics : DriverSemG sem) {ρ : Nat → CV} {w w' : W}
    (source : Star (VStepAt result.code result.edgeArgs sem) (VConf.init ρ w) (.halt w')) :
    Star (VStepAt prepared.code prepared.edges sem) (VConf.init ρ w) (.halt w') :=
  PerEdgePrep.prep_halt semantics (stock_prepCheckAt_complete lowered scope preparedRun) source

/-- Typed return and coded-trap observations of actual Stock preparation are
preserved under the original source scope, deriving every structural check. -/
theorem stock_prepare_sound {W : Type} {f : Clif.Function} {result : Result} {prepared : EdgeVCode}
    (lowered : Stock.lower f = .ok result) (scope : LowerScope f)
    (preparedRun : prepareAt result.code result.edgeArgs = .ok prepared)
    {sem : ISem CV W} (semantics : DriverSemG sem) (ρ : Nat → CV) (w : W) :
    (∀ us values w',PerEdgePrep.VRetFromAt result.code result.edgeArgs sem ⟨0,0,ρ,w⟩ us values w' →
      PerEdgePrep.VRetFromAt prepared.code prepared.edges sem ⟨0,0,ρ,w⟩ us values w') ∧
    (∀ c,PerEdgePrep.VTrapFromAt result.code result.edgeArgs sem ⟨0,0,ρ,w⟩ c →
      PerEdgePrep.VTrapFromAt prepared.code prepared.edges sem ⟨0,0,ρ,w⟩ c) :=
  PerEdgePrep.prep_sound semantics (stock_prepCheckAt_complete lowered scope preparedRun) ρ w

end Backend.Stock.Proof

import FV.Backend.Proof.StockPrepareComplete
import FV.Backend.Proof.StockPrepareInputs
import FV.Backend.Proof.StockCriticalCode

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

/-- Every returned Stock block has its actual dense numeric index as label.
This holds for every successful run, without a source scope or CFG premise. -/
theorem stock_lower_dense_labels {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∀ (k : Nat) (hk : k < result.code.blocks.size),result.code.blocks[k].label = k := by
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
  exact dense

/-- Every synthetic node satisfies its complete emitted-CFG clause against the
computed graph, including actual target-label lookup after final aliasing. -/
theorem stock_lower_critical_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label pred index target : Nat}
    (node : result.order.nodes[label]? = some (.edge pred index target)) :
    ∃ (block : VBlock) (t : MInst) (row : Array Nat),
      result.code.blocks[label]? = some block ∧ block.insts.back? = some t ∧
      t.isTerminator = true ∧ result.order.successors[label]? = some row ∧
      row.size = t.targets.length ∧
      ∀ (j : Nat) (l : Label),t.targets[j]? = some l → ∃ k,row[j]? = some k ∧ Prep.lab result.code.blocks l = some k := by
  obtain ⟨input,next,args,targetLabel,_,successors,targetNode,placed⟩ := stock_lower_critical_code run node
  have bound : targetLabel < result.code.blocks.size := by
    have h := (Array.getElem?_eq_some_iff.mp targetNode).1
    rw [← (stock_prepare_dimensions run).2.1] at h
    rw [← (stock_prepare_dimensions run).1]
    exact h
  have find : Prep.lab result.code.blocks targetLabel = some targetLabel :=
    Prep.lab_of (stock_prepare_domain run scope).2 bound (stock_lower_dense_labels run targetLabel bound)
  refine ⟨_,.jump targetLabel,#[targetLabel],placed,by rfl,rfl,successors,rfl,?_⟩
  intro j l atTarget
  cases j with
  | zero =>
    have same : targetLabel = l := Option.some.inj atTarget
    subst l
    exact ⟨targetLabel,rfl,find⟩
  | succ j => simp [MInst.targets] at atTarget

end Backend.Stock.Proof

import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 4096

/-- The exact successor-table computation used by blockOrder. -/
def stockSourceTable (f : Clif.Function) : Except String (Array (Array Nat)) :=
  f.blocks.toArray.mapM fun b =>
    (destinations b.term).toArray.mapM fun (id, _) =>
      match f.blocks.findIdx? (·.id == id) with
      | some i => pure i
      | none => throw s!"unknown block{id}"

private theorem mapM_lookup {α β : Type} {xs : Array α} {ys : Array β}
    {step : α → Except String β} (run : xs.mapM step = .ok ys)
    {i : Nat} {y : β} (lookup : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ step x = .ok y := by
  obtain ⟨sizes, calls⟩ := Prep.amapM_ok run
  obtain ⟨bound, eq⟩ := Array.getElem?_eq_some_iff.mp lookup
  have xb : i < xs.size := by omega
  obtain ⟨z, call, result⟩ := calls i xs[i] (by simp [xb])
  have same : z = y := by rw [lookup] at result; exact (Option.some.inj result).symm
  subst z
  exact ⟨xs[i], by simp [xb], call⟩

/-- Successful source destination lookup produces an in-bounds successor table. -/
theorem stock_sourceTable_bounds {f : Clif.Function} {source : Array (Array Nat)}
    (run : stockSourceTable f = .ok source) :
    source.size = f.blocks.length ∧ Prep.SuccsIn source := by
  have outer := Prep.amapM_ok run
  refine ⟨by simpa [stockSourceTable] using outer.1, ?_⟩
  intro b s member
  cases row : source[b]? with
  | none => simp only [getElem!_def, row] at member; cases member
  | some successors =>
    obtain ⟨block, found, blockRun⟩ := mapM_lookup run row
    have member' : s ∈ successors := by simpa only [getElem!_def, row, Array.mem_toList_iff] using member
    obtain ⟨i, lookup⟩ := Array.mem_iff_getElem?.mp member'
    obtain ⟨destination, _, destRun⟩ := mapM_lookup blockRun lookup
    cases target : f.blocks.findIdx? (·.id == destination.1) with
    | none => simp only [target, throw, throwThe, MonadExceptOf.throw] at destRun; cases destRun
    | some index =>
      simp only [target, pure, Except.pure] at destRun
      cases destRun
      have bound := (List.findIdx?_eq_some_iff_getElem.mp target).1
      simpa only [outer.1, List.size_toArray] using bound

/-- Actual source successors make reachable source RPO unique and bounded. -/
theorem stock_sourceTable_rpo {f : Clif.Function} {source : Array (Array Nat)}
    (run : stockSourceTable f = .ok source) (nonempty : f.blocks.length ≠ 0) :
    (rpo source).toList.Nodup ∧
    (∀ i ∈ (rpo source).toList, i < f.blocks.length) := by
  obtain ⟨size, bounds⟩ := stock_sourceTable_bounds run
  obtain ⟨valid, nodup, _⟩ := Prep.rpo_spec bounds (by simpa only [size] using nonempty)
  exact ⟨nodup, fun i member => by simpa only [size] using valid i member⟩

/-- A successful actual block order contains a successfully computed source table. -/
theorem stock_blockOrder_sourceTable {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) :
    ∃ source, stockSourceTable f = .ok source ∧
      source.size = f.blocks.length ∧ Prep.SuccsIn source := by
  unfold blockOrder at run
  simp only [bind, Except.bind] at run
  split at run
  · cases run
  · rename_i source sourceRun
    have computed : stockSourceTable f = .ok source := by
      unfold stockSourceTable
      apply Eq.trans ?_ sourceRun
      congr 2
    exact ⟨source, computed, stock_sourceTable_bounds computed⟩

/-- Source blocks in a lowered-node array, dropping inserted critical edges. -/
def stockOriginals (nodes : Array Node) : List Nat :=
  nodes.toList.filterMap fun
    | .original bi => some bi
    | .edge .. => none

private def orderEdgeStep (indegree : Array Nat) (bi : Nat)
    (pair : Nat × Nat) (nodes : Array Node) : Except String (ForInStep (Array Node)) :=
  if indegree[pair.1]! > 1 then pure (.yield (nodes.push (.edge bi pair.2 pair.1)))
  else pure (.yield nodes)

private theorem orderEdge_frame (indegree : Array Nat) (bi : Nat)
    (pair : Nat × Nat) (a b : Array Node)
    (run : orderEdgeStep indegree bi pair a = .ok (.yield b)) :
    stockOriginals b = stockOriginals a := by
  unfold orderEdgeStep at run
  split at run <;> cases run
  · simp [stockOriginals]
  · rfl

private theorem orderEdge_noBreak (indegree : Array Nat) (bi : Nat)
    (pair : Nat × Nat) (a b : Array Node) :
    orderEdgeStep indegree bi pair a ≠ .ok (.done b) := by
  intro run
  unfold orderEdgeStep at run
  split at run <;> cases run

private theorem forIn_frame {α β γ : Type} (field : α → γ)
    (step : β → α → Except String (ForInStep α))
    (keeps : ∀ x a b, step x a = .ok (.yield b) → field b = field a)
    (no_break : ∀ x a b, step x a ≠ .ok (.done b))
    (xs : List β) {a next : α} (h : forIn xs a step = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => simp only [List.forIn_nil, pure, Except.pure] at h; cases h; rfl
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases call : step x a with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok result =>
      cases result with
      | done b => exact False.elim (no_break x a b call)
      | yield b =>
        simp only [call, bind, Except.bind] at h
        exact (ih h).trans (keeps x a b call)


private def orderForce (term : Clif.Terminator) : Bool :=
  match term with
  | .brTable .. | .tryCall .. | .tryCallIndirect .. => true
  | _ => false

private def orderNodeStep (f : Clif.Function) (source : Array (Array Nat))
    (indegree : Array Nat) (bi : Nat) (nodes : Array Node) :
    Except String (ForInStep (Array Node)) := do
  let nodes := nodes.push (.original bi)
  let force := orderForce f.blocks[bi]!.term
  if force || source[bi]!.size > 1 then
    let next ← forIn source[bi]!.zipIdx nodes (orderEdgeStep indegree bi)
    pure (.yield next)
  else pure (.yield nodes)

private theorem orderNode_frame (f : Clif.Function) (source : Array (Array Nat))
    (indegree : Array Nat) (bi : Nat) (a b : Array Node)
    (run : orderNodeStep f source indegree bi a = .ok (.yield b)) :
    stockOriginals b = stockOriginals a ++ [bi] := by
  unfold orderNodeStep at run
  dsimp only at run
  split at run
  · cases loop : forIn source[bi]!.zipIdx (a.push (.original bi)) (orderEdgeStep indegree bi) with
    | error e => simp only [loop, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [loop, bind, Except.bind, pure, Except.pure] at run
      cases run
      rw [← Array.forIn_toList] at loop
      have same := forIn_frame stockOriginals _ (orderEdge_frame indegree bi)
        (orderEdge_noBreak indegree bi) _ loop
      simpa [stockOriginals] using same
  · cases run
    simp [stockOriginals]

private theorem orderNode_noBreak (f : Clif.Function) (source : Array (Array Nat))
    (indegree : Array Nat) (bi : Nat) (a b : Array Node) :
    orderNodeStep f source indegree bi a ≠ .ok (.done b) := by
  intro run
  unfold orderNodeStep at run
  dsimp only at run
  split at run
  · cases loop : forIn source[bi]!.zipIdx (a.push (.original bi)) (orderEdgeStep indegree bi) with
    | error e => simp only [loop, bind, Except.bind] at run; cases run
    | ok next => simp only [loop, bind, Except.bind, pure, Except.pure] at run; cases run
  · cases run

private theorem orderNodes_projection (f : Clif.Function) (source : Array (Array Nat))
    (indegree : Array Nat) (indices : List Nat) {a b : Array Node}
    (run : forIn indices a (orderNodeStep f source indegree) = .ok b) :
    stockOriginals b = stockOriginals a ++ indices := by
  induction indices generalizing a with
  | nil => simp only [List.forIn_nil, pure, Except.pure] at run; cases run; simp
  | cons bi rest ih =>
    rw [List.forIn_cons] at run
    cases call : orderNodeStep f source indegree bi a with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok step =>
      cases step with
      | done next => exact False.elim (orderNode_noBreak f source indegree bi a next call)
      | yield next =>
        simp only [call, bind, Except.bind] at run
        rw [ih run, orderNode_frame f source indegree bi a next call]
        simp only [List.append_assoc, List.singleton_append]

/-- Inserting critical-edge nodes preserves exactly the source RPO projection. -/
theorem stock_blockOrder_originals {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) :
    ∃ source, stockSourceTable f = .ok source ∧
      stockOriginals order.nodes = (rpo source).toList := by
  unfold blockOrder at run
  simp only [bind, Except.bind] at run
  split at run
  · cases run
  · rename_i source sourceRun
    have computed : stockSourceTable f = .ok source := by
      unfold stockSourceTable
      apply Eq.trans ?_ sourceRun
      congr 2
    split at run
    · cases run
    · rename_i indegree degreeRun
      split at run
      · cases run
      · rename_i nodes nodesRun
        have normalized : forIn (rpo source) #[] (orderNodeStep f source indegree) = .ok nodes := by
          apply Eq.trans ?_ nodesRun
          congr 2
        have projected : stockOriginals nodes = (rpo source).toList := by
          rw [← Array.forIn_toList] at normalized
          simpa [stockOriginals] using orderNodes_projection f source indegree _ normalized
        split at run
        · cases run
        · simp only [pure, Except.pure] at run
          cases run
          exact ⟨source, computed, projected⟩

/-- Original blocks in a successful nonempty actual lowered order occur once. -/
theorem stock_blockOrder_originals_nodup {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0) :
    (stockOriginals order.nodes).Nodup ∧
    (∀ bi ∈ stockOriginals order.nodes, bi < f.blocks.length) := by
  obtain ⟨source, computed, projected⟩ := stock_blockOrder_originals run
  rw [projected]
  exact stock_sourceTable_rpo computed nonempty

private def orderFunction : Clif.Function := {
  name := "source_order"
  sig := {}
  blocks := [
    { id := 7, params := [], body := [], term := .jump ⟨9, []⟩ },
    { id := 9, params := [], body := [], term := .ret [] }] }
private def orderSource : Array (Array Nat) := #[#[1], #[]]
private def orderOutput : Order := ⟨#[.original 0, .original 1], #[#[1], #[]]⟩

/-- Nontrivial source IDs resolve to dense in-bounds indices. -/
theorem stock_sourceTable_bounds_witness :
    stockSourceTable orderFunction = .ok orderSource ∧
    orderSource.size = orderFunction.blocks.length ∧ Prep.SuccsIn orderSource :=
  by
  have computed : stockSourceTable orderFunction = .ok orderSource := by cbv
  exact ⟨computed, stock_sourceTable_bounds computed⟩

/-- Both reachable source blocks occur once in the actual source RPO. -/
theorem stock_sourceTable_rpo_witness :
    (rpo orderSource).toList = [0, 1] ∧
    (rpo orderSource).toList.Nodup ∧
    (∀ i ∈ (rpo orderSource).toList, i < orderFunction.blocks.length) := by
  have computed : stockSourceTable orderFunction = .ok orderSource := by cbv
  exact ⟨by cbv, stock_sourceTable_rpo computed (by decide)⟩

/-- Actual blockOrder succeeds for the two reachable blocks and their connecting edge. -/
theorem stock_blockOrder_sourceTable_witness :
    blockOrder orderFunction = .ok orderOutput ∧
    (∃ source, stockSourceTable orderFunction = .ok source ∧
      source.size = orderFunction.blocks.length ∧ Prep.SuccsIn source) :=
  by
  have computed : blockOrder orderFunction = .ok orderOutput := by cbv
  exact ⟨computed, stock_blockOrder_sourceTable computed⟩

private def parallelFunction : Clif.Function := {
  name := "parallel_source_edges"
  sig := {}
  blocks := [
    { id := 7, params := [], body := [], term := .brif 0 ⟨9, []⟩ ⟨9, []⟩ },
    { id := 9, params := [], body := [], term := .ret [] }] }
private def parallelSource : Array (Array Nat) := #[#[1, 1], #[]]
private def parallelOrder : Order :=
  ⟨#[.original 0, .edge 0 0 1, .edge 0 1 1, .original 1],
    #[#[1, 2], #[3], #[3], #[]]⟩

/-- Duplicate successor edges create two actual inserted nodes without repeating originals. -/
theorem stock_blockOrder_originals_witness :
    blockOrder parallelFunction = .ok parallelOrder ∧
    stockOriginals parallelOrder.nodes = [0, 1] ∧
    (∃ source, stockSourceTable parallelFunction = .ok source ∧
      stockOriginals parallelOrder.nodes = (rpo source).toList) := by
  have computed : blockOrder parallelFunction = .ok parallelOrder := by cbv
  exact ⟨computed, rfl, stock_blockOrder_originals computed⟩

/-- Both real source blocks remain unique even with two inserted critical edges. -/
theorem stock_blockOrder_originals_nodup_witness :
    blockOrder parallelFunction = .ok parallelOrder ∧
    (stockOriginals parallelOrder.nodes).Nodup ∧
    (∀ bi ∈ stockOriginals parallelOrder.nodes, bi < parallelFunction.blocks.length) := by
  have computed : blockOrder parallelFunction = .ok parallelOrder := by cbv
  exact ⟨computed, stock_blockOrder_originals_nodup computed (by decide)⟩

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 4096

/-- Two occurrences of the same original source block in the actual lowered
order are the same node, despite intervening inserted critical-edge nodes. -/
theorem stock_blockOrder_original_unique {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0)
    {i j bi : Nat} (first : order.nodes[i]? = some (.original bi))
    (second : order.nodes[j]? = some (.original bi)) : i = j := by
  have nd := (stock_blockOrder_originals_nodup run nonempty).1
  have pairs := List.pairwise_filterMap.mp nd
  obtain ⟨ibound, ieq⟩ := Array.getElem?_eq_some_iff.mp first
  obtain ⟨jbound, jeq⟩ := Array.getElem?_eq_some_iff.mp second
  rcases Nat.lt_trichotomy i j with before | equal | after
  · have relation := List.Pairwise.rel_getElem_of_lt
      (by simpa using ibound) (by simpa using jbound) pairs before
    simp only [Array.getElem_toList, ieq, jeq] at relation
    exact False.elim (relation bi rfl bi rfl rfl)
  · exact equal
  · have relation := List.Pairwise.rel_getElem_of_lt
      (by simpa using jbound) (by simpa using ibound) pairs after
    simp only [Array.getElem_toList, ieq, jeq] at relation
    exact False.elim (relation bi rfl bi rfl rfl)

/-- The exact reverse-index suffix after a protected original node contains
only other valid source originals. This derives the structural alias-fold
condition from actual blockOrder, without adding an input checker. -/
theorem stock_blockOrder_backward_suffix_others {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0)
    {label owner : Nat} (defined : order.nodes[label]? = some (.original owner)) :
    ∀ k ∈ (Array.range label).reverse.toList, ∀ bi,
      order.nodes[k]! = .original bi → bi < f.blocks.length ∧ bi ≠ owner := by
  intro k member bi node
  have before : k < label := by
    simpa only [Array.toList_reverse, Array.toList_range, List.mem_reverse, List.mem_range] using member
  have labelBound := (Array.getElem?_eq_some_iff.mp defined).1
  have inside : k < order.nodes.size := Nat.lt_trans before labelBound
  have lookup : order.nodes[k]? = some (.original bi) := by
    rw [getElem!_pos order.nodes k inside] at node
    simp only [Array.getElem?_eq_getElem inside, node]
  have valid := (stock_blockOrder_originals_nodup run nonempty).2
  have projected : bi ∈ stockOriginals order.nodes := by
    unfold stockOriginals
    apply List.mem_filterMap.mpr
    exact ⟨.original bi, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩
  refine ⟨valid bi projected, ?_⟩
  intro eq
  subst bi
  have same := stock_blockOrder_original_unique run nonempty lookup defined
  omega

/-- Actual parallel source edges insert two critical nodes; the final original
has a nonempty reverse suffix containing those edges and the other original. -/
theorem stock_blockOrder_backward_suffix_others_witness :
    blockOrder parallelFunction = .ok parallelOrder ∧
    parallelOrder.nodes[3]? = some (.original 1) ∧
    (Array.range 3).reverse.toList = [2, 1, 0] ∧
    (∀ k ∈ (Array.range 3).reverse.toList, ∀ bi,
      parallelOrder.nodes[k]! = .original bi → bi < parallelFunction.blocks.length ∧ bi ≠ 1) := by
  have run : blockOrder parallelFunction = .ok parallelOrder := by cbv
  refine ⟨run, rfl, ?_, stock_blockOrder_backward_suffix_others run (by decide) rfl⟩
  simp only [Array.toList_reverse, Array.toList_range]
  rfl

/-- Two actual lookups of the same original in an edge-expanded order inhabit
both successful lookup premises of the uniqueness result. -/
theorem stock_blockOrder_original_unique_witness :
    blockOrder parallelFunction = .ok parallelOrder ∧
    parallelOrder.nodes[3]? = some (.original 1) ∧
    (∀ j, parallelOrder.nodes[j]? = some (.original 1) → j = 3) := by
  have run : blockOrder parallelFunction = .ok parallelOrder := by cbv
  exact ⟨run, rfl, fun _ lookup => stock_blockOrder_original_unique run (by decide) lookup rfl⟩

end Backend.Stock.Proof

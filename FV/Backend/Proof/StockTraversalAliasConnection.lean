import FV.Backend.Proof.StockNodeAliasConnection
import FV.Backend.Proof.StockSourceOrder
import FV.Backend.Proof.StockBackwardSuffixSplit

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- A successful actual traversal suffix preserves the protected source alias
once its own original block is excluded. Every remaining node is executed; the
proof derives reservations at successive steps from actual allocation bounds. -/
theorem stock_lowerNodes_other_aliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {owner ownerBlock x key : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    {first : Clif.Block} {owned : Nat × Nat}
    (firstBlock : f.blocks[ownerBlock]? = some first)
    (firstRange : ranges[ownerBlock]? = some owned)
    (ownerLower : owned.1 ≤ owner) (ownerUpper : owner < owned.2)
    {order : Order} {params labels : List Nat} {input output : DriverState}
    (other : ∀ label ∈ labels, ∀ bi, order.nodes[label]! = .original bi →
      bi < f.blocks.length ∧ bi ≠ ownerBlock)
    (bound : input.state.alias.size ≤ initial.base.nextVreg ∧
      initial.base.nextVreg ≤ input.state.base.nextVreg ∧ input.state.tryRegs = initial.tryRegs)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    (output.state.alias[key]?).join = (input.state.alias[key]?).join := by
  obtain ⟨original, st0, old, spec, view⟩ := buildCtx_source build
  induction labels generalizing input with
  | nil => simp only [List.foldlM_nil, pure, Except.pure] at run; cases run; rfl
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok middle =>
      simp only [call, bind, Except.bind] at run
      have nextBound := stock_lowerNode_allocationBounds build bound call
      have tail := ih (fun l mem => other l (List.mem_cons_of_mem _ mem)) nextBound run
      have step : (middle.state.alias[key]?).join = (input.state.alias[key]?).join := by
        cases node : order.nodes[label]! with
        | edge pred k target => rw [stock_lowerNode_edge_alias node call]
        | original bi =>
          obtain ⟨inside, different⟩ := other label (List.mem_cons_self) bi node
          have secondBlock : f.blocks[bi]? = some f.blocks[bi] := by simp [inside]
          have secondRange := spec.ranges bi f.blocks[bi] secondBlock
          exact stock_lowerNode_other_aliasEntry build ssa definition result mapped
            firstBlock secondBlock different.symm firstRange secondRange ownerLower ownerUpper
            node bound.2.2 call
      exact tail.trans step

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- The actual backward node suffix preserves a previously recorded source
alias. Node exclusion is derived from successful blockOrder, not assumed by the
caller, and intermediate reservations are derived from actual transitions. -/
theorem stock_lowerNodes_backward_aliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {owner ownerBlock x key : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    {first : Clif.Block} {owned : Nat × Nat}
    (firstBlock : f.blocks[ownerBlock]? = some first)
    (firstRange : ranges[ownerBlock]? = some owned)
    (ownerLower : owned.1 ≤ owner) (ownerUpper : owner < owned.2)
    {order : Order} (ordered : blockOrder f = .ok order)
    (nonempty : f.blocks.length ≠ 0) {label : Nat}
    (node : order.nodes[label]? = some (.original ownerBlock))
    {params : List Nat} {input output : DriverState}
    (bound : input.state.alias.size ≤ initial.base.nextVreg ∧
      initial.base.nextVreg ≤ input.state.base.nextVreg ∧ input.state.tryRegs = initial.tryRegs)
    (run : (Array.range label).reverse.toList.foldlM
      (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    (output.state.alias[key]?).join = (input.state.alias[key]?).join :=
  stock_lowerNodes_other_aliasEntry build ssa definition result mapped firstBlock firstRange
    ownerLower ownerUpper (stock_blockOrder_backward_suffix_others ordered nonempty node) bound run

/-- Before lowering a source definition's own node, its mapped register has no
alias. Actual reverse order excludes the owner from the successful prefix, and
the actual allocated initial state supplies the empty alias map and bounds. -/
theorem stock_lowerNodes_prefix_noAlias {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {owner ownerBlock x key : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    {first : Clif.Block} {owned : Nat × Nat}
    (firstBlock : f.blocks[ownerBlock]? = some first)
    (firstRange : ranges[ownerBlock]? = some owned)
    (ownerLower : owned.1 ≤ owner) (ownerUpper : owner < owned.2)
    {order : Order} (ordered : blockOrder f = .ok order)
    (nonempty : f.blocks.length ≠ 0) {label : Nat} {earlier suffix : List Nat}
    (node : order.nodes[label]? = some (.original ownerBlock))
    (split : (Array.range order.nodes.size).reverse.toList = earlier ++ label :: suffix)
    {params : List Nat} {input output : DriverState} (start : input.state = initial)
    (run : earlier.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    (output.state.alias[key]?).join = none := by
  obtain ⟨original, st0, requests, _, _, allocated⟩ := buildCtx_allocation build
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) allocated
  change initial = _ at state
  have empty : initial.alias = #[] := by rw [state]; rfl
  have bound : input.state.alias.size ≤ initial.base.nextVreg ∧
      initial.base.nextVreg ≤ input.state.base.nextVreg ∧ input.state.tryRegs = initial.tryRegs := by
    rw [start, empty]
    exact ⟨Nat.zero_le _, Nat.le_refl _, rfl⟩
  have kept := stock_lowerNodes_other_aliasEntry build ssa definition result mapped
    firstBlock firstRange ownerLower ownerUpper
    (stock_blockOrder_backward_prefix_others ordered nonempty node split) bound run
  simpa only [start, empty, Array.getElem?_empty, Option.join_none] using kept

private def suffixFunction : Clif.Function := {
  name := "actual_order_alias_suffix"
  sig := {}
  blocks := [
    { id := 7, params := [], body := [⟨[0], .iconst .i64 7⟩], term := .jump ⟨9, []⟩ },
    { id := 9, params := [], body := [⟨[1], .iconst .i64 9⟩], term := .ret [] }] }
private def suffixBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx suffixFunction).toOption.getD (sinkCtx, #[], sinkState)
private def suffixOrder : Order := ⟨#[.original 0, .original 1], #[#[1], #[]]⟩
private def suffixInput : DriverState := {
  state := { suffixBuilt.2.2 with
    base := (suffixBuilt.2.2.base.fresh .int).2
    alias := aliasStep #[] (193, 194) }
  blocks := Array.replicate 2 default
  edgeArgs := Array.replicate 2 #[]
  schedule := #[]
  scans := #[]
  blockScans := #[]
  rules := #[] }
private def suffixCall := (Array.range 1).reverse.toList.foldlM
  (fun d label => lowerNode suffixBuilt.1 suffixBuilt.2.1 suffixOrder suffixFunction [] label d)
  suffixInput
private theorem suffix_build : Stock.buildCtx suffixFunction = .ok suffixBuilt := rfl
private theorem suffix_order : blockOrder suffixFunction = .ok suffixOrder := by cbv
private theorem suffix_success : suffixCall.isOk = true := by decide +kernel
private theorem suffix_observed : suffixCall.toOption.map
    (fun d => (d.blocks[0]!.insts, d.blockScans.size)) = some (#[.jump 1], 1) := by decide +kernel

/-- A real two-block order and its nonempty reverse suffix execute the other
block's jump and two scans, preserving a nonempty protected alias. The incoming
state is chosen; this witness does not assert reachability from Stock.lower. -/
theorem stock_lowerNodes_backward_aliasEntry_witness :
    blockOrder suffixFunction = .ok suffixOrder ∧
    ∃ output, suffixCall = .ok output ∧ output.blocks[0]!.insts = #[.jump 1] ∧
      output.blockScans.size = 1 ∧ (output.state.alias[193]?).join = some 194 := by
  refine ⟨suffix_order, ?_⟩
  cases call : suffixCall with
  | error e => have success := suffix_success; simp only [call, Except.isOk] at success; cases success
  | ok output =>
    have observation := suffix_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observation
    have kept := stock_lowerNodes_backward_aliasEntry
      (ctx := suffixBuilt.1) (ranges := suffixBuilt.2.1) (initial := suffixBuilt.2.2)
      (owner := 2) (ownerBlock := 1) (x := 1) (key := 193)
      (info := infoOf suffixFunction ⟨[1], .iconst .i64 9⟩)
      suffix_build (by decide) rfl (by decide) rfl
      (first := suffixFunction.blocks[1]!) (owned := (2, 4)) rfl rfl (by decide) (by decide)
      suffix_order (by decide) (label := 1) rfl (params := [])
      (input := suffixInput) (output := output) (by decide) call
    have entry : (suffixInput.state.alias[193]?).join = some 194 := by decide
    exact ⟨output, rfl, observation.1, observation.2, kept.trans entry⟩

/-- The same actual nonempty backward suffix supplies every condition of the
more general node-fold alias frame, through its actual-order specialization. -/
theorem stock_lowerNodes_other_aliasEntry_witness :
    ∃ output, suffixCall = .ok output ∧ output.blocks[0]!.insts = #[.jump 1] ∧
      output.blockScans.size = 1 ∧ (output.state.alias[193]?).join = some 194 :=
  stock_lowerNodes_backward_aliasEntry_witness.2

private def prefixInput : DriverState := {
  state := suffixBuilt.2.2
  blocks := Array.replicate 2 default
  edgeArgs := Array.replicate 2 #[]
  schedule := #[]
  scans := #[]
  blockScans := #[]
  rules := #[] }
private def prefixCall := ([1] : List Nat).foldlM
  (fun d label => lowerNode suffixBuilt.1 suffixBuilt.2.1 suffixOrder suffixFunction [] label d)
  prefixInput
private theorem prefix_success : prefixCall.isOk = true := by decide +kernel
private theorem prefix_observed : prefixCall.toOption.map
    (fun d => (d.blocks[1]!.insts, d.blockScans.size)) = some (#[.rets []], 1) := by decide +kernel

/-- The actual initial allocation and a successful nonempty owner-excluding
prefix execute the other block's return, leaving the first source result
without an alias before its owner node. -/
theorem stock_lowerNodes_prefix_noAlias_witness :
    Stock.buildCtx suffixFunction = .ok suffixBuilt ∧
    blockOrder suffixFunction = .ok suffixOrder ∧
    ∃ output, prefixCall = .ok output ∧ output.blocks[1]!.insts = #[.rets []] ∧
      output.blockScans.size = 1 ∧ (output.state.alias[192]?).join = none := by
  refine ⟨suffix_build, suffix_order, ?_⟩
  cases call : prefixCall with
  | error e => have success := prefix_success; simp only [call, Except.isOk] at success; cases success
  | ok output =>
    have observation := prefix_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observation
    have absent := stock_lowerNodes_prefix_noAlias
      (ctx := suffixBuilt.1) (ranges := suffixBuilt.2.1) (initial := suffixBuilt.2.2)
      (owner := 0) (ownerBlock := 0) (x := 0) (key := 192)
      (info := infoOf suffixFunction ⟨[0], .iconst .i64 7⟩)
      suffix_build (by decide) rfl (by decide) rfl
      (first := suffixFunction.blocks[0]!) (owned := (0, 2)) rfl rfl (by decide) (by decide)
      suffix_order (by decide) (label := 0) (earlier := [1]) (suffix := []) rfl (by simp only [Array.toList_reverse, Array.toList_range]; decide)
      (params := []) (input := prefixInput) (output := output) rfl call
    exact ⟨output, rfl, observation.1, observation.2, absent⟩

end Backend.Stock.Proof

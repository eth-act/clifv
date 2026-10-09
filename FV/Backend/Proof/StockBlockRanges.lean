import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem bsl_end_le : ∀ (blocks : List Clif.Block) (i j : Nat) (b : Clif.Block),
    blocks[i]? = some b → i < j → bsl blocks i + b.body.length + 1 ≤ bsl blocks j
  | [], i, j, b, lookup, before => by simp at lookup
  | first :: rest, 0, 0, b, lookup, before => by omega
  | first :: rest, 0, j + 1, b, lookup, before => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
    subst b
    rw [bsl_zero, bsl_cons]
    omega
  | first :: rest, i + 1, 0, b, lookup, before => by omega
  | first :: rest, i + 1, j + 1, b, lookup, before => by
    simp only [List.getElem?_cons_succ] at lookup
    have bound := bsl_end_le rest i j b lookup (by omega)
    rw [bsl_cons, bsl_cons]
    omega

/-- Real source block ranges are disjoint; terminator slots are included. -/
theorem stock_buildCtx_block_ranges_disjoint {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {i j : Nat} {first second : Clif.Block}
    (left : f.blocks[i]? = some first) (right : f.blocks[j]? = some second)
    (distinct : i ≠ j) {a b : Nat × Nat}
    (firstRange : ranges[i]? = some a) (secondRange : ranges[j]? = some b) :
    a.2 ≤ b.1 ∨ b.2 ≤ a.1 := by
  obtain ⟨original, st0, _, spec, _⟩ := buildCtx_source build
  have firstEq := spec.ranges i first left
  have secondEq := spec.ranges j second right
  rw [firstRange] at firstEq
  rw [secondRange] at secondEq
  cases firstEq
  cases secondEq
  rcases Nat.lt_or_gt_of_ne distinct with before | after
  · left
    exact bsl_end_le f.blocks i j first left before
  · right
    exact bsl_end_le f.blocks j i second right after

/-- A source definition's slot is outside every other block's actual scan interval. -/
theorem stock_buildCtx_other_block_slot {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {i j : Nat} {first second : Clif.Block}
    (left : f.blocks[i]? = some first) (right : f.blocks[j]? = some second)
    (distinct : i ≠ j) {a b : Nat × Nat}
    (firstRange : ranges[i]? = some a) (secondRange : ranges[j]? = some b)
    {owner scanned : Nat} (ownerLower : a.1 ≤ owner) (ownerUpper : owner < a.2)
    (scanLower : b.1 ≤ scanned) (scanUpper : scanned < b.2) : scanned ≠ owner := by
  have disjoint := stock_buildCtx_block_ranges_disjoint build left right distinct firstRange secondRange
  rcases disjoint with before | after <;> omega

/-- Membership in the driver's exact backward indices implies half-open bounds. -/
theorem stock_backward_indices_mem {start stop n : Nat}
    (member : n ∈ (((Array.range (stop - start)).map (start + ·)).reverse.toList)) :
    start ≤ n ∧ n < stop := by
  simp only [Array.toList_reverse, Array.toList_map, Array.toList_range,
    List.mem_reverse, List.mem_map, List.mem_range] at member
  obtain ⟨k, bound, rfl⟩ := member
  constructor <;> omega

/-- Actual backward scans in another source block cannot revisit a definition's slot. -/
theorem stock_buildCtx_other_block_indices {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {i j : Nat} {first second : Clif.Block}
    (left : f.blocks[i]? = some first) (right : f.blocks[j]? = some second)
    (distinct : i ≠ j) {a b : Nat × Nat}
    (firstRange : ranges[i]? = some a) (secondRange : ranges[j]? = some b)
    {owner : Nat} (ownerLower : a.1 ≤ owner) (ownerUpper : owner < a.2) :
    owner ∉ (((Array.range (b.2 - b.1)).map (b.1 + ·)).reverse.toList) := by
  intro member
  obtain ⟨low, high⟩ := stock_backward_indices_mem member
  exact stock_buildCtx_other_block_slot build left right distinct firstRange secondRange
    ownerLower ownerUpper low high rfl

private def rangesFunction : Clif.Function := {
  name := "disjoint_block_ranges"
  sig := { returns := [⟨.i64, .none, .normal⟩] }
  blocks := [
    { id := 7, params := [], body := [⟨[0], .iconst .i64 7⟩], term := .jump ⟨9, []⟩ },
    { id := 9, params := [], body := [⟨[1], .iconst .i64 9⟩], term := .ret [1] }] }
private def rangesBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx rangesFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem rangesBuild : Stock.buildCtx rangesFunction = .ok rangesBuilt := rfl

/-- Two actual nonempty blocks have adjacent half-open ranges, with distinct terminators. -/
theorem stock_buildCtx_block_ranges_disjoint_witness :
    Stock.buildCtx rangesFunction = .ok rangesBuilt ∧
    rangesBuilt.2.1 = #[(0, 2), (2, 4)] ∧
    (2 ≤ 2 ∨ 4 ≤ 0) := by
  refine ⟨rangesBuild, rfl, ?_⟩
  exact stock_buildCtx_block_ranges_disjoint rangesBuild (i := 0) (j := 1)
    rfl rfl (by decide) rfl rfl

/-- The definition in block0 cannot be revisited by block1's scan slots. -/
theorem stock_buildCtx_other_block_slot_witness :
    Stock.buildCtx rangesFunction = .ok rangesBuilt ∧
    (∀ scanned, 2 ≤ scanned → scanned < 4 → scanned ≠ 0) := by
  refine ⟨rangesBuild, ?_⟩
  intro scanned low high
  exact stock_buildCtx_other_block_slot rangesBuild (i := 0) (j := 1)
    rfl rfl (by decide) (a := (0, 2)) (b := (2, 4)) rfl rfl
    (owner := 0) (by decide) (by decide) low high

/-- Nonempty exact backward indices include both a body and terminator slot. -/
theorem stock_backward_indices_mem_witness :
    (3 : Nat) ∈ (((Array.range (4 - 2)).map (2 + ·)).reverse.toList) ∧
    2 ≤ (3 : Nat) ∧ (3 : Nat) < 4 := by
  have member : (3 : Nat) ∈ (((Array.range (4 - 2)).map (2 + ·)).reverse.toList) := by
    simp only [Array.toList_reverse, Array.toList_map, Array.toList_range]
    decide
  exact ⟨member, stock_backward_indices_mem member⟩

/-- The real second block's two backward scan slots exclude the first block's definition. -/
theorem stock_buildCtx_other_block_indices_witness :
    Stock.buildCtx rangesFunction = .ok rangesBuilt ∧
    (0 : Nat) ∉ (((Array.range (4 - 2)).map (2 + ·)).reverse.toList) := by
  refine ⟨rangesBuild, ?_⟩
  exact stock_buildCtx_other_block_indices rangesBuild (i := 0) (j := 1)
    rfl rfl (by decide) (a := (0, 2)) (b := (2, 4)) rfl rfl
    (owner := 0) (by decide) (by decide)

end Backend.Stock.Proof

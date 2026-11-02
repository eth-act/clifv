import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

/-- The instruction result table inherits unique source definitions from the
existing Dominated condition, independently of dense register allocation. -/
theorem stock_buildCtx_resultTable_nodup {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) :
    (ctx.insts.toList.flatMap (fun info => info.results)).Nodup := by
  obtain ⟨original, st0, old, _, view⟩ := buildCtx_source build
  obtain ⟨model, _, _, _⟩ := buildCtx_model old
  have table : (ctxModel f (maxVOf f)).2.2.1 = (instsOf f f.blocks).toArray := by
    unfold ctxModel
    rw [blockFold]
    simp only [Array.empty_append]
  rw [view.insts, congrArg Ctx.insts model, table]
  have results : (instsOf f f.blocks).flatMap (fun info => info.results) =
      f.blocks.flatMap (fun b => b.body.flatMap (fun stmt => stmt.results)) := by
    simp [instsOf, List.flatMap_assoc, List.flatMap_append, List.flatMap_map,
      infoOf, placeholder]
  rw [results]
  exact ssa.sublist (flatMap_sub (fun b : Clif.Block => b.params.map (·.1))
    (fun b => b.body.flatMap (fun stmt => stmt.results)) f.blocks)

/-- A successful actual context has no second instruction defining a value;
this uses the existing SSA input condition, without a new checker premise. -/
theorem stock_buildCtx_result_unique {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {i j x : Nat} {a b : IInfo}
    (first : ctx.insts[i]? = some a) (second : ctx.insts[j]? = some b)
    (defined : x ∈ a.results) (again : x ∈ b.results) : i = j := by
  have nd := stock_buildCtx_resultTable_nodup build ssa
  have pairs := (List.pairwise_flatMap.mp nd).2
  have hi : ctx.insts.toList[i]? = some a := by simpa using first
  have hj : ctx.insts.toList[j]? = some b := by simpa using second
  obtain ⟨ibound, ieq⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨jbound, jeq⟩ := List.getElem?_eq_some_iff.mp hj
  rcases Nat.lt_trichotomy i j with before | equal | after
  · have distinct := List.Pairwise.rel_getElem_of_lt ibound jbound pairs before
    rw [ieq, jeq] at distinct
    exact False.elim (distinct x defined x again rfl)
  · exact equal
  · have distinct := List.Pairwise.rel_getElem_of_lt jbound ibound pairs after
    rw [jeq, ieq] at distinct
    exact False.elim (distinct x again x defined rfl)

/-- Every other original instruction, including a missing/default slot, excludes
an already-defined source result. The driver must still show it visits each
original instruction once and that terminator overrides add no results. -/
theorem stock_buildCtx_other_results {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {i j x : Nat} {a : IInfo}
    (first : ctx.insts[i]? = some a) (defined : x ∈ a.results)
    (different : j ≠ i) : x ∉ ctx.insts[j]!.results := by
  intro member
  cases slot : ctx.insts[j]? with
  | none =>
    simp only [getElem!_def, slot] at member
    change x ∈ ([] : List Nat) at member
    cases member
  | some b =>
    have again : x ∈ b.results := by
      simpa only [getElem!_def, slot, Option.getD_some] using member
    exact different (stock_buildCtx_result_unique build ssa first slot defined again).symm

private theorem termCtx_results_subset (ctx : Ctx) (ti j : Nat) (data : V) :
    ((Driver.termCtx ctx ti data).insts[j]!.results).Sublist (ctx.insts[j]!.results) := by
  by_cases different : j ≠ ti
  · simp only [getElem!_def, termCtx_insts_ne different data]
    exact List.Sublist.refl _
  · have eq : j = ti := Classical.not_not.mp different
    subst j
    show ((ctx.insts.set! ti ⟨data, [], [], none⟩)[ti]!.results).Sublist _
    simp only [getElem!_def, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self]
    by_cases inside : ti < ctx.insts.size
    · simp only [inside, ite_true]
      exact List.nil_sublist _
    · simp only [inside, ite_false]
      exact List.nil_sublist _

/-- The real terminator context override introduces no new source results, so
existing source SSA exclusions survive that update without a placeholder premise. -/
theorem stock_buildCtx_term_other_results {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {i j ti x : Nat} {a : IInfo} (data : V)
    (first : ctx.insts[i]? = some a) (defined : x ∈ a.results)
    (different : j ≠ i) : x ∉ (Driver.termCtx ctx ti data).insts[j]!.results := by
  intro member
  exact stock_buildCtx_other_results build ssa first defined different
    ((termCtx_results_subset ctx ti j data).subset member)

private def ssaFunction : Clif.Function := {
  name := "source_ssa"
  sig := { params := [], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{
    id := 0
    params := []
    body := [⟨[0], .iconst .i64 7⟩, ⟨[1], .iconst .i64 9⟩]
    term := .ret [1] }] }
private def ssaBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx ssaFunction).toOption.getD (sinkCtx, #[], sinkState)
private def firstInfo : IInfo := infoOf ssaFunction ⟨[0], .iconst .i64 7⟩
private def secondInfo : IInfo := infoOf ssaFunction ⟨[1], .iconst .i64 9⟩
private theorem ssaBuild : Stock.buildCtx ssaFunction = .ok ssaBuilt := rfl
private theorem ssaInput : (valueDefs ssaFunction).Nodup := by decide
private theorem firstLookup : ssaBuilt.1.insts[0]? = some firstInfo := rfl
private theorem firstResult : (0 : Nat) ∈ firstInfo.results := by decide

/-- Two actual source definitions and a terminator placeholder inhabit the
result-table uniqueness proof; neither definition is omitted from the table. -/
theorem stock_buildCtx_resultTable_nodup_witness :
    Stock.buildCtx ssaFunction = .ok ssaBuilt ∧
    (valueDefs ssaFunction).Nodup ∧
    ssaBuilt.1.insts.toList.flatMap (fun info => info.results) = [0, 1] ∧
    (ssaBuilt.1.insts.toList.flatMap (fun info => info.results)).Nodup := by
  exact ⟨ssaBuild, ssaInput, rfl, stock_buildCtx_resultTable_nodup ssaBuild ssaInput⟩

/-- Source value0 has an actual defining instruction; every successful lookup
containing it identifies that same slot, while slot1 defines value1. -/
theorem stock_buildCtx_result_unique_witness :
    Stock.buildCtx ssaFunction = .ok ssaBuilt ∧
    (valueDefs ssaFunction).Nodup ∧
    ssaBuilt.1.insts[0]? = some firstInfo ∧ (0 : Nat) ∈ firstInfo.results ∧
    ssaBuilt.1.insts[1]? = some secondInfo ∧
    (∀ j b, ssaBuilt.1.insts[j]? = some b → (0 : Nat) ∈ b.results → j = 0) := by
  refine ⟨ssaBuild, ssaInput, firstLookup, firstResult, rfl, ?_⟩
  intro j b lookup member
  exact (stock_buildCtx_result_unique ssaBuild ssaInput firstLookup lookup firstResult member).symm

/-- The actual second definition, the terminator placeholder and a missing slot
all exclude the first result. This witnesses the distinct-index premises. -/
theorem stock_buildCtx_other_results_witness :
    Stock.buildCtx ssaFunction = .ok ssaBuilt ∧
    (valueDefs ssaFunction).Nodup ∧
    ssaBuilt.1.insts[0]? = some firstInfo ∧ (0 : Nat) ∈ firstInfo.results ∧
    ssaBuilt.1.insts[1]!.results = [1] ∧
    (0 : Nat) ∉ ssaBuilt.1.insts[1]!.results ∧
    (0 : Nat) ∉ ssaBuilt.1.insts[2]!.results ∧
    (0 : Nat) ∉ ssaBuilt.1.insts[999]!.results := by
  exact ⟨ssaBuild, ssaInput, firstLookup, firstResult, rfl,
    stock_buildCtx_other_results ssaBuild ssaInput firstLookup firstResult (by decide),
    stock_buildCtx_other_results ssaBuild ssaInput firstLookup firstResult (by decide),
    stock_buildCtx_other_results ssaBuild ssaInput firstLookup firstResult (by decide)⟩

/-- An actual three-slot context witnesses the terminator override; it keeps
slot1's result and clears the final placeholder, both excluding value0. -/
theorem stock_buildCtx_term_other_results_witness :
    Stock.buildCtx ssaFunction = .ok ssaBuilt ∧
    (valueDefs ssaFunction).Nodup ∧
    ssaBuilt.1.insts[0]? = some firstInfo ∧ (0 : Nat) ∈ firstInfo.results ∧
    (Driver.termCtx ssaBuilt.1 2 (.int 17)).insts[1]!.results = [1] ∧
    (Driver.termCtx ssaBuilt.1 2 (.int 17)).insts[2]!.results = [] ∧
    (0 : Nat) ∉ (Driver.termCtx ssaBuilt.1 2 (.int 17)).insts[1]!.results ∧
    (0 : Nat) ∉ (Driver.termCtx ssaBuilt.1 2 (.int 17)).insts[2]!.results := by
  exact ⟨ssaBuild, ssaInput, firstLookup, firstResult, rfl, rfl,
    stock_buildCtx_term_other_results ssaBuild ssaInput (.int 17) firstLookup firstResult (by decide),
    stock_buildCtx_term_other_results ssaBuild ssaInput (.int 17) firstLookup firstResult (by decide)⟩

end Backend.Stock.Proof

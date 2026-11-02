import FV.Backend.Proof.StockFreshAlias
import FV.Backend.Proof.StockAliasTerminal

/-! Availability along actual final source aliases. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem results_definition {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (ssa : (valueDefs f).Nodup)
    {i x : Nat} {info : IInfo} (lookup : ctx.insts[i]? = some info)
    (member : x ∈ info.results) : ctx.defInst? x = some i := by
  obtain ⟨original, before, old, spec, view⟩ := buildCtx_source build
  have oldLookup : original.insts[i]? = some info := by rw [← view.insts]; exact lookup
  have table : info ∈ original.insts.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldLookup)
  rcases spec.insts info table with placeholder | ⟨b, blockMember, stm, stmtMember, same⟩
  · rw [placeholder] at member; cases member
  · subst info
    obtain ⟨bi, block⟩ := List.getElem?_of_mem blockMember
    obtain ⟨j, statement⟩ := List.getElem?_of_mem stmtMember
    have defined := defInst_res spec.facts ssa block statement member
    obtain ⟨other, otherLookup, _, otherResults⟩ := spec.facts.stmt bi b j stm block statement
    have sourceLookup : ctx.insts[blockStart f bi + j]? = some other := by
      rw [view.insts]; exact otherLookup
    have equal := stock_buildCtx_result_unique build ssa lookup sourceLookup member
      (by simpa only [otherResults, infoOf] using member)
    rw [← equal] at defined
    simpa only [Ctx.defInst?, view.valDef] using defined

/-- Every actual final alias between source mappings follows the defining
instruction's operand provenance, including aliases to unaliased parameters. -/
theorem stock_lower_source_alias_provenance {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {x key y target : Nat}
    (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (targetMapped : result.ctx.valueReg? y = some (.vreg target .int))
    (entry : (result.final.alias[key]?).join = some target) :
    ∃ d, result.ctx.defInst? x = some d ∧ Prov result.ctx d y := by
  obtain ⟨event, record, step, info, inst, eventMem, recordMem,
    recorded, emitted, source, original, defines, installed⟩ :=
    stock_lower_source_alias_emitted_record run scope dominated.ssa mapped entry
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem
  have definition := results_definition build dominated.ssa source defines
  refine ⟨record.inst, definition, ?_⟩
  rcases stock_lower_emitted_record_finalAliasOrigins_noInherited run scope
      (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) dominated.ssa
      eventMem recordMem recorded emitted source original defines mapped target entry with
      fresh | ⟨z, reached, register⟩ | reserved
  · have sourceBound := (buildCtx_allocated build).1 y target targetMapped
    have frontier := stock_lower_blockScanInitialFrontier run event eventMem record recordMem
    omega
  · have equal := (buildCtx_allocated build).2.1 z y target register targetMapped
    subst z
    exact reached
  · exact (reserved.2.2 y targetMapped).elim

/-- Following any actual final source alias preserves the original source
availability at a chosen block/statement boundary. -/
theorem stock_lower_source_alias_available {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {bi j x key y target : Nat}
    (available : x ∈ availOf f (availIn f result.ctx) bi j)
    (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (targetMapped : result.ctx.valueReg? y = some (.vreg target .int))
    (entry : (result.final.alias[key]?).join = some target) :
    y ∈ availOf f (availIn f result.ctx) bi j := by
  obtain ⟨d, definition, reached⟩ := stock_lower_source_alias_provenance run scope dominated mapped targetMapped entry
  obtain ⟨event, eventMem, produced⟩ := stock_lower_source_alias_record run mapped entry
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, block, data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem
  exact stock_available_provenance build dominated available definition reached

private theorem entries_iff {a : Array (Option Nat)} {key target : Nat} :
    (key, target) ∈ finalAliasEntries a ↔ (a[key]?).join = some target := by
  constructor
  · intro member
    obtain ⟨n, _, mapped⟩ := List.mem_filterMap.mp member
    cases lookup : (a[n]?).join with
    | none => simp only [lookup, Option.map_none] at mapped; cases mapped
    | some value =>
      simp only [lookup, Option.map_some, Option.some.injEq, Prod.mk.injEq] at mapped
      rcases mapped with ⟨rfl, rfl⟩
      exact lookup
  · intro entry
    have inside : key < a.size := by
      apply Nat.lt_of_not_ge
      intro outside
      rw [Array.getElem?_eq_none outside] at entry
      cases entry
    exact List.mem_filterMap.mpr ⟨key, List.mem_range.mpr inside, by rw [entry]; rfl⟩

private theorem built_context {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∃ ranges, Stock.buildCtx f = .ok (result.ctx, ranges, result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  exact ⟨_, hbuild⟩

private theorem mapped_path_start {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {key endpoint y : Nat}
    (path : AliasPath (finalAliasEntries result.final.alias) key endpoint)
    (mapped : result.ctx.valueReg? y = some (.vreg endpoint .int)) :
    ∃ x, result.ctx.valueReg? x = some (.vreg key .int) := by
  cases path with
  | refl key => exact ⟨y, mapped⟩
  | step member tail =>
    have entry := entries_iff.mp member
    rcases stock_lower_alias_key_origin run entry with source | ⟨slot, rs, lookup, payload⟩
    · exact source
    · obtain ⟨owner, rets, allocated, returned⟩ := stock_lower_payload_aliasOrigin run lookup payload entry
      have absent := (stock_lower_reservedReturn_terminal run allocated returned).1
      cases tail with
      | refl =>
        obtain ⟨ranges, build⟩ := built_context run
        have separate := buildCtx_valueReservedDisjoint build y _ mapped owner rets allocated _
          (List.mem_append_left _ returned)
        exact (separate rfl).elim
      | step more rest =>
        have second := entries_iff.mp more
        rw [absent] at second
        cases second

/-- Any actual alias path between mapped source values stays within their
source availability, including paths ending at an unaliased parameter. -/
theorem stock_lower_source_path_available {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {bi j x key y endpoint : Nat}
    (available : x ∈ availOf f (availIn f result.ctx) bi j)
    (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (targetMapped : result.ctx.valueReg? y = some (.vreg endpoint .int))
    (path : AliasPath (finalAliasEntries result.final.alias) key endpoint) :
    y ∈ availOf f (availIn f result.ctx) bi j := by
  obtain ⟨ranges, build⟩ := built_context run
  induction path generalizing x with
  | refl key =>
    have equal := (buildCtx_allocated build).2.1 x y key mapped targetMapped
    subst x
    exact available
  | step member tail ih =>
    obtain ⟨z, nextMapped⟩ := mapped_path_start run tail targetMapped
    have nextAvailable := stock_lower_source_alias_available run scope dominated available mapped nextMapped
      (entries_iff.mp member)
    exact ih nextAvailable nextMapped targetMapped

private theorem terminal_path_refl {a : Array (Option Nat)} {key endpoint : Nat}
    (absent : (a[key]?).join = none) (path : AliasPath (finalAliasEntries a) key endpoint) : key = endpoint := by
  cases path with
  | refl => rfl
  | step member tail =>
    have entry := entries_iff.mp member
    rw [absent] at entry
    cases entry

private theorem reserved_path_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {slot key endpoint : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[slot]? = some rs) (member : (.vreg key .int) ∈ rs.1 ++ rs.2)
    (path : AliasPath (finalAliasEntries result.final.alias) key endpoint) :
    endpoint < result.initial.base.nextVreg := by
  obtain ⟨ranges, build⟩ := built_context run
  rcases List.mem_append.mp member with returned | payload
  · have absent := (stock_lower_reservedReturn_terminal run lookup returned).1
    have same := terminal_path_refl absent path
    obtain ⟨n, equal, bound⟩ := buildCtx_reservedBelow build slot rs lookup
      (.vreg key .int) (List.mem_append_left _ returned)
    have number : key = n := (Reg.vreg.inj equal).1
    omega
  · cases path with
    | refl =>
      obtain ⟨n, equal, bound⟩ := buildCtx_reservedBelow build slot rs lookup
        (.vreg key .int) (List.mem_append_right _ payload)
      have number : key = n := (Reg.vreg.inj equal).1
      omega
    | step edge tail =>
      have entry := entries_iff.mp edge
      obtain ⟨owner, rets, allocated, returned⟩ := stock_lower_payload_aliasOrigin run lookup payload entry
      have absent := (stock_lower_reservedReturn_terminal run allocated returned).1
      have same := terminal_path_refl absent tail
      obtain ⟨n, equal, bound⟩ := buildCtx_reservedBelow build owner rets allocated _
        (List.mem_append_left _ returned)
      have number := (Reg.vreg.inj equal).1
      omega

/-- An actual fresh alias endpoint comes from the allocation interval of a
retained source definition available at the chosen source boundary. -/
def AvailableFreshOrigin (f : Clif.Function) (result : Result) (bi j target : Nat) : Prop :=
  ∃ (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (x key : Nat),
    event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
    result.ctx.insts[record.inst]? = some info ∧ x ∈ info.results ∧
    result.ctx.valueReg? x = some (.vreg key .int) ∧
    x ∈ availOf f (availIn f result.ctx) bi j ∧
    record.input.base.nextVreg ≤ target ∧ target < record.output.state.base.nextVreg

/-- Following actual source aliases to a fresh endpoint preserves its source
producer's availability. This is the origin needed to exclude writes by a
not-yet-available source definition; no extra endpoint-origin premise is assumed. -/
theorem stock_lower_source_path_fresh_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {bi j x key endpoint : Nat}
    (available : x ∈ availOf f (availIn f result.ctx) bi j)
    (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (path : AliasPath (finalAliasEntries result.final.alias) key endpoint)
    (fresh : result.initial.base.nextVreg ≤ endpoint) : AvailableFreshOrigin f result bi j endpoint := by
  obtain ⟨ranges, build⟩ := built_context run
  induction path generalizing x with
  | refl key =>
    have below := (buildCtx_allocated build).1 x key mapped
    omega
  | @step start next finish member tail ih =>
    have entry := entries_iff.mp member
    obtain ⟨event, record, step, info, inst, eventMem, recordMem,
      recorded, emitted, source, original, defines, installed⟩ :=
      stock_lower_source_alias_emitted_record run scope dominated.ssa mapped entry
    rcases stock_lower_emitted_record_finalAliasOrigins_noInherited run scope
        (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) dominated.ssa eventMem recordMem
        recorded emitted source original defines mapped _ entry with
        allocated | ⟨y, reached, targetMapped⟩ | reserved
    · have initialBound := stock_lower_blockScanInitialFrontier run event eventMem record recordMem
      have absent := (stock_lower_freshAlias_terminal run (Nat.le_trans initialBound allocated.1)).1
      have same := terminal_path_refl absent tail
      rw [← same]
      exact ⟨event, record, info, x, _, eventMem, recordMem, source, defines, mapped, available, allocated⟩
    · have nextAvailable := stock_lower_source_alias_available run scope dominated available mapped targetMapped entry
      exact ih nextAvailable targetMapped fresh
    · cases lookup : result.initial.tryRegs[event.termInst]? with
      | none => simp only [getElem!_def, lookup] at reserved; cases reserved.1
      | some rs =>
        have slotMember : (Reg.vreg next .int) ∈ rs.1 ++ rs.2 := by
          simpa only [getElem!_def, lookup, Option.getD_some] using reserved.1
        have below := reserved_path_below run lookup slotMember tail
        omega

private def parameterFunction : Clif.Function := {
  name := "source_parameter_alias_available"
  sig := {params := [⟨.i64, .none, .normal⟩], returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV}
  blocks := [{id := 0, params := [(0, .i64)], body := [⟨[1], .ireduce .i8 0⟩], term := .ret [1]}] }
private theorem parameterScope : LowerScope parameterFunction := lowerScope_of (by decide +kernel)
private theorem parameterDominated : Dominated parameterFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [parameterFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j with
        | zero =>
          simp at statement
          subst stm
          change y ∈ [0] at member
          simp only [List.mem_singleton] at member; subst y
          change 0 ∈ ([0] ++ (availIn parameterFunction ctx).getD 0 [] ++ []).filter
            (fun x => decide (x ∉ [1]))
          simp
        | succ j => simp at statement
      · intro y member
        change y ∈ [1] at member
        simp only [List.mem_singleton] at member; subst y
        change 1 ∈ ([0] ++ (availIn parameterFunction ctx).getD 0 [] ++ [1]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    | succ bi => simp [parameterFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have candidate := (inFix_fixOk (f := parameterFunction) (ctx := ctx) (gn := id)).cand tl x available
    have small : tl < 1 := by simpa only [parameterFunction, List.length_cons, List.length_nil] using candidate.2.1
    omega

private theorem parameterAvailable (ctx : Ctx) :
    (1 : Nat) ∈ availOf parameterFunction (availIn parameterFunction ctx) 0 1 := by
  change 1 ∈ ([0] ++ (availIn parameterFunction ctx).getD 0 [] ++ [1]).filter
    (fun x => decide (x ∉ ([] : List Nat)))
  simp

set_option maxRecDepth 20000 in
private theorem parameterObserved : (Stock.lower parameterFunction).toOption.map (fun result =>
    (result.ctx.valueReg? 1, result.ctx.valueReg? 0,
      (result.final.alias[193]?).join, (result.final.alias[192]?).join)) =
    some (some (.vreg 193 .int), some (.vreg 192 .int), some 192, none) := by
  decide +kernel

/-- A real reduction aliases its result193 to the unaliased parameter192.
The original source availability and actual one-edge path are inhabited, and
all three source provenance/availability results are instantiated together. -/
theorem stock_lower_source_alias_available_witness :
    ∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      result.ctx.valueReg? 1 = some (.vreg 193 .int) ∧ result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (result.final.alias[193]?).join = some 192 ∧ (result.final.alias[192]?).join = none ∧
      (∃ d, result.ctx.defInst? 1 = some d ∧ Prov result.ctx d 0) ∧
      (1 : Nat) ∈ availOf f (availIn f result.ctx) 0 1 ∧
      (0 : Nat) ∈ availOf f (availIn f result.ctx) 0 1 ∧
      AliasPath (finalAliasEntries result.final.alias) 193 192 ∧
      (0 : Nat) ∈ availOf f (availIn f result.ctx) 0 1 := by
  have observed := parameterObserved
  cases run : Stock.lower parameterFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨mapped, targetMapped, entry, absent⟩ := observed
    have path : AliasPath (finalAliasEntries result.final.alias) 193 192 :=
      .step (entries_iff.mpr entry) (.refl 192)
    have available := parameterAvailable result.ctx
    exact ⟨parameterFunction, result, run, parameterScope, parameterDominated, mapped, targetMapped, entry, absent,
      stock_lower_source_alias_provenance run parameterScope parameterDominated mapped targetMapped entry,
      available, stock_lower_source_alias_available run parameterScope parameterDominated available mapped targetMapped entry,
      path, stock_lower_source_path_available run parameterScope parameterDominated available mapped targetMapped path⟩

private def freshFunction : Clif.Function := {
  name := "available_fresh_origin"
  sig := {returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV}
  blocks := [{id := 0, body := [⟨[0], .iconst .i8 7⟩], term := .ret [0]}] }
private theorem freshScope : LowerScope freshFunction := lowerScope_of (by decide +kernel)
private theorem freshDominated : Dominated freshFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [freshFunction] at block; subst b
      constructor
      · intro j stm statement y member
        cases j with
        | zero => simp at statement; subst stm; simp [Backend.Proof.Driver.instArgs] at member
        | succ j => simp at statement
      · intro y member
        change y ∈ [0] at member
        simp only [List.mem_singleton] at member; subst y
        change 0 ∈ ((availIn freshFunction ctx).getD 0 [] ++ [0]).filter (fun x => decide (x ∉ ([] : List Nat)))
        simp
    | succ bi => simp [freshFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    cases tl <;> simp [parsOf, freshFunction]
private theorem freshAvailable (ctx : Ctx) :
    (0 : Nat) ∈ availOf freshFunction (availIn freshFunction ctx) 0 1 := by
  change 0 ∈ ((availIn freshFunction ctx).getD 0 [] ++ [0]).filter (fun x => decide (x ∉ ([] : List Nat)))
  simp
set_option maxRecDepth 20000 in
private theorem freshObserved : (Stock.lower freshFunction).toOption.map (fun result =>
    (result.ctx.valueReg? 0, result.initial.base.nextVreg, (result.final.alias[192]?).join)) =
    some (some (.vreg 192 .int), 193, some 193) := by
  decide +kernel

/-- A complete actual constant lowering supplies an available source value,
its installed fresh alias and the allocation origin of the reached endpoint. -/
theorem stock_lower_source_path_fresh_origin_witness :
    ∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      result.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (result.final.alias[192]?).join = some 193 ∧ result.initial.base.nextVreg ≤ 193 ∧
      (0 : Nat) ∈ availOf f (availIn f result.ctx) 0 1 ∧
      AliasPath (finalAliasEntries result.final.alias) 192 193 ∧
      AvailableFreshOrigin f result 0 1 193 := by
  have observed := freshObserved
  cases run : Stock.lower freshFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨mapped, initial, entry⟩ := observed
    have path : AliasPath (finalAliasEntries result.final.alias) 192 193 := .step (entries_iff.mpr entry) (.refl 193)
    have available := freshAvailable result.ctx
    have fresh : result.initial.base.nextVreg ≤ 193 := Nat.le_of_eq initial
    exact ⟨freshFunction, result, run, freshScope, freshDominated, mapped, entry, fresh, available, path,
      stock_lower_source_path_fresh_origin run freshScope freshDominated available mapped path fresh⟩

end Backend.Stock.Proof

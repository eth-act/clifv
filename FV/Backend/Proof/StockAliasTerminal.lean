import FV.Backend.Proof.StockPayloadAliasOrigins
import FV.Backend.Proof.StockAliasDomain

/-! The actual finite-fuel final resolver reaches endpoints and respects edges.
Combine source rank, key-domain construction and reserved payload endpoints. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Nonempty entries of the actual alias array, with their array indices. -/
def finalAliasEntries (a : Array (Option Nat)) : List (Nat × Nat) :=
  (List.range a.size).filterMap fun key => (a[key]?).join.map (key, ·)

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

private theorem entries_faithful (a : Array (Option Nat)) :
    Faithful (finalAliasEntries a) (fun key => (a[key]?).join) := by
  constructor
  · intro key target entry; exact entries_iff.mpr entry
  · intro key absent target member
    have entry := entries_iff.mp member
    rw [absent] at entry
    cases entry

private noncomputable def finalRank (result : Result) (key : Nat) : Nat := by
  classical
  exact if source : ∃ x, result.ctx.valueReg? x = some (.vreg key .int) then
    sourceAliasRank result.ctx (Classical.choose source) + 2 else 1

private theorem source_rank {result : Result} (injective : ValueMapInjective result.ctx)
    {x key : Nat} (mapped : result.ctx.valueReg? x = some (.vreg key .int)) :
    finalRank result key = sourceAliasRank result.ctx x + 2 := by
  classical
  unfold finalRank
  split
  · rename_i source
    have equal := injective (Classical.choose source) x key (Classical.choose_spec source) mapped
    rw [equal]
  · rename_i absent
    exact (absent ⟨x, mapped⟩).elim

private theorem rank_decreases {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {key target next : Nat} (entry : (result.final.alias[key]?).join = some target)
    (targetEntry : (result.final.alias[target]?).join = some next) :
    finalRank result target < finalRank result key := by
  classical
  rcases stock_lower_alias_key_origin run entry with ⟨x, mapped⟩ | ⟨slot, rs, lookup, member⟩
  · obtain ⟨event, eventMem, produced⟩ := stock_lower_source_alias_record run mapped entry
    obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
      label, bi, data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem
    have injective := (buildCtx_allocated build).2.1
    rw [source_rank injective mapped]
    by_cases source : ∃ y, result.ctx.valueReg? y = some (.vreg target .int)
    · obtain ⟨y, targetMapped⟩ := source
      rw [source_rank injective targetMapped]
      have decrease := stock_lower_final_source_chain_rank run scope dominated
        (FinalSourcePath.single ⟨key, target, next, mapped, targetMapped, entry, targetEntry⟩)
      omega
    · simp only [finalRank, source, dite_false]
      omega
  · obtain ⟨owner, rets, allocated, returned⟩ := stock_lower_payload_aliasOrigin run lookup member entry
    have absent := (stock_lower_reservedReturn_terminal run allocated returned).1
    rw [absent] at targetEntry
    cases targetEntry

/-- Actual final aliases are well founded under the unchanged input conditions. -/
theorem stock_lower_alias_wellFounded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) :
    AliasWF (finalAliasEntries result.final.alias) := by
  refine ⟨finalRank result, ?_⟩
  intro p member q other equal
  have first := entries_iff.mp member
  have second := entries_iff.mp other
  rw [equal] at second
  exact rank_decreases run scope dominated first second

private theorem resolver_path {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (key : Nat) :
    AliasPath (finalAliasEntries result.final.alias) key (aliasNum result.final.alias key) ∧
      (result.final.alias[aliasNum result.final.alias key]?).join = none := by
  obtain ⟨rank, decrease⟩ := stock_lower_alias_wellFounded run scope dominated
  have contains : ∀ p ∈ finalAliasEntries result.final.alias,
      p.1 ∈ List.range result.final.alias.size := by
    intro p member
    obtain ⟨key, inside, mapped⟩ := List.mem_filterMap.mp member
    cases lookup : (result.final.alias[key]?).join with
    | none => simp only [lookup, Option.map_none] at mapped; cases mapped
    | some target =>
      simp only [lookup, Option.map_some, Option.some.injEq] at mapped
      subst p
      exact inside
  have count := chainCount_le (finalAliasEntries result.final.alias) rank
    (List.range result.final.alias.size) key
  simp only [List.length_range] at count
  exact chaseF_end (entries_faithful result.final.alias) decrease contains
    (result.final.alias.size + 1) key (by omega)

/-- The exact size+1 resolver used by production emission reaches an unaliased
endpoint for every key. No supplied resolver/chain certificate is required. -/
theorem stock_lower_alias_terminal {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (key : Nat) : (result.final.alias[aliasNum result.final.alias key]?).join = none :=
  (resolver_path run scope dominated key).2

/-- Resolving a final endpoint again leaves it unchanged. -/
theorem stock_lower_alias_idempotent {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (key : Nat) : aliasNum result.final.alias (aliasNum result.final.alias key) =
      aliasNum result.final.alias key :=
  chaseF_none (stock_lower_alias_terminal run scope dominated key) _

private theorem path_unique {a : Array (Option Nat)} {key endpoint other : Nat}
    (path : AliasPath (finalAliasEntries a) key endpoint) (terminal : (a[endpoint]?).join = none)
    (otherPath : AliasPath (finalAliasEntries a) key other) (otherTerminal : (a[other]?).join = none) :
    endpoint = other := by
  induction path generalizing other with
  | refl key =>
    cases otherPath with
    | refl => rfl
    | step member tail =>
      have entry := entries_iff.mp member
      rw [terminal] at entry
      cases entry
  | step member tail ih =>
    cases otherPath with
    | refl =>
      have entry := entries_iff.mp member
      rw [otherTerminal] at entry
      cases entry
    | step otherMember otherTail =>
      have equal := Option.some.inj ((entries_iff.mp member).symm.trans (entries_iff.mp otherMember))
      subst equal
      exact ih terminal otherTail otherTerminal

/-- Both ends of each actual final alias resolve to the same endpoint, even
though their finite-fuel chases begin at different positions in the chain. -/
theorem stock_lower_alias_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {key target : Nat} (entry : (result.final.alias[key]?).join = some target) :
    aliasNum result.final.alias key = aliasNum result.final.alias target := by
  have first := resolver_path run scope dominated key
  have second := resolver_path run scope dominated target
  exact path_unique first.1 first.2 (.step (entries_iff.mpr entry) second.1) second.2

/-- Transport an already-held value through every actual final alias edge,
including source chains. Execution establishing the value remains separate. -/
theorem stock_lower_alias_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {key target : Nat} (entry : (result.final.alias[key]?).join = some target)
    {regs : Nat → CV} {value : Clif.Val}
    (held : VHolds value (regs (aliasNum result.final.alias target))) :
    VHolds value (regs (aliasNum result.final.alias key)) := by
  rw [stock_lower_alias_step run scope dominated entry]
  exact held

/-- A complete constant/two-reduction run supplies a nonempty three-edge
alias chain. Well-foundedness, actual resolver endpoints/idempotence, edge
agreement and already-held value transport are inhabited together. -/
theorem stock_lower_alias_terminal_witness :
    ∃ (f : Clif.Function) (result : Result) (regs : Nat → CV),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      (result.final.alias[194]?).join = some 193 ∧
      (result.final.alias[193]?).join = some 192 ∧
      (result.final.alias[192]?).join = some 195 ∧
      AliasWF (finalAliasEntries result.final.alias) ∧
      (∀ key, (result.final.alias[aliasNum result.final.alias key]?).join = none) ∧
      (∀ key, aliasNum result.final.alias (aliasNum result.final.alias key) = aliasNum result.final.alias key) ∧
      aliasNum result.final.alias 194 = aliasNum result.final.alias 193 ∧
      VHolds (.ofInt .i8 7) (regs (aliasNum result.final.alias 193)) ∧
      VHolds (.ofInt .i8 7) (regs (aliasNum result.final.alias 194)) := by
  obtain ⟨f, result, scope, dominated, run, first, second, fresh, edge2, edge1, path, rank1, rank2, noCycle⟩ :=
    stock_recorded_source_chain_witness
  let regs : Nat → CV := fun _ => BitVec.ofNat 128 7
  have held : VHolds (.ofInt .i8 7) (regs (aliasNum result.final.alias 193)) := rfl
  exact ⟨f, result, regs, run, scope, dominated, first, second, fresh,
    stock_lower_alias_wellFounded run scope dominated,
    stock_lower_alias_terminal run scope dominated,
    stock_lower_alias_idempotent run scope dominated,
    stock_lower_alias_step run scope dominated first, held,
    stock_lower_alias_value run scope dominated first held⟩

end Backend.Stock.Proof

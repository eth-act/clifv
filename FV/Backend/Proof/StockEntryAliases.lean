module

public import FV.Backend.Proof.StockAliasAvailable

@[expose] public section

/-! Original inherited values remain disjoint from successor parameter writes,
including through actual nonempty final alias paths. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

private theorem chase_path (a : Array (Option Nat)) (fuel : Nat) :
    ∀ key,AliasPath (finalAliasEntries a) key (chaseF (fun n => (a[n]?).join) fuel key) := by
  induction fuel with
  | zero => intro key; exact .refl key
  | succ fuel ih =>
    intro key
    cases lookup : (a[key]?).join with
    | none => simpa only [chaseF,lookup] using (AliasPath.refl (al := finalAliasEntries a) key)
    | some target =>
      simpa only [chaseF,lookup] using (AliasPath.step (entries_iff.mpr lookup) (ih target))

private theorem entry_path {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {tl x key y endpoint : Nat} (incoming : x ∈ (availIn f result.ctx).getD tl [])
    (notLocal : x ∉ defsOf f tl) (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (targetMapped : result.ctx.valueReg? y = some (.vreg endpoint .int))
    (path : AliasPath (finalAliasEntries result.final.alias) key endpoint) :
    y ∈ (availIn f result.ctx).getD tl [] ∧ y ∉ defsOf f tl := by
  obtain ⟨ranges,build⟩ := built_context run
  induction path generalizing x with
  | refl key =>
    have same := (buildCtx_allocated build).2.1 x y key mapped targetMapped
    subst x
    exact ⟨incoming,notLocal⟩
  | step member tail ih =>
    obtain ⟨z,nextMapped⟩ := mapped_path_start run tail targetMapped
    obtain ⟨d,definition,reached⟩ := stock_lower_source_alias_provenance run scope dominated mapped nextMapped
      (entries_iff.mp member)
    have next := stock_entry_available_provenance build dominated incoming notLocal definition reached
    exact ih next.1 next.2 nextMapped targetMapped

private theorem parameter_resolve {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (ssa : (valueDefs f).Nodup)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b) {y key : Nat}
    (parameter : y ∈ b.params.map (·.1)) (mapped : result.ctx.valueReg? y = some (.vreg key .int)) :
    aliasNum result.final.alias key = key := by
  obtain ⟨ranges,build⟩ := built_context run
  obtain ⟨original,st0,sourceBuild,spec,view⟩ := buildCtx_source build
  have old := defInst_par spec.facts ssa block parameter
  have undefined : result.ctx.defInst? y = none := by simpa only [Ctx.defInst?,view.valDef] using old
  exact (stock_lower_undefinedSource_terminal run ssa undefined mapped).2

/-- An inherited available value cannot resolve to any successor parameter's
resolved register. Actual alias provenance and original parameter-freedom
derive the separation needed by outgoing parallel-copy frame proofs. -/
theorem stock_lower_entry_alias_apart {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b)
    {x key y parameterKey : Nat} (available : x ∈ availOf f (availIn f result.ctx) tl 0)
    (notParameter : x ∉ b.params.map (·.1)) (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (parameter : y ∈ b.params.map (·.1)) (targetMapped : result.ctx.valueReg? y = some (.vreg parameterKey .int)) :
    aliasNum result.final.alias key ≠ aliasNum result.final.alias parameterKey := by
  rw [parameter_resolve run dominated.ssa block parameter targetMapped]
  intro equal
  obtain ⟨present,noFuture⟩ := (mem_av block).mp available
  have incoming : x ∈ (availIn f result.ctx).getD tl [] := by
    rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
    · exact False.elim (notParameter parameter)
    · exact incoming
    · omega
  have notLocal : x ∉ defsOf f tl := by
    intro localDef
    obtain ⟨original,j,stm,found,statement,defines⟩ := mem_defsOf.mp localDef
    cases Option.some.inj (found.symm.trans block)
    exact noFuture ⟨j,stm,Nat.zero_le _,statement,defines⟩
  have path : AliasPath (finalAliasEntries result.final.alias) key parameterKey := by
    rw [← equal]
    exact chase_path result.final.alias (result.final.alias.size+1) key
  have inherited := entry_path run scope dominated incoming notLocal mapped targetMapped path
  have absent := (inFix_fixOk (f := f) (ctx := result.ctx) (gn := id)).cand tl y inherited.1
  exact (absent.2.2.2.2.1) (by rwa [parsOf_of block])

/-- Every original source block parameter remains fixed by the actual final
alias resolver, under the unchanged original SSA condition. -/
theorem stock_lower_parameter_resolves {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (ssa : (valueDefs f).Nodup)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b) {y key : Nat}
    (parameter : y ∈ b.params.map (·.1)) (mapped : result.ctx.valueReg? y = some (.vreg key .int)) :
    aliasNum result.final.alias key = key := parameter_resolve run ssa block parameter mapped
end Backend.Stock.Proof

import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.StockAvailableValues
import FV.Backend.Proof.StockScanSemantics

/-! Source consistency across actual retained Stock statements. The proof uses
only the original SSA/dominance and context construction facts. It covers every
successful ordinary source instruction, including memory effects; it makes no
claim about execution of its selected machine code or deferred traps. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem view_avail {ctx original : Ctx} (view : DFGViewEq ctx original)
    (f : Clif.Function) : availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs, Ctx.defInst?, view.valDef, view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers, usersN, args, view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0, view.valDef, bytes, args]
  simp only [availIn, inFix_eq, users, bytes, work, view.valDef]

/-- A successful original statement preserves restricted DFG consistency and
frame typing in the actual Stock scan context. This includes effectful source
steps: only pure definitions are re-evaluated by `DFGCons`. -/
theorem stock_lower_source_step_dfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (func : fr.func = f)
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (step : SourceInstResult env cp event.ctx record.inst (fr, cm) (fr', cm')) :
    DFGCons event.ctx (restrict fr' (availOf f (availIn f result.ctx) bi (j + 1))) := by
  obtain ⟨info, inst, vals, regs, rest, source, clif, body, outcome, set, frame⟩ := step
  dsimp only at source clif body outcome set frame
  obtain ⟨inv, maps, sources⟩ := stock_lower_record_context run scope events
  have globalSource := sources _ _ _ source clif
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, nodeBi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original, st0, oldBuild, spec, view⟩ := buildCtx_source build
  have defs : event.ctx.valDef = original.valDef := by
    rw [eventEq, (stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valDef
  have types : event.ctx.valTy = original.valTy := by
    rw [eventEq, (stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valTy
  have avail := view_avail view f
  have originalSource : original.insts[blockStart f bi + j]? = some info := by
    rw [← view.insts, ← current]
    exact globalSource
  obtain ⟨other, otherSource, otherClif, results⟩ := spec.facts.stmt bi b j stm block statement
  cases Option.some.inj (otherSource.symm.trans originalSource)
  have sameInst := Option.some.inj (otherClif.symm.trans clif)
  subst inst
  have args : ∀ y ∈ Driver.instArgs stm.inst, y ∈ availOf f (availIn f result.ctx) bi j := by
    intro y member
    rw [avail]
    exact (dominated.uses original ranges st0 oldBuild bi b block).1 j stm statement y member
  have resultFacts : ∀ x ∈ info.results,
      x ∉ availOf f (availIn f result.ctx) bi j ∧ event.ctx.defInst? x = some record.inst := by
    intro x member
    have xm : x ∈ stm.results := by rwa [results] at member
    refine ⟨?_, ?_⟩
    · intro available
      exact ((mem_av block).mp available).2 ⟨j, stm, Nat.le_refl _, statement, xm⟩
    · simpa only [Ctx.defInst?, defs, current] using
        (defInst_res spec.facts dominated.ssa block statement xm)
  have next : ∀ x ∈ availOf f (availIn f result.ctx) bi (j + 1),
      x ∈ availOf f (availIn f result.ctx) bi j ∨ x ∈ info.results := by
    intro x member
    by_cases h : x ∈ info.results
    · exact .inr h
    · exact .inl (available_before_of_after_not_result block statement member (by rwa [← results]))
  have closed : ∀ k x d info' cl, x ∈ availOf f (availIn f result.ctx) bi k →
      event.ctx.defInst? x = some d → event.ctx.insts[d]? = some info' →
      info'.clif = some cl → ∀ y ∈ Driver.instArgs cl,
      y ∈ availOf f (availIn f result.ctx) bi k := by
    intro k x d info' cl hx hd hi hc y hy
    have hd0 : original.defInst? x = some d := by simpa only [Ctx.defInst?, defs] using hd
    have hi0 : original.insts[d]? = some info' := by
      rw [← view.insts]
      exact sources _ _ _ hi hc
    rw [avail] at hx ⊢
    exact avail_step dominated oldBuild hx hd0 hi0 hc (.inl hy)
  have nodup : info.results.Nodup := by rw [results]; exact stmt_nodup dominated.ssa block statement
  subst fr'
  refine ⟨?_, ?_⟩
  · intro x d info' cl v hd hi hc hp hv
    have hx : x ∈ availOf f (availIn f result.ctx) bi (j + 1) := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by rw [restrict_regs_of_mem hx] at hv; exact hv
    have clargs := closed (j + 1) x d info' cl hx hd hi hc
    rcases next x hx with old | new
    · have other : x ∉ info.results := fun h => (resultFacts x h).1 old
      have oldValue : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some v := by
        rw [restrict_regs_of_mem old, ← setMany_other set other]; exact hv'
      obtain ⟨vals0, evaluated, lookup⟩ := dfg.1 x d info' cl v hd hi hc hp oldValue
      refine ⟨vals0, fun mem => ?_, lookup⟩
      rw [← evaluated mem]
      refine evalInst_congr ?_ ?_ mem cl ?_
      · rfl
      · rfl
      intro y hy
      have oldY := closed j x d info' cl old hd hi hc y hy
      have otherY : y ∉ info.results := fun h => (resultFacts y h).1 oldY
      rw [restrict_regs_of_mem (clargs y hy), restrict_regs_of_mem oldY]
      exact setMany_other set otherY
    · have equal := (resultFacts x new).2
      rw [hd] at equal
      cases Option.some.inj equal
      rw [source] at hi
      cases hi
      rw [clif] at hc
      cases hc
      have evaluated : Clif.evalInst fr cm stm.inst = .ok (vals, cm') := by
        rw [← instOutcome_of_pure (env := env) (p := cp) hp]; exact outcome
      obtain ⟨_, allMem⟩ := evalInst_pure hp evaluated
      obtain ⟨m, v', hxm, hvm, hrv⟩ := setMany_mem set nodup x new
      rw [hrv] at hv'
      cases hv'
      refine ⟨vals, fun mem => ?_, lookup_zip_nodup nodup (setMany_length set) m x _ hxm hvm⟩
      rw [← allMem mem]
      refine evalInst_congr ?_ ?_ mem stm.inst ?_
      · rfl
      · rfl
      intro y hy
      have oldY := args y hy
      have otherY : y ∉ info.results := fun h => (resultFacts y h).1 oldY
      rw [restrict_regs_of_mem (clargs y hy)]
      exact setMany_other set otherY
  · intro x t v ht hv
    have hx : x ∈ availOf f (availIn f result.ctx) bi (j + 1) := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by rw [restrict_regs_of_mem hx] at hv; exact hv
    by_cases new : x ∈ info.results
    · obtain ⟨m, v', hxm, hvm, hrv⟩ := setMany_mem set nodup x new
      have equal : v' = v := Option.some.inj (hrv.symm.trans hv')
      obtain ⟨tys, resultTypes, mappedTypes, _⟩ := inv.resTys _ info stm.inst source clif
      have actualTypes := instOutcome_types outcome (by rw [func]; exact resultTypes)
      have atType : info.resTys[m]? = some (CTy.ofClif v'.ty) := by
        rw [mappedTypes, ← actualTypes]
        simp [List.getElem?_map, hvm]
      have declared := (spec.facts.types dominated.ssa).1 _ info originalSource m x _ hxm atType
      have actual : event.ctx.valueType? x = some (CTy.ofClif v'.ty) := by
        simpa only [Ctx.valueType?, types] using declared
      rw [actual] at ht
      rw [← equal]
      exact Option.some.inj ht
    · have old := (next x hx).resolve_right new
      apply dfg.2 x t v ht
      rw [restrict_regs_of_mem old, ← setMany_other set new]
      exact hv'
end Backend.Stock.Proof

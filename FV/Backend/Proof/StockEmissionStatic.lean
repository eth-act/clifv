import FV.Backend.Proof.StockEmissionCoverage

namespace Backend.Stock.Proof.Coverage.Emission
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem since_spill_valid {before after : LState} (since : CovSince before after)
    {i : MInst} (member : i ∈ after.emitted.toList.drop before.emitted.size) (ordinary : i.isCtl = false) :
    SpillInstOk i := by
  obtain ⟨code,emitted,covered⟩ := since
  have suffix : after.emitted.toList.drop before.emitted.size = code := by
    rw [emitted,Array.toList_append,List.toList_toArray]
    simp
  rw [suffix] at member
  have form := covered i member
  simp only [Covered,ordinary,Bool.false_or] at form
  exact spillInstOk_of_formOk form

/-- Every actual non-control instruction newly emitted by a successful Stock
statement root satisfies the spill allocator's complete local static contract.
Its valid operands/constraints/scratch capacity/defs follow from coverage;
no additional accepted-program assumption is introduced. -/
theorem stock_statement_spill_static {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ii] before = .ok (out,after,trace))
    {i : MInst} (member : i ∈ after.base.emitted.toList.drop before.base.emitted.size)
    (ordinary : i.isCtl = false) : SpillInstOk i :=
  since_spill_valid (stock_statement_emission_coverage mapped clean source original run) member ordinary

/-- Actual straight-line compare/setup instructions emitted by branch roots
also satisfy the spill static contract. The branch terminator is handled by
the separate control proof; earlier theorem interfaces remain unchanged. -/
theorem stock_branch_spill_static {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {targets : List Label} {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets] before = .ok (out,after,trace))
    {i : MInst} (member : i ∈ after.base.emitted.toList.drop before.base.emitted.size)
    (ordinary : i.isCtl = false) : SpillInstOk i :=
  since_spill_valid (stock_branch_emission_coverage mapped clean run) member ordinary

end Backend.Stock.Proof.Coverage.Emission

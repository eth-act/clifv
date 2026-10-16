import FV.Backend.Proof.StockEmissionCoverageFixture

namespace Backend.Stock.Proof.EmissionCoverageWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.EmissionCoverageFixture
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem lower_build {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩

private theorem root_context {branch : Bool} {result : Result}
    (run : Stock.lower (function branch) = .ok result) (scope : LowerScope (function branch)) :
    MappedCtxInv (function branch) (rootCtx branch result.ctx) ∧
      Clean (sourceIdentityCtx (rootCtx branch result.ctx)) := by
  obtain ⟨ranges,build⟩ := lower_build run
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have mapped := buildCtx_mappedInv scope build
  have clean : Clean (sourceIdentityCtx result.ctx) := by
    intro i info lookup
    change result.ctx.insts[i]? = some info at lookup
    rw [view.insts] at lookup
    exact Cov.clean_of_build legacy i info lookup
  cases branch
  · exact ⟨mapped,clean⟩
  · have block : (function true).blocks[0]? = some (function true).blocks[0]! := rfl
    have placeholder := spec.facts.term 0 _ block
    have index : blockStart (function true) 0 + ((function true).blocks[0]!).body.length = 1 := rfl
    rw [index] at placeholder
    have ph : result.ctx.insts[1]? = some ⟨.op .unit,[],[],none⟩ := by rw [view.insts]; exact placeholder
    exact ⟨mapped.termCtx ph _,clean_termCtx clean (t := .brif 17 ⟨1,[7]⟩ ⟨2,[7]⟩) rfl 1⟩

/-- Complete actual original-input sources and raw/checked/physical pipelines
inhabit both emitted-form roots and their ordinary spill-static contracts with
an actual non-control instruction, so the ordinary premise is not vacuous. -/
theorem stock_emission_spill_static_witness (branch : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (out : Backend.V)
      (after : State) (trace : List RuleId) (i : MInst),
      Stock.lower (function branch) = .ok result ∧ LowerScope (function branch) ∧
      Dominated (function branch) ∧ ArityOk (function branch) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      MappedCtxInv (function branch) (rootCtx branch result.ctx) ∧ Clean (sourceIdentityCtx (rootCtx branch result.ctx)) ∧
      Stock.runTerm (rootCtx branch result.ctx) (rootName branch) (rootArgs branch) result.initial =
        .ok (some out,after,trace) ∧ CovSince result.initial.base after.base ∧
      i ∈ after.base.emitted.toList.drop result.initial.base.emitted.size ∧ i.isCtl = false ∧ SpillInstOk i := by
  obtain ⟨fixture⟩ := emission_fixture branch
  obtain ⟨mapped,clean⟩ := root_context fixture.lowered fixture.scope
  obtain ⟨i,member,ordinary⟩ := Array.any_eq_true'.mp fixture.ordinary
  have ordinary : i.isCtl = false := by simpa using ordinary
  have emitted : i ∈ fixture.after.base.emitted.toList.drop fixture.result.initial.base.emitted.size := by
    rw [fixture.initialEmpty]
    simpa using member
  have since : CovSince fixture.result.initial.base fixture.after.base ∧ SpillInstOk i := by
    cases branch
    · obtain ⟨ranges,build⟩ := lower_build fixture.lowered
      obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
      have block : (function false).blocks[0]? = some (function false).blocks[0]! := rfl
      have stmt : ((function false).blocks[0]!).body[0]? = some ⟨[7],.iconst .i64 9⟩ := rfl
      obtain ⟨info,source,clif,results⟩ := spec.facts.stmt 0 _ 0 _ block stmt
      have source' : (rootCtx false fixture.result.ctx).insts[0]? = some info := by
        rw [show blockStart (function false) 0 + 0 = 0 from rfl] at source
        change fixture.result.ctx.insts[0]? = some info
        rw [view.insts]; exact source
      exact ⟨Coverage.Emission.stock_statement_emission_coverage mapped clean source' clif fixture.root,
        Coverage.Emission.stock_statement_spill_static mapped clean source' clif fixture.root emitted ordinary⟩
    · exact ⟨Coverage.Emission.stock_branch_emission_coverage mapped clean fixture.root,
        Coverage.Emission.stock_branch_spill_static mapped clean fixture.root emitted ordinary⟩
  exact ⟨fixture.result,fixture.prepared,fixture.rf,fixture.af,fixture.out,fixture.after,fixture.trace,i,
    fixture.lowered,fixture.scope,fixture.dominated,fixture.arity,fixture.prepare,fixture.fallback,fixture.accepted,fixture.physical,
    mapped,clean,fixture.root,since.1,emitted,ordinary,since.2⟩

end Backend.Stock.Proof.EmissionCoverageWitness

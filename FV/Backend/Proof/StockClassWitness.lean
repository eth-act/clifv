import FV.Backend.Proof.StockClassRoots
import FV.Backend.Proof.StockClassGrowthWitness
import FV.Backend.Proof.StockEmissionCoverageWitness
namespace Backend.Stock.Proof.OperandClassWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.OperandClassDraft
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


private theorem suffix_inst_classes {ctx : Ctx} {before after : LState}
    (invariant : ClsIs ctx before after) {i : MInst}
    (member : i ∈ after.emitted.toList.drop before.emitted.size) : InstCls after.classes i := by
  obtain ⟨code,emitted,covered⟩ := invariant.emitted
  have suffix : after.emitted.toList.drop before.emitted.size = code := by
    rw [emitted,Array.toList_append,List.toList_toArray]
    simp
  rw [suffix] at member
  exact instCls_of (covered i member)

/-- Complete original statement and comparing-branch source pipelines inhabit
all class-root premises and include a real ordinary emitted instruction. -/
theorem stock_complete_operand_classes_witness (branch : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (out : Backend.V)
      (after : State) (trace : List RuleId) (ranges : Array (Nat × Nat)) (i : MInst),
      Stock.lower (function branch) = .ok result ∧ LowerScope (function branch) ∧
      Dominated (function branch) ∧ ArityOk (function branch) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function branch) = .ok (result.ctx,ranges,result.initial) ∧
      MappedCtxInv (function branch) (rootCtx branch result.ctx) ∧ Clean (rootCtx branch result.ctx) ∧
      Stock.runTerm (rootCtx branch result.ctx) (rootName branch) (rootArgs branch) result.initial =
        .ok (some out,after,trace) ∧
      ClsIs (rootCtx branch result.ctx) result.initial.base result.initial.base ∧
      ClsIs (rootCtx branch result.ctx) result.initial.base after.base ∧
      (branch = false → GoodV after.base.classes out) ∧
      i ∈ after.base.emitted.toList.drop result.initial.base.emitted.size ∧ i.isCtl = false ∧
      InstCls after.base.classes i := by
  obtain ⟨fixture⟩ := emission_fixture branch
  obtain ⟨ranges,build⟩ := lower_build fixture.lowered
  obtain ⟨mapped,clean⟩ := root_context fixture.lowered fixture.scope
  have initial0 := stock_build_initial_classInvariant build
  have initial : ClsIs (rootCtx branch fixture.result.ctx) fixture.result.initial.base fixture.result.initial.base := by
    cases branch
    · exact initial0
    · exact ⟨initial0.sz,initial0.vals,initial0.try1,initial0.try2,initial0.emitted⟩
  have facts : ClsIs (rootCtx branch fixture.result.ctx) fixture.result.initial.base fixture.after.base ∧
      (branch = false → GoodV fixture.after.base.classes fixture.out) := by
    cases branch
    · obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
      have block : (function false).blocks[0]? = some (function false).blocks[0]! := rfl
      have stmt : ((function false).blocks[0]!).body[0]? = some ⟨[7],.iconst .i64 9⟩ := rfl
      obtain ⟨info,source,clif,results⟩ := spec.facts.stmt 0 _ 0 _ block stmt
      have source' : (rootCtx false fixture.result.ctx).insts[0]? = some info := by
        rw [show blockStart (function false) 0 + 0 = 0 from rfl] at source
        change fixture.result.ctx.insts[0]? = some info
        rw [view.insts]; exact source
      have classed := stock_statement_classes mapped clean source' clif fixture.root initial
      exact ⟨classed.1,fun _ => classed.2 _ rfl (by rw [results]; decide)⟩
    · exact ⟨stock_branch_classes (ctx := rootCtx true fixture.result.ctx) clean fixture.root initial,by intro h; cases h⟩
  obtain ⟨i,member,ordinary⟩ := Array.any_eq_true'.mp fixture.ordinary
  have ordinary : i.isCtl = false := by simpa using ordinary
  have emitted : i ∈ fixture.after.base.emitted.toList.drop fixture.result.initial.base.emitted.size := by
    rw [fixture.initialEmpty]
    simpa using member
  exact ⟨fixture.result,fixture.prepared,fixture.rf,fixture.af,fixture.out,fixture.after,fixture.trace,ranges,i,
    fixture.lowered,fixture.scope,fixture.dominated,fixture.arity,fixture.prepare,fixture.fallback,fixture.accepted,fixture.physical,
    build,mapped,clean,fixture.root,initial,facts.1,facts.2,emitted,ordinary,suffix_inst_classes facts.1 emitted⟩

/-- Complete original return source and actual raw/global-checked/physical
stages inhabit the term-context builder and real return class-root contract. -/
theorem stock_complete_retTrap_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (out : Option Backend.V) (after : State) (trace : List RuleId),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧
      ClsIs (Coverage.TerminalDraftObservation.context result)
        (Coverage.TerminalDraftObservation.before result).base (Coverage.TerminalDraftObservation.before result).base ∧
      Stock.runTerm (Coverage.TerminalDraftObservation.context result) "lower" [.inst 1]
        (Coverage.TerminalDraftObservation.before result) = .ok (out,after,trace) ∧ out.isSome = true ∧
      ClsIs (Coverage.TerminalDraftObservation.context result)
        (Coverage.TerminalDraftObservation.before result).base after.base := by
  rcases Coverage.TerminalDraftWitness.stock_complete_terminal_scan_form_witness with
    ⟨result,p,rf,af,ranges,out,after,trace,emission,scan,body,i,
      lowered,scope,dominated,arity,prepared,fallback,checked,physical,build,
      mapped,clean,slot,data,named,hasOut,since,emissionRun,emitted,covered,
      scanRun,scanned,scanCoverage,scanSlot,bodyRun,bodyCoverage,member,ordinary,icov,ivalid⟩
  have base := stock_build_term_classInvariant build 1 Coverage.TerminalDraftObservation.termDataValue
  have initial : ClsIs (Coverage.TerminalDraftObservation.context result)
      (Coverage.TerminalDraftObservation.before result).base (Coverage.TerminalDraftObservation.before result).base := by
    have classes : (Coverage.TerminalDraftObservation.before result).base.classes = result.initial.base.classes := by
      unfold Coverage.TerminalDraftObservation.before scanState
      dsimp only
      split <;> rfl
    have frontier : (Coverage.TerminalDraftObservation.before result).base.nextVreg = result.initial.base.nextVreg := by
      unfold Coverage.TerminalDraftObservation.before scanState
      dsimp only
      split <;> rfl
    refine ⟨?_,?_,?_,?_,⟨[],by simp,by simp⟩⟩
    · simpa only [Sz,classes,frontier] using base.sz
    · intro x r lookup
      change RegCls (Coverage.TerminalDraftObservation.before result).base.classes r
      rw [classes]; exact base.vals x r lookup
    · intro r member
      change RegCls (Coverage.TerminalDraftObservation.before result).base.classes r
      rw [classes]; exact base.try1 r member
    · intro r member
      change RegCls (Coverage.TerminalDraftObservation.before result).base.classes r
      rw [classes]; exact base.try2 r member
  have final := stock_retTrap_classes (ctx := Coverage.TerminalDraftObservation.context result) clean (t := .ret [7]) rfl data slot named initial
  exact ⟨result,p,rf,af,ranges,out,after,trace,lowered,scope,dominated,arity,prepared,fallback,checked,
    physical,build,initial,named,hasOut,final⟩

end Backend.Stock.Proof.OperandClassWitnessDraft

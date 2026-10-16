import FV.Backend.Proof.StockBindingCoverageKernel
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockScanContextCoverage

namespace Backend.Stock.Proof.BindingCoverageWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Backend.Proof.PerEdgePrep
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

private theorem zip_right {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β}
    (member : (x,y) ∈ xs.zip ys) : y ∈ ys := by
  obtain ⟨j,atPair⟩ := List.mem_iff_getElem?.mp member
  exact List.mem_of_getElem? (List.getElem?_zip_eq_some.mp atPair).2

/-- Complete original-input source/raw/checked/physical success inhabits the
result-register, no-copy binding, actual emitted scan and whole-run record
coverage proofs. Both a real result register and a real retained instruction
are present; the result and instruction membership premises are not vacuous. -/
theorem stock_bound_record_form_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (n : Nat)
      (out : V) (after : State) (trace : List RuleId) (emission : Emission)
      (event : BlockScanEvent) (record : ScanRecord) (info : IInfo)
      (rss : List (List Reg)) (root bound : State) (fired : List RuleId) (i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.runTerm result.ctx "lower" [.inst 0] result.initial = .ok (some out,after,trace) ∧
      (.vreg n .int) ∈ out.regsIn ∧
      (∀ r ∈ out.regsIn,∃ k,r = .vreg k .int) ∧
      emitInstruction result.ctx 0 result.initial = .ok emission ∧ emission.code ≠ #[] ∧
      (∀ m ∈ emission.code.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m)) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ Clean (sourceIdentityCtx event.ctx) ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.iconst .i64 9) ∧ info.results = [7] ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some (.regsVec rss),root,fired) ∧
      rss ≠ [] ∧ info.results.zip rss ≠ [] ∧
      bindResults event.ctx (info.results.zip rss) root = .ok (bound,#[]) ∧ bound.base = root.base ∧
      i ∈ record.output.emitted.toList ∧ i.isCtl = false ∧ Covered i = true ∧ SpillInstOk i := by
  obtain ⟨fixture⟩ := emission_fixture false
  have observed := stock_binding_observed
  unfold Observed at observed
  rw [fixture.lowered] at observed
  have facts :
      (Stock.runTerm fixture.result.ctx "lower" [.inst 0] fixture.result.initial).toOption.any
        (fun (out,_,_) => out.any (fun v => !v.regsIn.isEmpty)) = true ∧
      (emitInstruction fixture.result.ctx 0 fixture.result.initial).toOption.any (fun emission => !emission.code.isEmpty) = true ∧
      fixture.result.blockScans.any (fun event => event.output.records.any (recordB event)) = true := by
    apply of_decide_eq_true
    exact Option.some.inj observed
  obtain ⟨returned,emitted,retained⟩ := facts
  have named := fixture.root
  change Stock.runTerm fixture.result.ctx "lower" [.inst 0] fixture.result.initial = .ok (some fixture.out,fixture.after,fixture.trace) at named
  rw [named] at returned
  change (!fixture.out.regsIn.isEmpty) = true at returned
  obtain ⟨r,member⟩ : ∃ r,r ∈ fixture.out.regsIn := by
    cases list : fixture.out.regsIn with
    | nil => simp [list] at returned
    | cons r rs => exact ⟨r,List.mem_cons_self ..⟩
  obtain ⟨ranges,build⟩ := lower_build fixture.lowered
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have mapped := buildCtx_mappedInv fixture.scope build
  have clean : Clean (sourceIdentityCtx fixture.result.ctx) := by
    intro k info found
    change fixture.result.ctx.insts[k]? = some info at found
    rw [view.insts] at found
    exact Cov.clean_of_build legacy k info found
  have block : (function false).blocks[0]? = some (function false).blocks[0]! := rfl
  have stmt : ((function false).blocks[0]!).body[0]? = some ⟨[7],.iconst .i64 9⟩ := rfl
  obtain ⟨sourceInfo,atSource,sourceInst,sourceResults⟩ := spec.facts.stmt 0 _ 0 _ block stmt
  have actualSource : fixture.result.ctx.insts[0]? = some sourceInfo := by
    rw [view.insts]
    exact atSource
  have registers := Coverage.Result.stock_statement_result_registers mapped clean actualSource sourceInst named
    (by rw [sourceResults]; decide)
  obtain ⟨n,register⟩ := registers r member
  subst r
  cases emitRun : emitInstruction fixture.result.ctx 0 fixture.result.initial with
  | error err => simp only [emitRun,Except.toOption,Option.any_none,Bool.false_eq_true] at emitted
  | ok emission =>
    have nonempty : emission.code ≠ #[] := by
      simp only [emitRun,Except.toOption,Option.any_some,Bool.not_eq_true'] at emitted
      intro empty
      rw [empty] at emitted
      cases emitted
    have code := Coverage.Result.stock_emitInstruction_form_coverage mapped clean actualSource sourceInst fixture.initialEmpty emitRun
    obtain ⟨event,eventMember,hasRecord⟩ := Array.any_eq_true'.mp retained
    obtain ⟨record,recordMember,properties⟩ := List.any_eq_true.mp hasRecord
    simp only [recordB,Bool.and_eq_true,beq_iff_eq] at properties
    obtain ⟨⟨⟨⟨zero,cleanData⟩,sourceData⟩,stepData⟩,nonemptyCode⟩ := properties
    have eventMember := Array.mem_toList_iff.mpr eventMember
    have eventClean := Coverage.Result.stock_lower_scan_context_clean fixture.lowered eventMember
    have sourceData := of_decide_eq_true sourceData
    obtain ⟨info,source,clif,results⟩ : ∃ info,event.ctx.insts[record.inst]? = some info ∧
        info.clif = some (.iconst .i64 9) ∧ info.results = [7] := by
      cases found : event.ctx.insts[record.inst]? with
      | none => simp [found] at sourceData
      | some info =>
        rw [found] at sourceData
        simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at sourceData
        exact ⟨info,rfl,sourceData.1,sourceData.2⟩
    obtain ⟨step,recorded,stepProperties⟩ := (Option.any_eq_true _ _).mp stepData
    simp only [Bool.and_eq_true,beq_iff_eq] at stepProperties
    have decision : step.decision = .emitted := stepProperties.1
    obtain ⟨selected⟩ := stock_lower_record_selection fixture.lowered eventMember recordMember recorded decision
    have nonemptyResults : selected.results ≠ [] := by
      intro empty
      have present := stepProperties.2
      rw [selected.resultRegs,empty] at present
      cases present
    have nonemptyPairs : info.results.zip selected.results ≠ [] := by
      rw [results]
      cases list : selected.results with
      | nil => exact False.elim (nonemptyResults list)
      | cons rs rest => simp
    have eventMapped := (stock_lower_record_context fixture.lowered fixture.scope eventMember).1
    have root := selected.rootRun
    rw [selected.output] at root
    have outputs := Coverage.Result.stock_statement_result_registers eventMapped eventClean source clif root
      (by rw [results]; decide)
    have virtual : ∀ pair ∈ info.results.zip selected.results,∀ r ∈ pair.2,∃ k,r = .vreg k .int := by
      intro pair inside r register
      exact outputs r (mem_regsVec (zip_right inside) register)
    have binding := selected.binding
    have lookup : event.ctx.insts[record.inst]! = info := by rw [getElem!_def,source]
    rw [lookup] at binding
    obtain ⟨sameBase,noCopies⟩ := Coverage.Result.stock_bindResults_virtual_only eventMapped.valueReg virtual binding
    rw [noCopies] at binding
    have allInstructions := Coverage.Result.stock_lower_source_record_form_coverage_original fixture.lowered fixture.scope
      eventMember recordMember source clif
    obtain ⟨i,instruction,ordinary⟩ := Array.any_eq_true'.mp nonemptyCode
    have instruction : i ∈ record.output.emitted.toList := Array.mem_toList_iff.mpr instruction
    have ordinary : i.isCtl = false := by simpa using ordinary
    exact ⟨fixture.result,fixture.prepared,fixture.rf,fixture.af,n,fixture.out,fixture.after,fixture.trace,emission,
      event,record,info,selected.results,selected.next,selected.bound,selected.fired,i,
      fixture.lowered,fixture.scope,fixture.dominated,fixture.arity,fixture.prepare,fixture.fallback,fixture.accepted,fixture.physical,
      named,member,registers,emitRun,nonempty,code,eventMember,recordMember,eventClean,source,clif,results,
      root,nonemptyResults,nonemptyPairs,binding,sameBase,instruction,ordinary,(allInstructions i instruction).1,(allInstructions i instruction).2 ordinary⟩

end Backend.Stock.Proof.BindingCoverageWitness

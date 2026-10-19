import FV.Backend.Proof.StockCoreFormContracts
import FV.Backend.Proof.StockCoreFormObservation

namespace Backend.Stock.Proof.Coverage.CoreDraftWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.EmissionCoverageFixture Backend.Stock.Proof.Coverage.CoreDraft
open Backend.Stock.Proof.Coverage.CoreDraftObservation
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore emitBranch

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

private theorem clean_block {f : Clif.Function} {ctx : Ctx}
    (clean : Clean (sourceIdentityCtx ctx)) {t : Clif.Terminator} {data : V}
    (prepared : blockData f t = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    Clean (sourceIdentityCtx {Driver.termCtx ctx ti data with tryRegs := trs}) := by
  cases t <;> simp only [blockData] at prepared
  all_goals first
    | exact clean_tryCtx clean prepared ti trs
    | exact clean_termCtx clean prepared ti

private theorem lower_build {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩

theorem stock_complete_core_form_witness (flag : Bool) :
    ∃ (result : Backend.Stock.Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (core : LoweredBlockCore) (br : Option BranchEmission) (i : MInst),
      Stock.lower (function flag) = .ok result ∧ LowerScope (function flag) ∧
      Dominated (function flag) ∧ ArityOk (function flag) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function flag) = .ok (result.ctx,ranges,result.initial) ∧
      (function flag).blocks[0]? = some (sourceBlock flag) ∧ ranges[0]? = some (0,2) ∧
      blockData (function flag) (sourceBlock flag).term = .ok (data flag) ∧
      MappedCtxInv (function flag) (context flag result) ∧ Clean (sourceIdentityCtx (context flag result)) ∧
      lowerBlockCore result.ctx result.order (function flag) (sourceBlock flag) 0 0 2
        (data flag) result.order.successors[0]! result.initial = .ok core ∧
      (∀ m ∈ core.code.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m)) ∧
      i ∈ core.code.toList ∧ i.isCtl = false ∧ Covered i = true ∧ SpillInstOk i ∧
      br.isSome = flag ∧
      (∀ emission,br = some emission →
        emitBranch (context flag result) (function flag) (sourceBlock flag).term 0 1
          result.order.successors[0]! result.initial = .ok emission ∧
        ∀ m ∈ emission.code.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m)) ∧
      (flag = true → ∃ emission j,br = some emission ∧ j ∈ emission.code.toList ∧
        j.isCtl = false ∧ Covered j = true ∧ SpillInstOk j) := by
  obtain ⟨fixture⟩ := emission_fixture flag
  obtain ⟨ranges,build⟩ := lower_build fixture.lowered
  obtain ⟨original,oldState,legacy,spec,view⟩ := buildCtx_source build
  have block : (function flag).blocks[0]? = some (sourceBlock flag) := by cases flag <;> rfl
  have rangeRun : ranges[0]? = some (0,2) := by
    have found := spec.ranges 0 _ block
    cases flag <;> exact found
  have ph : fixture.result.ctx.insts[1]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    have found := spec.facts.term 0 _ block
    cases flag <;> exact found
  have prepared : blockData (function flag) (sourceBlock flag).term = .ok (data flag) := by
    cases flag <;> rfl
  have mapped : MappedCtxInv (function flag) (context flag fixture.result) :=
    ((buildCtx_mappedInv fixture.scope build).termCtx ph (data flag)).withTryRegs _
  have clean : Clean (sourceIdentityCtx (context flag fixture.result)) :=
    clean_block (clean_stock build) prepared 1 _
  have actual := observed flag
  unfold CoreDraftObservation.Observed CoreDraftObservation.pipeline at actual
  rw [fixture.lowered] at actual
  simp only [bind,Except.bind] at actual
  cases brRun : (if flag then some <$> (emitBranch (context flag fixture.result) (function flag)
      (sourceBlock flag).term 0 1 fixture.result.order.successors[0]! fixture.result.initial)
      else pure none : Except String (Option BranchEmission)) with
  | error e =>
    simp only [pure,Except.pure] at brRun actual
    rw [brRun] at actual
    cases actual
  | ok br =>
    simp only [brRun,bind,Except.bind] at actual
    cases coreRun : lowerBlockCore fixture.result.ctx fixture.result.order (function flag) (sourceBlock flag)
        0 0 2 (data flag) fixture.result.order.successors[0]! fixture.result.initial with
    | error e => simp [coreRun,Except.toOption] at actual
    | ok core =>
      simp only [coreRun,bind,Except.bind,pure,Except.pure,Except.toOption,Option.map_some] at actual
      have facts : core.code.any (fun i => !i.isCtl) = true ∧
          (if flag then br.any (fun b => b.code.any (fun i => !i.isCtl)) = true else br = none) := by
        apply of_decide_eq_true
        exact Option.some.inj actual
      have branchRun {emission : BranchEmission} (selected : br = some emission) :
          emitBranch (context flag fixture.result) (function flag) (sourceBlock flag).term 0 1
            fixture.result.order.successors[0]! fixture.result.initial = .ok emission := by
        cases flag with
        | false =>
          simp only [Bool.false_eq_true,ite_false,pure,Except.pure] at brRun
          cases brRun
          cases selected
        | true =>
          change (some <$> emitBranch (context true fixture.result) (function true) (sourceBlock true).term
            0 1 fixture.result.order.successors[0]! fixture.result.initial : Except String (Option BranchEmission)) = .ok br at brRun
          cases emitted : emitBranch (context true fixture.result) (function true) (sourceBlock true).term
              0 1 fixture.result.order.successors[0]! fixture.result.initial with
          | error e => simp [emitted,Functor.map,Except.map] at brRun
          | ok output =>
            simp only [emitted,Functor.map,Except.map,Except.ok.injEq] at brRun
            cases brRun
            cases selected
            rfl
      have branchForms : ∀ emission,br = some emission →
          emitBranch (context flag fixture.result) (function flag) (sourceBlock flag).term 0 1
            fixture.result.order.successors[0]! fixture.result.initial = .ok emission ∧
          ∀ m ∈ emission.code.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m) := by
        intro emission selected
        exact ⟨branchRun selected,stock_emitBranch_form_coverage mapped clean (branchRun selected)⟩
      have shape : br.isSome = flag := by
        cases flag with
        | false =>
          have none : br = none := facts.2
          rw [none]
          rfl
        | true =>
          have present : br.any (fun b => b.code.any (fun i => !i.isCtl)) = true := facts.2
          obtain ⟨emission,selected,nonempty⟩ := (Option.any_eq_true _ _).mp present
          rw [selected]
          rfl
      have branchWitness : flag = true → ∃ emission j,br = some emission ∧
          j ∈ emission.code.toList ∧ j.isCtl = false ∧ Covered j = true ∧ SpillInstOk j := by
        intro enabled
        have present := facts.2
        rw [enabled] at present
        obtain ⟨emission,selected,nonempty⟩ := (Option.any_eq_true _ _).mp present
        obtain ⟨j,member,ordinary⟩ := Array.any_eq_true'.mp nonempty
        have member : j ∈ emission.code.toList := Array.mem_toList_iff.mpr member
        have ordinary : j.isCtl = false := by simpa using ordinary
        have form := (branchForms emission selected).2 j member
        exact ⟨emission,j,selected,member,ordinary,form.1,form.2 ordinary⟩
      have coreForms := stock_blockCore_form_coverage build fixture.scope block rangeRun prepared coreRun
      obtain ⟨i,member,ordinary⟩ := Array.any_eq_true'.mp facts.1
      have member : i ∈ core.code.toList := Array.mem_toList_iff.mpr member
      have ordinary : i.isCtl = false := by simpa using ordinary
      have form := coreForms i member
      exact ⟨fixture.result,fixture.prepared,fixture.rf,fixture.af,ranges,core,br,i,
        fixture.lowered,fixture.scope,fixture.dominated,fixture.arity,fixture.prepare,fixture.fallback,
        fixture.accepted,fixture.physical,build,block,rangeRun,prepared,mapped,clean,coreRun,coreForms,
        member,ordinary,form.1,form.2 ordinary,shape,branchForms,branchWitness⟩

end Backend.Stock.Proof.Coverage.CoreDraftWitness

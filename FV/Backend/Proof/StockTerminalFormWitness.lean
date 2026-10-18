import FV.Backend.Proof.StockTerminalFormContracts
import FV.Backend.Proof.StockTerminalFormObservation

namespace Backend.Stock.Proof.Coverage.TerminalDraftWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.Coverage.TerminalDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
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


open Backend.Stock.Proof.EmissionCoverageFixture
open Backend.Stock.Proof.Coverage.TerminalDraftObservation

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

theorem stock_complete_terminal_scan_form_witness :
    ∃ (result : Backend.Stock.Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (out : Option V) (after : State) (trace : List RuleId)
      (emission : Emission) (scan : Scan) (body : BlockScan) (i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      Backend.prepareAt result.code result.edgeArgs = .ok p ∧
      rf = Backend.spillAllocAt p.code p.edges ∧
      Backend.checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧
      MappedCtxInv (function false) (context result) ∧ Clean (sourceIdentityCtx (context result)) ∧
      (context result).insts[1]? = some ⟨termDataValue,[],[],none⟩ ∧
      Backend.termData (.ret [7]) = .ok termDataValue ∧
      Stock.runTerm (context result) "lower" [.inst 1] (before result) = .ok (out,after,trace) ∧
      out.isSome = true ∧ CovSince (before result).base after.base ∧
      emitInstruction (context result) 1 (before result) = .ok emission ∧ emission.code ≠ #[] ∧
      (∀ m ∈ emission.code.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m)) ∧
      scanInstruction (context result) 0 1 1 false result.initial = .ok scan ∧ scan.emitted ≠ #[] ∧
      (∀ m ∈ scan.emitted.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m)) ∧
      ScanSlot (context result) 1 1 false ∧
      scanBlock (context result) 0 1 false [1,0] result.initial = .ok body ∧
      (∀ m ∈ body.code.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m)) ∧
      i ∈ body.code.toList ∧ i.isCtl = false ∧ Covered i = true ∧ SpillInstOk i := by
  obtain ⟨fixture⟩ := emission_fixture false
  obtain ⟨ranges,build⟩ := lower_build fixture.lowered
  obtain ⟨original,oldState,legacy,spec,view⟩ := buildCtx_source build
  have block : (function false).blocks[0]? = some (function false).blocks[0]! := rfl
  have placeholder : fixture.result.ctx.insts[1]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact spec.facts.term 0 _ block
  have rangeRun : ranges[0]? = some (0,2) := spec.ranges 0 _ block
  have prepared : blockData (function false) ((function false).blocks[0]!).term = .ok termDataValue := rfl
  have dataRun : Backend.termData (.ret [7]) = .ok termDataValue := rfl
  have mapped : MappedCtxInv (function false) (context fixture.result) :=
    ((buildCtx_mappedInv fixture.scope build).termCtx placeholder termDataValue).withTryRegs _
  have clean : Clean (sourceIdentityCtx (context fixture.result)) :=
    clean_block (clean_stock build) prepared 1 _
  have slot : (context fixture.result).insts[1]? = some ⟨termDataValue,[],[],none⟩ :=
    termCtx_insts_self placeholder termDataValue
  have empty : (before fixture.result).base.emitted = #[] := by
    unfold before scanState
    dsimp only
    split <;> rfl
  have actual := observed
  unfold TerminalDraftObservation.Observed TerminalDraftObservation.pipeline at actual
  rw [fixture.lowered] at actual
  simp only [bind,Except.bind] at actual
  cases named : Stock.runTerm (context fixture.result) "lower" [.inst 1] (before fixture.result) with
  | error e => simp [named,Except.toOption] at actual
  | ok answer =>
    rcases answer with ⟨out,after,trace⟩
    simp only [named,bind,Except.bind] at actual
    cases emitted : emitInstruction (context fixture.result) 1 (before fixture.result) with
    | error e => simp [emitted,Except.toOption] at actual
    | ok emission =>
      simp only [emitted,bind,Except.bind] at actual
      cases scanned : scanInstruction (context fixture.result) 0 1 1 false fixture.result.initial with
      | error e => simp [scanned,Except.toOption] at actual
      | ok scan =>
        simp only [scanned,bind,Except.bind] at actual
        cases bodyRun : scanBlock (context fixture.result) 0 1 false [1,0] fixture.result.initial with
        | error e => simp [bodyRun,Except.toOption] at actual
        | ok body =>
          simp only [bodyRun,bind,Except.bind,pure,Except.pure,Except.toOption,Option.map_some] at actual
          have facts : out.isSome = true ∧ emission.code ≠ #[] ∧ scan.emitted ≠ #[] ∧
              body.code.any (fun i => !i.isCtl) = true := by
            apply of_decide_eq_true
            exact Option.some.inj actual
          have rootForms := stock_retTrap_emission_coverage mapped clean rfl dataRun slot named
          have emissionForms := stock_emit_retTrap_form_coverage mapped clean rfl dataRun slot empty emitted
          have scanForms := stock_scan_retTrap_form_coverage mapped clean rfl dataRun slot scanned
          have scanSlot : ScanSlot (context fixture.result) 1 1 false := .inr (.inr ⟨.ret [7],termDataValue,rfl,dataRun,slot⟩)
          have scanForms := stock_scan_slot_form_coverage mapped clean scanSlot scanned
          have builtRun : scanBlock {Driver.termCtx fixture.result.ctx ((0,2) : Nat × Nat).2.pred termDataValue
                with tryRegs := fixture.result.initial.tryRegs[1]!} 0 1 (blockBranch ((function false).blocks[0]!).term)
              (((Array.range (2-0)).map (0+·)).reverse.toList) fixture.result.initial = .ok body := by
            have indices : (((Array.range (2-0)).map (0+·)).reverse.toList) = [1,0] := by decide +kernel
            rw [show blockBranch ((function false).blocks[0]!).term = false from rfl,indices]
            exact bodyRun
          have bodyForms := stock_built_scanBlock_form_coverage build fixture.scope block rangeRun prepared
            (fixture.result.initial.tryRegs[1]!) builtRun
          obtain ⟨i,member,ordinary⟩ := Array.any_eq_true'.mp facts.2.2.2
          have member : i ∈ body.code.toList := Array.mem_toList_iff.mpr member
          have ordinary : i.isCtl = false := by simpa using ordinary
          have form := bodyForms i member
          exact ⟨fixture.result,fixture.prepared,fixture.rf,fixture.af,ranges,out,after,trace,emission,scan,body,i,
            fixture.lowered,fixture.scope,fixture.dominated,fixture.arity,fixture.prepare,fixture.fallback,
            fixture.accepted,fixture.physical,build,mapped,clean,slot,dataRun,named,facts.1,rootForms,
            emitted,facts.2.1,emissionForms,scanned,facts.2.2.1,scanForms,scanSlot,bodyRun,bodyForms,
            member,ordinary,form.1,form.2 ordinary⟩


end Backend.Stock.Proof.Coverage.TerminalDraftWitness

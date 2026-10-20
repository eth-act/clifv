import FV.Backend.Proof.StockScanClassContracts
import FV.Backend.Proof.StockClassWitness
import FV.Backend.Proof.StockBindingCoverageWitness

namespace Backend.Stock.Proof.BindingClassWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.ScanClassDraft Backend.Stock.Proof.OperandClassDraft
open Backend.Stock.Proof.EmissionCoverageFixture
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The real nonempty source emission, with actual ordered binding, has a
complete original-source/raw/global-checked/physical witness and operand classes. -/
theorem stock_complete_binding_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (ranges : Array (Nat × Nat))
      (emission : Emission) (info : IInfo) (i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧
      MappedCtxInv (function false) result.ctx ∧ Clean result.ctx ∧
      result.ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i64 9) ∧ info.results = [7] ∧
      ClsIs result.ctx result.initial.base result.initial.base ∧ result.initial.base.emitted = #[] ∧
      emitInstruction result.ctx 0 result.initial = .ok emission ∧ emission.code ≠ #[] ∧
      ClsIs result.ctx result.initial.base emission.state.base ∧
      (∀ m ∈ emission.code.toList,RegsFrom (RegCls emission.state.base.classes) m ∧ InstCls emission.state.base.classes m) ∧
      i ∈ emission.code.toList ∧ InstCls emission.state.base.classes i := by
  rcases OperandClassWitnessDraft.stock_complete_operand_classes_witness false with
    ⟨result,p,rf,af,out,after,trace,ranges,ordinary,lowered,scope,dominated,arity,prepared,
      fallback,checked,physical,build,mapped,clean,named,initial,rest⟩
  rcases BindingCoverageWitness.stock_bound_record_form_witness with
    ⟨result2,p2,rf2,af2,n,out2,after2,trace2,emission,event,record,info2,rss,root,bound,fired,i2,
      lowered2,_,_,_,_,_,_,_,_,_,_,emitted,nonempty,more⟩
  have same : result2 = result := Except.ok.inj (lowered2.symm.trans lowered)
  subst result2
  obtain ⟨fixture⟩ := emission_fixture false
  have sameFixture : fixture.result = result := Except.ok.inj (fixture.lowered.symm.trans lowered)
  have empty : result.initial.base.emitted = #[] := by rw [← sameFixture]; exact fixture.initialEmpty
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have block : (function false).blocks[0]? = some (function false).blocks[0]! := rfl
  have stmt : ((function false).blocks[0]!).body[0]? = some ⟨[7],.iconst .i64 9⟩ := rfl
  obtain ⟨info,source,clif,results⟩ := spec.facts.stmt 0 _ 0 _ block stmt
  have actualSource : result.ctx.insts[0]? = some info := by rw [view.insts]; exact source
  have classes := stock_emitInstruction_classes mapped clean actualSource clif initial empty emitted
  obtain ⟨i,member⟩ : ∃ i,i ∈ emission.code.toList := by
    have listNonempty : emission.code.toList ≠ [] := by simpa using nonempty
    cases found : emission.code.toList with
    | nil => exact False.elim (listNonempty found)
    | cons i is => exact ⟨i,by simp [found]⟩
  exact ⟨result,p,rf,af,ranges,emission,info,i,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    build,mapped,clean,actualSource,clif,results,initial,empty,emitted,nonempty,classes.1,classes.2,member,(classes.2 i member).2⟩

/-- A real complete return-plus-constant scan transports code to its final class
array, and every recorded input/output has the class invariant. The body has a
real non-control instruction and return emission is nonempty. -/
theorem stock_complete_scan_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (ranges : Array (Nat × Nat))
      (emission : Emission) (scan : Scan) (body : BlockScan) (i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧
      emitInstruction (Coverage.TerminalDraftObservation.context result) 1
        (Coverage.TerminalDraftObservation.before result) = .ok emission ∧ emission.code ≠ #[] ∧
      (∀ m ∈ emission.code.toList,InstCls emission.state.base.classes m) ∧
      scanInstruction (Coverage.TerminalDraftObservation.context result) 0 1 1 false result.initial = .ok scan ∧
      (∀ m ∈ scan.emitted.toList,InstCls scan.state.base.classes m) ∧
      scanBlock (Coverage.TerminalDraftObservation.context result) 0 1 false [1,0] result.initial = .ok body ∧
      ClassGrowthDraft.ClassGrowth result.initial body.state ∧
      (∀ m ∈ body.code.toList,RegsFrom (RegCls body.state.base.classes) m ∧ InstCls body.state.base.classes m) ∧
      (∀ record ∈ body.records,ClsIs (Coverage.TerminalDraftObservation.context result) record.input.base record.input.base ∧
        ClsIs (Coverage.TerminalDraftObservation.context result) record.output.state.base record.output.state.base) ∧
      i ∈ body.code.toList ∧ i.isCtl = false ∧ InstCls body.state.base.classes i := by
  rcases Coverage.TerminalDraftWitness.stock_complete_terminal_scan_form_witness with
    ⟨result,p,rf,af,ranges,out,after,trace,emission,scan,body,i,
      lowered,scope,dominated,arity,prepared,fallback,checked,physical,build,
      mapped,clean,slot,data,named,hasOut,since,emissionRun,emitted,covered,
      scanRun,scanned,scanCoverage,scanSlot,bodyRun,bodyCoverage,member,ordinary,icov,ivalid⟩
  have initial := stock_build_term_classInvariant build 1 Coverage.TerminalDraftObservation.termDataValue
  have reset : ClsIs (Coverage.TerminalDraftObservation.context result)
      (Coverage.TerminalDraftObservation.before result).base (Coverage.TerminalDraftObservation.before result).base := by
    unfold Coverage.TerminalDraftObservation.before scanState
    dsimp only
    split
    all_goals exact ⟨initial.sz,initial.vals,initial.try1,initial.try2,⟨[],by simp,by simp⟩⟩
  have buffer : (Coverage.TerminalDraftObservation.before result).base.emitted = #[] := by
    unfold Coverage.TerminalDraftObservation.before scanState
    dsimp only
    split <;> rfl
  have emittedClass := stock_emit_retTrap_classes (ctx := Coverage.TerminalDraftObservation.context result)
    clean (t := .ret [7]) rfl data slot reset buffer emissionRun
  have scannedClass := stock_scan_slot_classes mapped clean scanSlot initial scanRun
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have block : (function false).blocks[0]? = some (function false).blocks[0]! := rfl
  have rangeRun : ranges[0]? = some (0,2) := spec.ranges 0 _ block
  have bodyClass := stock_built_scanBlock_classes build scope block rangeRun
    (data := Coverage.TerminalDraftObservation.termDataValue) (by rfl)
    result.initial.tryRegs[1]! initial (output := body) (by
      change scanBlock (Coverage.TerminalDraftObservation.context result) 0 1 false
        (((Array.range 2).map (0 + ·)).reverse.toList) result.initial = .ok body
      have indices : ((Array.range 2).map (0 + ·)).reverse.toList = [1,0] := by decide +kernel
      rw [indices]
      exact bodyRun)
  exact ⟨result,p,rf,af,ranges,emission,scan,body,i,lowered,scope,dominated,arity,prepared,fallback,checked,physical,build,
    emissionRun,emitted,fun m hm => (emittedClass.2 m hm).2,scanRun,fun m hm => (scannedClass.2 m hm).2,
    bodyRun,bodyClass.1,bodyClass.2.2.1,bodyClass.2.2.2,member,ordinary,(bodyClass.2.2.1 i member).2⟩

end Backend.Stock.Proof.BindingClassWitnessDraft

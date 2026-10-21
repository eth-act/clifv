import FV.Backend.Proof.StockWholeClassGrowth
import FV.Backend.Proof.StockTerminalFormWitness

namespace Backend.Stock.Proof.ClassGrowthWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.ClassGrowthDraft Backend.Stock.Proof.InitialClassesDraft
open Backend.Stock.Proof.WholeClassGrowthDraft
open Backend.Stock.Proof.EmissionCoverageFixture
open Backend.Stock.Proof.Coverage.TerminalDraftObservation
open Backend.Stock.Proof.Coverage.TerminalDraftWitness
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Original source conditions and actual whole compiler stages inhabit class
preservation through a named rule, real scans and the complete Stock traversal.
The body contains a genuine non-control instruction, not an empty-code example. -/
theorem stock_complete_class_growth_witness :
    ∃ (result : Backend.Stock.Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (out : Option V) (after : State) (trace : List RuleId)
      (scan : Scan) (body : BlockScan) (i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧
      Stock.runTerm (context result) "lower" [.inst 1] (before result) = .ok (out,after,trace) ∧
      out.isSome = true ∧ scanInstruction (context result) 0 1 1 false result.initial = .ok scan ∧
      scanBlock (context result) 0 1 false [1,0] result.initial = .ok body ∧
      i ∈ body.code.toList ∧ i.isCtl = false ∧
      ClassGrowth (before result) after ∧ ClassGrowth result.initial scan.state ∧
      ClassGrowth result.initial body.state ∧ ClassGrowth result.initial result.final ∧
      Sz result.initial.base ∧ Sz result.final.base ∧
      result.code.classes = result.final.base.classes ∧
      (∀ x r,result.ctx.valueReg? x = some r → RegCls result.initial.base.classes r) ∧
      (∀ x r,result.ctx.valueReg? x = some r → RegCls result.code.classes r) ∧
      (∀ (j : Nat) (rs : List Reg × List Reg),result.initial.tryRegs[j]? = some rs →
        ∀ r ∈ rs.1 ++ rs.2,RegCls result.initial.base.classes r ∧ RegCls result.code.classes r) := by
  rcases stock_complete_terminal_scan_form_witness with
    ⟨result,p,rf,af,ranges,out,after,trace,emission,scan,body,i,
      lowered,scope,dominated,arity,prepared,fallback,checked,physical,build,
      mapped,clean,slot,data,named,hasOut,since,emissionRun,emitted,covered,
      scanRun,scanned,scanCoverage,scanSlot,bodyRun,bodyCoverage,member,ordinary,icov,ivalid⟩
  obtain ⟨growth,finalSize,table,finalValues,finalReserved⟩ := stock_lower_class_growth lowered
  obtain ⟨initialSize,initialValues,initialReserved⟩ := stock_build_classes build
  exact ⟨result,p,rf,af,ranges,out,after,trace,scan,body,i,
    lowered,scope,dominated,arity,prepared,fallback,checked,physical,build,named,hasOut,
    scanRun,bodyRun,member,ordinary,stock_named_classGrowth named,stock_scan_classGrowth scanRun,
    stock_scanBlock_classGrowth bodyRun,growth,initialSize,finalSize,table,initialValues,finalValues,
    fun j rs lookup r mem => ⟨initialReserved j rs lookup r mem,finalReserved j rs lookup r mem⟩⟩

end Backend.Stock.Proof.ClassGrowthWitnessDraft

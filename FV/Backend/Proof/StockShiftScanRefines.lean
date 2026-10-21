import FV.Backend.Proof.StockMulScanRefines
import FV.Backend.Proof.StockShiftCompleteSourceTransfer

/-! Complete shift source transfer through the shared scalar body boundary. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- All shift first-match families refine an actual indexed source step,
including its guarded DFG, memory/world relation and fresh-register frame. -/
theorem stock_lower_shift_scan_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : ScalarShift.Kind) {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held
  rw [position] at dfg values
  obtain ⟨ρ',execution,unchanged,post⟩ := ShiftComplete.record_source
    run scope dominated events records block statement current kind source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨w',executed,world⟩ := execution w
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ (SameWorld.nf world) memory
  · simpa only [advance,position] using post



theorem stock_lower_mixed_mul_record_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {record : ScanRecord} (records : record ∈ event.output.records)
    (family : MixedMulOrOmittedRecord f event.ctx bi record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  rcases family with old | mul
  · exact stock_lower_mixed_bnot_record_fall_refines run scope dominated events
      records old refines driver stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,ty,x,y,z,a,
      source,clif,results,statementResults,mapped⟩ := mul
    exact stock_lower_mul_scan_fall_refines run scope dominated events records
      block statement current source clif results statementResults mapped recorded emitted refines stable


/-- Original shift statements extend the complete shipped record family. -/
def MixedShiftOrOmittedRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop :=
  MixedMulOrOmittedRecord f ctx bi r ∨
    ∃ j b stm, f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧
      r.inst = blockStart f bi + j ∧ ∃ step, r.output.step = some step ∧
        step.decision = .emitted ∧ ∃ (kind : ScalarShift.Kind), ∃ info ty x y z a,
          ctx.insts[r.inst]? = some info ∧ info.clif = some (.binary kind.cop ty x y) ∧
          info.results = [z] ∧ stm.results = [z] ∧ ctx.valueReg? z = some (.vreg a .int)

theorem stock_lower_mixed_shift_body_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {indices : List Nat} {input : State} {body : BlockScan}
    (scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      indices input body)
    (retained : ∀ r ∈ body.records, r ∈ event.output.records)
    (families : ∀ r ∈ body.records, MixedShiftOrOmittedRecord f event.ctx bi r)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx bi) indices.reverse s s' →
      ∀ ρ w, GuardedScanRel f result event.ctx bi MR body.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
          some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx bi MR input s' ρ' w' := by
  apply scanned.fall_refines
  intro record member
  rcases families record member with old | mul
  · exact stock_lower_mixed_mul_record_fall_refines run scope dominated events
      (retained record member) old refines driver stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,kind,info,ty,x,y,z,a,
      source,clif,results,statementResults,mapped⟩ := mul
    exact stock_lower_shift_scan_fall_refines run scope dominated events (retained record member)
      block statement current kind source clif results statementResults mapped recorded emitted refines stable


theorem stock_lower_mixed_shift_record_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {record : ScanRecord} (records : record ∈ event.output.records)
    (family : MixedShiftOrOmittedRecord f event.ctx bi record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  rcases family with old | mul
  · exact stock_lower_mixed_mul_record_fall_refines run scope dominated events
      records old refines driver stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,kind,info,ty,x,y,z,a,
      source,clif,results,statementResults,mapped⟩ := mul
    exact stock_lower_shift_scan_fall_refines run scope dominated events records
      block statement current kind source clif results statementResults mapped recorded emitted refines stable


end Backend.Stock.Proof

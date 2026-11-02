import FV.Backend.Proof.StockCastScanRefines
import FV.Backend.Proof.StockBitFamily
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

theorem stock_lower_unary_bit_scan_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {op : Clif.UnaryOp} (unary : BitBody.Unary op)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary op ty x))
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
  obtain ⟨ρ',execution,unchanged,post⟩ := BitBody.unary_source
    run scope dominated events records block statement current unary source clif results statementResults
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


theorem stock_lower_rotate_scan_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (left : Bool)
    {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (ScalarRotate.rotateOp left) ty x y))
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
  obtain ⟨ρ',execution,unchanged,post⟩ := BitBody.rotate_source
    run scope dominated events records block statement current left source clif results statementResults
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



def MixedBitOrOmittedRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop :=
  MixedCastOrOmittedRecord f ctx bi r ∨
    (∃ j b stm,f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧ r.inst = blockStart f bi+j ∧
      ∃ step,r.output.step = some step ∧ step.decision = .emitted ∧
      ∃ info op ty x z a,ctx.insts[r.inst]? = some info ∧ info.clif = some (.unary op ty x) ∧
        info.results = [z] ∧ stm.results = [z] ∧ ctx.valueReg? z = some (.vreg a .int) ∧ BitBody.Unary op) ∨
    (∃ j b stm,f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧ r.inst = blockStart f bi+j ∧
      ∃ step,r.output.step = some step ∧ step.decision = .emitted ∧
      ∃ info left ty x y z a,ctx.insts[r.inst]? = some info ∧
        info.clif = some (.binary (ScalarRotate.rotateOp left) ty x y) ∧
        info.results = [z] ∧ stm.results = [z] ∧ ctx.valueReg? z = some (.vreg a .int))

theorem stock_lower_mixed_bit_record_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {record : ScanRecord} (records : record ∈ event.output.records)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastBody.SafeFormat stm.inst)
    (family : MixedBitOrOmittedRecord f event.ctx bi record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  rcases family with old | unary | rotated
  · exact stock_lower_mixed_cast_record_fall_refines_of_formats run scope dominated events records sourceFamily old refines driver stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,op,ty,x,z,a,
      source,clif,results,statementResults,mapped,supported⟩ := unary
    exact stock_lower_unary_bit_scan_fall_refines run scope dominated events records
      block statement current supported source clif results statementResults mapped recorded emitted refines stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,left,ty,x,y,z,a,
      source,clif,results,statementResults,mapped⟩ := rotated
    exact stock_lower_rotate_scan_fall_refines run scope dominated events records
      block statement current left source clif results statementResults mapped recorded emitted refines stable

theorem stock_lower_mixed_bit_body_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {indices : List Nat} {input : State} {body : BlockScan}
    (scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      indices input body)
    (retained : ∀ r ∈ body.records, r ∈ event.output.records)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastBody.SafeFormat stm.inst)
    (families : ∀ r ∈ body.records, MixedBitOrOmittedRecord f event.ctx bi r)
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
  exact stock_lower_mixed_bit_record_fall_refines run scope dominated events
    (retained record member) sourceFamily (families record member) refines driver stable
end Backend.Stock.Proof

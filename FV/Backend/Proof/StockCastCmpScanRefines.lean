module

public import FV.Backend.Proof.StockCastCmpCompleteSourceTransfer
public import FV.Backend.Proof.StockMinMaxScanRefines

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
theorem stock_lower_extend_scan_fall_refines_of_memory_formats {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst) (sg : Bool)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
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
  obtain ⟨unchanged,execution⟩ := CastComplete.extend_source_of_memory_formats
    run scope dominated events records block statement current sourceFamily sg source clif results statementResults
    mapped recorded emitted refines dfg values sourceStep
  obtain ⟨ρ',w',executed,world,post⟩ := execution w
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ world memory
  · simpa only [advance,position] using post

/-- Existing mixed families reuse their original leaf proofs. Only the cast
leaf needs the broader memory-only source-format variant. -/
theorem stock_lower_mixed_minmax_record_fall_refines_of_memory_formats {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {record : ScanRecord} (records : record ∈ event.output.records)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    (family : MixedMinMaxOrOmittedRecord f event.ctx bi record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  rcases family with (((old | extended | reduced) | unary | rotated) | popcount) | minmax
  · exact stock_lower_mixed_shift_record_fall_refines run scope dominated events records old refines driver stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,op,ty,x,z,a,
      source,clif,results,statementResults,mapped⟩ := extended
    cases op with
    | uextend =>
      exact stock_lower_extend_scan_fall_refines_of_memory_formats run scope dominated events records
        block statement current sourceFamily false source clif results statementResults mapped recorded emitted refines stable
    | sextend =>
      exact stock_lower_extend_scan_fall_refines_of_memory_formats run scope dominated events records
        block statement current sourceFamily true source clif results statementResults mapped recorded emitted refines stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,ty,x,z,a,
      source,clif,results,statementResults,mapped⟩ := reduced
    exact stock_lower_reduce_scan_fall_refines run scope dominated events records
      block statement current source clif results statementResults mapped recorded emitted stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,op,ty,x,z,a,
      source,clif,results,statementResults,mapped,supported⟩ := unary
    exact stock_lower_unary_bit_scan_fall_refines run scope dominated events records
      block statement current supported source clif results statementResults mapped recorded emitted refines stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,left,ty,x,y,z,a,
      source,clif,results,statementResults,mapped⟩ := rotated
    exact stock_lower_rotate_scan_fall_refines run scope dominated events records
      block statement current left source clif results statementResults mapped recorded emitted refines stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,ty,x,z,a,
      source,clif,results,statementResults,mapped⟩ := popcount
    exact stock_lower_popcount_scan_fall_refines run scope dominated events records
      block statement current source clif results statementResults mapped recorded emitted refines stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,unsigned,maximum,ty,x,y,z,a,
      source,clif,results,statementResults,mapped⟩ := minmax
    exact stock_lower_minmax_scan_fall_refines run scope dominated events records
      block statement current unsigned maximum source clif results statementResults mapped recorded emitted refines stable


end Backend.Stock.Proof

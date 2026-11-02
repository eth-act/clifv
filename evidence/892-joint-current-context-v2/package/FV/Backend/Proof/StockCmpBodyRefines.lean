import FV.Backend.Proof.StockMinMaxBodyRefines
import FV.Backend.Proof.StockCmpFamily
import FV.Backend.Proof.StockCmpScanRefines
namespace Backend.Stock.Proof.CmpBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm


theorem emitted_record_family {f : Clif.Function} {ctx : Ctx} {bi : Nat}
    {record : ScanRecord} {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {info : IInfo} {z a : Nat} (source : ctx.insts[record.inst]? = some info)
    (clif : info.clif = some stm.inst) (one : info.results = [z]) (results : stm.results = [z])
    (mapped : ctx.valueReg? z = some (.vreg a .int)) (family : Family stm.inst) :
    MixedCmpOrOmittedRecord f ctx bi record := by
  rcases family with old | ⟨cc,ty,x,y,shape⟩
  · exact Or.inl (MinMaxBody.emitted_record_family block statement current recorded emitted source clif one results mapped old)
  · have original : info.clif = some (.icmp cc ty x y) := by rw [clif,shape]
    exact Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
      info,cc,ty,x,y,z,a,source,original,one,results,mapped⟩

theorem actual_cmp_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b]) (family : ∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,MixedCmpOrOmittedRecord f event.ctx event.block record := by
  obtain ⟨term,body,split,sourceRecords⟩ := PureBody.actual_source_records run scope blocks
    (fun stm member => family_quiet (family stm member))
    (fun stm member => family_single (family stm member) f) events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,b',stm,block,statement,current,step,recorded,decision⟩ := sourceRecords record member
  have same : b' = b := Option.some.inj (block.symm.trans split.block)
  subst b'
  rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      ⟨j,b,stm,block,statement,current,step,recorded,Or.inl omitted⟩))))))))))
  · exact emitted_record_family block statement current recorded emitted source clif one results mapped
      (family stm (List.mem_of_getElem? statement))

/-- Comparison composes with every shipped scalar family
through the same original guarded body/source relation. -/
theorem actual_cmp_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b]) (family : ∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (driver : DriverSem isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,body,split,families⟩ := actual_cmp_families run scope blocks family events
  have sourceFamily : ∀ b' ∈ f.blocks,∀ stm ∈ b'.body,CastComplete.MemoryFormat stm.inst := by
    intro b' member stm present
    have same : b' = b := by simpa only [blocks,List.mem_singleton] using member
    subst b'
    exact family_formats (family stm present)
  refine ⟨term,body,split,?_⟩
  intro s s' source ρ w held
  apply stock_lower_mixed_cmp_body_fall_refines run scope dominated events
    split.scanned split.retained sourceFamily families refines driver stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held
end Backend.Stock.Proof.CmpBody

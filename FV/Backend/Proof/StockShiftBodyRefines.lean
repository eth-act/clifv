import FV.Backend.Proof.StockMulBodyRefines
import FV.Backend.Proof.StockShiftScanRefines
namespace Backend.Stock.Proof.ShiftBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def Family (inst : Clif.Inst) : Prop :=
  MulBody.Family inst ∨ ∃ (kind : ScalarShift.Kind) (ty : Clif.Ty) (x y : Nat), inst = .binary kind.cop ty x y

theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with old | ⟨kind,ty,x,y,rfl⟩
  · exact MulBody.family_pure old
  · cases kind <;> rfl

theorem family_quiet {inst : Clif.Inst} (family : Family inst) : colored inst = false := by
  rcases family with old | ⟨kind,ty,x,y,rfl⟩
  · exact MulBody.family_quiet old
  · cases kind <;> rfl

theorem family_single {inst : Clif.Inst} (family : Family inst) (f : Clif.Function) :
    (inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
  rcases family with old | ⟨kind,ty,x,y,rfl⟩
  · exact MulBody.family_single old f
  · cases kind <;> rfl

private theorem mul_record_family {f : Clif.Function} {ctx : Ctx} {bi : Nat}
    {record : ScanRecord} {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {info : IInfo} {z a : Nat} (source : ctx.insts[record.inst]? = some info)
    (clif : info.clif = some stm.inst) (one : info.results = [z]) (results : stm.results = [z])
    (mapped : ctx.valueReg? z = some (.vreg a .int)) (family : MulBody.Family stm.inst) :
    MixedMulOrOmittedRecord f ctx bi record := by
  rcases family with old | ⟨ty,x,y,shape⟩
  · exact Or.inl (BnotBody.emitted_record_family block statement current recorded emitted source clif one results mapped old)
  · have original : info.clif = some (.binary .imul ty x y) := by rw [clif,shape]
    exact Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
      info,ty,x,y,z,a,source,original,one,results,mapped⟩

/-- Original syntax and actual whole lowering derive retained coverage internally. -/
theorem actual_shift_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b]) (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, MixedShiftOrOmittedRecord f event.ctx event.block record := by
  obtain ⟨term,body,split,sourceRecords⟩ := PureBody.actual_source_records run scope blocks
    (fun stm member => family_quiet (family stm member))
    (fun stm member => family_single (family stm member) f) events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,b',stm,block,statement,current,step,recorded,decision⟩ := sourceRecords record member
  have same : b' = b := Option.some.inj (block.symm.trans split.block)
  subst b'
  rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      ⟨j,b,stm,block,statement,current,step,recorded,Or.inl omitted⟩)))))
  · rcases family stm (List.mem_of_getElem? statement) with old | ⟨kind,ty,x,y,shape⟩
    · exact Or.inl (mul_record_family block statement current recorded emitted source clif
        one results mapped old)
    · have original : info.clif = some (.binary kind.cop ty x y) := by rw [clif,shape]
      exact Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
        kind,info,ty,x,y,z,a,source,original,one,results,mapped⟩

/-- Shifts, fused bitfields and all shipped pure records compose in source order. -/
theorem actual_shift_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b]) (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (driver : DriverSem isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,body,split,families⟩ := actual_shift_families run scope blocks family events
  refine ⟨term,body,split,?_⟩
  intro s s' source ρ w held
  apply stock_lower_mixed_shift_body_fall_refines run scope dominated events
    split.scanned split.retained families refines driver stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held
end Backend.Stock.Proof.ShiftBody

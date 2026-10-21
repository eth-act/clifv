import FV.Backend.Proof.StockConstantBodyRefines
import FV.Backend.Proof.StockBnotScanRefines

namespace Backend.Stock.Proof.BnotBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Original pure syntax: retain every shipped constant/logical/mixed instruction
and add integer NOT. No selected-rule or output premise. -/
def Family (inst : Clif.Inst) : Prop :=
  ConstantBody.Family inst ∨ ∃ (ty : Clif.Ty) (x : Nat), inst = .unary .bnot ty x

/-- Source execution uses the common pure-instruction semantics. -/
theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with old | ⟨ty,x,rfl⟩
  · exact ConstantBody.family_pure old
  · rfl

/-- Original syntax and successful whole lowering supply all actual record
coverage and mappings, including omitted statements and fused NOT operands. -/
theorem actual_bnot_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, MixedBnotOrOmittedRecord f event.ctx event.block record := by
  have quiet : ∀ stm ∈ b.body, colored stm.inst = false := by
    intro stm member
    rcases family stm member with ((⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩) | ⟨ty,imm,shape⟩) | ⟨ty,x,shape⟩
    all_goals rw [shape]
    · cases subtract <;> rfl
    · rfl
    · cases kind <;> rfl
    · rfl
    · rfl
  have single : ∀ stm ∈ b.body,
      (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
    intro stm member
    rcases family stm member with ((⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩) | ⟨ty,imm,shape⟩) | ⟨ty,x,shape⟩
    all_goals rw [shape]
    all_goals rfl
  obtain ⟨term,body,split,sourceRecords⟩ := PureBody.actual_source_records run scope blocks quiet single events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,b',stm,block,statement,current,step,recorded,decision⟩ := sourceRecords record member
  have same : b' = b := Option.some.inj (block.symm.trans split.block)
  subst b'
  rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨j,b,stm,block,statement,current,step,recorded,Or.inl omitted⟩)))
  · rcases family stm (List.mem_of_getElem? statement) with
      ((⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩) | ⟨ty,imm,shape⟩) | ⟨ty,x,shape⟩
    · have original : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y) := by rw [clif,shape]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
        subtract,info,ty,x,y,z,a,source,original,one,results,mapped⟩)))
    · have original : info.clif = some (.select ty c x y) := by rw [clif,shape]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨j,b,stm,block,statement,current,step,recorded,Or.inr
        ⟨emitted,info,ty,c,x,y,z,a,source,original,one,results,mapped⟩⟩)))
    · have original : info.clif = some (.binary kind.cop ty x y) := by rw [clif,shape]
      exact Or.inl (Or.inl (Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
        kind,info,ty,x,y,z,a,source,original,one,results,mapped⟩))
    · have original : info.clif = some (.iconst ty imm) := by rw [clif,shape]
      exact Or.inl (Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
        info,ty,imm,z,a,source,original,one,results,mapped⟩)
    · have original : info.clif = some (.unary .bnot ty x) := by rw [clif,shape]
      exact Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
        info,ty,x,z,a,source,original,one,results,mapped⟩

/-- Whole pure source-body refinement reuses NOT and shipped record proofs,
with the original availability/DFG guard and memory/world relation. -/
theorem actual_bnot_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,body,split,families⟩ := actual_bnot_families run scope blocks family events
  refine ⟨term,body,split,?_⟩
  intro s s' source ρ w held
  apply stock_lower_mixed_bnot_body_fall_refines run scope dominated events
    split.scanned split.retained families refines driver stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held

end Backend.Stock.Proof.BnotBody

import FV.Backend.Proof.StockArithmeticBodyRefines
import FV.Backend.Proof.StockLogicalScanRefines
import FV.Backend.Proof.StockPureBodyFamilies

/-! Source-syntax coverage for complete select/arithmetic/logical bodies. -/
namespace Backend.Stock.Proof.LogicalBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Input syntax only; actual matching, binding and record decisions are derived. -/
def Family (inst : Clif.Inst) : Prop :=
  (∃ subtract : Bool, ∃ ty x y,
    inst = .binary (if subtract then .isub else .iadd) ty x y) ∨
  (∃ ty c x y, inst = .select ty c x y) ∨
  (∃ kind : LogicalSelected.Kind, ∃ ty x y, inst = .binary kind.cop ty x y)

/-- Original syntax and successful lowering supply every body record's family,
source result, actual mapped register and emission/omission decision internally. -/
theorem actual_logical_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, MixedLogicalOrOmittedRecord f event.ctx event.block record := by
  have quiet : ∀ stm ∈ b.body, colored stm.inst = false := by
    intro stm member
    rcases family stm member with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩
    all_goals rw [shape]
    · cases subtract <;> rfl
    · rfl
    · cases kind <;> rfl
  have single : ∀ stm ∈ b.body,
      (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
    intro stm member
    rcases family stm member with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩
    all_goals rw [shape]
    all_goals rfl
  obtain ⟨term,body,split,sourceRecords⟩ := PureBody.actual_source_records run scope blocks quiet single events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,b',stm,block,statement,current,step,recorded,decision⟩ := sourceRecords record member
  have same : b' = b := Option.some.inj (block.symm.trans split.block)
  subst b'
  rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
  · exact Or.inl (Or.inl ⟨j,b,stm,block,statement,current,step,recorded,Or.inl omitted⟩)
  · rcases family stm (List.mem_of_getElem? statement) with
      ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩
    · have original : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y) := by rw [clif,shape]
      exact Or.inl (Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
        subtract,info,ty,x,y,z,a,source,original,one,results,mapped⟩)
    · have original : info.clif = some (.select ty c x y) := by rw [clif,shape]
      exact Or.inl (Or.inl ⟨j,b,stm,block,statement,current,step,recorded,Or.inr
        ⟨emitted,info,ty,c,x,y,z,a,source,original,one,results,mapped⟩⟩)
    · have original : info.clif = some (.binary kind.cop ty x y) := by rw [clif,shape]
      exact Or.inr ⟨j,b,stm,block,statement,current,step,recorded,emitted,
        kind,info,ty,x,y,z,a,source,original,one,results,mapped⟩

/-- Whole ordinary-body refinement derives its record coverage and maps from
source syntax. The original indexed availability/DFG and memory/world boundary
is retained, including unused/dead statements and all prior body families. -/
theorem actual_logical_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,body,split,families⟩ := actual_logical_families run scope blocks family events
  refine ⟨term,body,split,?_⟩
  intro s s' source ρ w held
  apply stock_lower_mixed_logical_body_fall_refines run scope dominated events
    split.scanned split.retained families refines stable s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held

end Backend.Stock.Proof.LogicalBody

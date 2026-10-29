module

public import FV.Backend.Proof.StockBodyScanRefines
public import FV.Backend.Proof.StockAddSubAllSourceValues

@[expose] public section

/-! Actual add/sub record semantics composed into the ordinary-body scan relation.
The syntactic family partition remains internal partial coverage; it is not a
new compiler acceptance premise. Existing select/omission variants are retained. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
theorem stock_lower_addsub_scan_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (subtract : Bool) {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
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
  obtain ⟨u,v,ρ',getX,getY,execution,value,unchanged,kept,post⟩ :=
    ScalarAddSub.stock_lower_addsub_source_by_instruction
      run scope dominated events records block statement current subtract source clif results statementResults
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

def SelectAddSubOrOmittedRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop :=
  SelectOrOmittedRecord f ctx bi r ∨
    ∃ j b stm, f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧
      r.inst = blockStart f bi + j ∧ ∃ step, r.output.step = some step ∧
        step.decision = .emitted ∧ ∃ subtract : Bool, ∃ info ty x y z a,
          ctx.insts[r.inst]? = some info ∧
          info.clif = some (.binary (if subtract then .isub else .iadd) ty x y) ∧
          info.results = [z] ∧ stm.results = [z] ∧ ctx.valueReg? z = some (.vreg a .int)

theorem stock_lower_select_addsub_omitted_body_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {indices : List Nat} {input : State} {body : BlockScan}
    (scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      indices input body)
    (retained : ∀ r ∈ body.records, r ∈ event.output.records)
    (families : ∀ r ∈ body.records, SelectAddSubOrOmittedRecord f event.ctx bi r)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx bi) indices.reverse s s' →
      ∀ ρ w, GuardedScanRel f result event.ctx bi MR body.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
          some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx bi MR input s' ρ' w' := by
  apply scanned.fall_refines
  intro r member
  rcases families r member with old | addsub
  ·
    obtain ⟨j,b,stm,block,statement,current,step,recorded,kind⟩ := old
    rcases kind with omitted | ⟨emitted,info,ty,c,x,y,z,a,source,clif,results,statementResults,mapped⟩
    · exact stock_lower_omitted_scan_fall_refines run scope dominated events (retained r member)
        block statement current recorded omitted
    · exact stock_lower_select_scan_fall_refines run scope dominated events (retained r member)
        block statement current source clif results statementResults mapped recorded emitted refines stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,subtract,info,ty,x,y,z,a,
      source,clif,results,statementResults,mapped⟩ := addsub
    exact stock_lower_addsub_scan_fall_refines run scope dominated events (retained r member)
      block statement current subtract source clif results statementResults mapped recorded emitted refines stable

end Backend.Stock.Proof

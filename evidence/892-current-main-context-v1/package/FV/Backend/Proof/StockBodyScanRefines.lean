import FV.Backend.Proof.StockGuardedOmission

/-! Concrete ordinary-body composition for the discharged select and omission
cases. The syntactic family partition is an internal partial-coverage boundary,
not an additional condition on programs accepted by the compiler. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- Structural cases whose ordinary-source scan semantics have been discharged.
There is no machine-execution or source-refinement certificate in this predicate. -/
def SelectOrOmittedRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop :=
  ∃ j b stm, f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧
    r.inst = blockStart f bi + j ∧ ∃ step, r.output.step = some step ∧
      (step.decision = .omitted ∨
        step.decision = .emitted ∧ ∃ info ty c x y z a,
          ctx.insts[r.inst]? = some info ∧ info.clif = some (.select ty c x y) ∧
          info.results = [z] ∧ stm.results = [z] ∧ ctx.valueReg? z = some (.vreg a .int))

/-- Compose the actual emitted chunks for an ordinary source body containing
selects and omissions. The proof discharges every local execution obligation by
its concrete family theorem, including post DFG and memory/world transport. -/
theorem stock_lower_select_omitted_body_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {indices : List Nat} {input : State} {body : BlockScan}
    (scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      indices input body)
    (retained : ∀ r ∈ body.records, r ∈ event.output.records)
    (families : ∀ r ∈ body.records, SelectOrOmittedRecord f event.ctx bi r)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx bi) indices.reverse s s' →
      ∀ ρ w, GuardedScanRel f result event.ctx bi MR body.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
          some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx bi MR input s' ρ' w' := by
  apply scanned.fall_refines
  intro r member
  obtain ⟨j,b,stm,block,statement,current,step,recorded,kind⟩ := families r member
  rcases kind with omitted | ⟨emitted,info,ty,c,x,y,z,a,source,clif,results,statementResults,mapped⟩
  · exact stock_lower_omitted_scan_fall_refines run scope dominated events (retained r member)
      block statement current recorded omitted
  · exact stock_lower_select_scan_fall_refines run scope dominated events (retained r member)
      block statement current source clif results statementResults mapped recorded emitted refines stable
end Backend.Stock.Proof

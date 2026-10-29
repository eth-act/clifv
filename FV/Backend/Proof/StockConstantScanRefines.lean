module

public import FV.Backend.Proof.StockLogicalScanRefines
public import FV.Backend.Proof.StockConstantCompleteValues

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- Original integer constants refine the indexed source step, deriving actual
selection and alias-renaming facts internally from the existing driver contract. -/
theorem stock_lower_constant_scan_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (statementResults : stm.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  have semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i := by
    intro aliases i
    apply driver.rename _ (aliasNum aliases) ?_ i
    refine ⟨fun n c => resolve_vreg aliases _ n c, ?_⟩
    intro r hr
    cases r with
    | vreg n c => exact False.elim (hr n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  have transfer := ConstantComplete.record_source run scope dominated events records block statement current
    source clif statementResults results mapped recorded emitted refines semantics
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held
  rw [position] at dfg values
  obtain ⟨ρ',w',executed,postMemory,post⟩ := transfer env cp (fun cm w => MR s.2.1.slots cm w)
    (fun cm w w' world mem => stable _ _ _ _ (SameWorld.nf world) mem)
    _ _ _ _ ρ w sourceStep memory values
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots]; exact postMemory
  · simpa only [advance,position] using post

/-- Internal partition extending the shipped logical/mixed records with constants. -/
def MixedConstantOrOmittedRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop :=
  MixedLogicalOrOmittedRecord f ctx bi r ∨
    ∃ j b stm, f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧
      r.inst = blockStart f bi + j ∧ ∃ step, r.output.step = some step ∧
        step.decision = .emitted ∧ ∃ (info : IInfo) (ty : Clif.Ty) (imm : BitVec ty.width) (x a : Nat),
          ctx.insts[r.inst]? = some info ∧ info.clif = some (.iconst ty imm) ∧
          info.results = [x] ∧ stm.results = [x] ∧ ctx.valueReg? x = some (.vreg a .int)

/-- Complete constant and previous logical/mixed records compose in actual scan
order, with the same original availability and world/memory relation. -/
theorem stock_lower_mixed_constant_body_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {indices : List Nat} {input : State} {body : BlockScan}
    (scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      indices input body)
    (retained : ∀ r ∈ body.records, r ∈ event.output.records)
    (families : ∀ r ∈ body.records, MixedConstantOrOmittedRecord f event.ctx bi r)
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
  rcases families record member with old | constant
  · exact stock_lower_mixed_logical_record_fall_refines run scope dominated events
      (retained record member) old refines stable
  · obtain ⟨j,b,stm,block,statement,current,step,recorded,emitted,info,ty,imm,x,a,
      source,clif,results,statementResults,mapped⟩ := constant
    exact stock_lower_constant_scan_fall_refines run scope dominated events (retained record member)
      block statement current source clif results statementResults mapped recorded emitted refines driver stable

end Backend.Stock.Proof

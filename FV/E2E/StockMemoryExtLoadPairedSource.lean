import FV.Backend.Proof.StockMemoryExtLoadScanRefines
import FV.Backend.Proof.StockMemoryExtLoadPairedRecord
import FV.E2E.PairDriverU

namespace E2E.StockMemory.ExtendedRoots
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Pair the real source step with one exact post-register file under guarded
reads. Existing source transfer supplies both original-frame postconditions;
semantic inclusion transfers the guarded executions without re-proving the
single-world DFG, demand, frame or result-binding arguments. -/
theorem stock_lower_extending_load_paired_source_step (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0)) (results : info.results = [z])
    (statementResults : stm.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none) (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem isemG : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    (guardedMemory : MemRefinesR Rd F sb syms isemG)
    (subGuarded : ∀ i us w r,isemG i us w = some r → isem i us w = some r)
    {fr fr' : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w w' : Arm.ArmState}
    (memory : MR fr.slots cm w) (otherMemory : MR fr.slots cm w') (reads : InitIn Rd cm)
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (v : Clif.Val) (ρ' : Nat → CV) (t t' : Arm.ArmState),
      Clif.evalInst fr cm (.load kind.sourceOp ty flags x 0) = .ok ([v],cm') ∧
      seqRun isemG (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' t) ∧
      seqRun isemG (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w' = some (.fall ρ' t') ∧
      SameWorld F t w ∧ SameWorld F t' w' ∧ MR fr'.slots cm' t ∧ MR fr'.slots cm' t' ∧
      VHolds v (ρ' record.input.base.nextVreg) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨v,baseRegs,baseWorld,evaluated,baseRun,baseSame,baseMemory,value,post⟩ :=
    stock_lower_extending_load_source_step kind run scope dominated events records block statement current
      source clif results statementResults mapped parameter pointer recorded emitted
      stable memorySem memoryOk memory dfg held sourceStep
  obtain ⟨otherValue,otherRegs,otherWorld,otherEval,otherRun,otherSame,otherMemory',otherValueHeld,otherPost⟩ :=
    stock_lower_extending_load_source_step kind run scope dominated events records block statement current
      source clif results statementResults mapped parameter pointer recorded emitted
      stable memorySem memoryOk otherMemory dfg held sourceStep
  have needed := stock_lower_extending_load_operand_coverage kind run scope dominated events records block statement current
    source clif results mapped parameter pointer recorded emitted
  have restrictedGet : (restrict fr (availOf f (availIn f result.ctx) bi j)).get x = fr.get x := by
    simp only [Clif.Frame.get,restrict_regs_of_mem needed.2]
  have restrictedEval : Clif.evalInst (restrict fr (availOf f (availIn f result.ctx) bi j)) cm
      (.load kind.sourceOp ty flags x 0) = .ok ([v],cm') := by
    simpa only [Clif.evalInst,restrictedGet] using evaluated
  have restrictedHeld : ValueHeld event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j))
      (fun k => ρ (aliasNum result.final.alias k)) x := by
    intro val lookup
    rw [restrict_regs_of_mem needed.2] at lookup
    exact held x needed val lookup
  obtain ⟨pairedRegs,t,t',first,second,same,otherSame'⟩ := stock_lower_extending_load_paired_record kind
    run scope dominated events records source clif results mapped parameter pointer recorded emitted
    guardedMemory memoryOk (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (ρ := ρ)
    memory otherMemory reads dfg restrictedHeld restrictedEval
  have firstBase := seqRun_sub subGuarded _ _ _ _ first
  have secondBase := seqRun_sub subGuarded _ _ _ _ second
  obtain ⟨fileEq,worldEq⟩ := SeqEnd.fall.inj (Option.some.inj (baseRun.symm.trans firstBase))
  obtain ⟨otherFileEq,otherWorldEq⟩ := SeqEnd.fall.inj (Option.some.inj (otherRun.symm.trans secondBase))
  refine ⟨v,pairedRegs,t,t',evaluated,first,second,same,otherSame',?_,?_,?_,?_⟩
  · rw [← worldEq]; exact baseMemory
  · rw [← otherWorldEq]; exact otherMemory'
  · rw [← fileEq]; exact value
  · rw [← fileEq]; exact post

/-- Paired actual loads retain both complete original indexed scan guards. -/
theorem stock_lower_extending_load_scan_pair (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0)) (results : info.results = [z])
    (statementResults : stm.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none) (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem isemG : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    (guardedMemory : MemRefinesR Rd F sb syms isemG)
    (subGuarded : ∀ i us w r,isemG i us w = some r → isem i us w = some r)
    {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s',IndexedSourceInst env cp f event.ctx bi record.inst s s' →
      ∀ (ρ : Nat → CV) (w w' : Arm.ArmState),InitIn Rd s.2.2 →
      GuardedScanRel f result event.ctx bi MR record.output.state s ρ w →
      GuardedScanRel f result event.ctx bi MR record.output.state s ρ w' →
      ∃ ρ' t t',seqRun isemG (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' t) ∧
        seqRun isemG (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w' = some (.fall ρ' t') ∧
        GuardedScanRel f result event.ctx bi MR record.input s' ρ' t ∧
        GuardedScanRel f result event.ctx bi MR record.input s' ρ' t' := by
  intro s s' sourceIndex ρ w w' reads before otherBefore
  obtain ⟨indexed,advance,sourceStep⟩ := sourceIndex
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func,dfg,memory,held⟩ := before
  have otherMemory := otherBefore.2.2.1
  rw [position] at dfg held
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨v,ρ',t,t',evaluated,first,second,same,otherSame,memory',otherMemory',value,post⟩ :=
    stock_lower_extending_load_paired_source_step kind ty run scope dominated events records block statement current
      source clif results statementResults mapped parameter pointer recorded emitted
      stable memorySem memoryOk guardedMemory subGuarded memory otherMemory reads dfg held sourceStep
  have postFunc : s'.2.1.func = f := by
    obtain ⟨info',inst,vals,regs,rest,_,_,_,_,_,updated⟩ := sourceStep
    change s'.2.1 = _ at updated
    rw [updated]
    exact func
  have defined : DFGCons event.ctx (restrict s'.2.1 (availOf f (availIn f result.ctx) bi s'.1)) := by
    simpa only [advance,position] using postDFG
  have values : ValuesHeld (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi s'.1) event.ctx s'.2.1
      (fun k => ρ' (aliasNum result.final.alias k)) := by
    simpa only [advance,position] using post
  exact ⟨ρ',t,t',first,second,⟨postFunc,defined,memory',values⟩,⟨postFunc,defined,otherMemory',values⟩⟩

end E2E.StockMemory.ExtendedRoots

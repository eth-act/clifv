import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockReduceRecord
namespace Backend.Stock.Proof.ScalarCast.Reduce
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Truncating an already-held original value needs no normalization assumption
about the register's unobserved upper bits. -/
theorem stock_reduce_holds {val : Clif.Val} {ty : Clif.Ty} (fits : ty.width ≤ val.ty.width)
    {r : CV} (held : VHolds val r) : VHolds ⟨ty,Clif.Sem.ireduce ty.width val.bits⟩ r := by
  change r.setWidth ty.width = val.bits.setWidth ty.width
  change r.setWidth val.ty.width = val.bits at held
  rw [← held,BitVec.setWidth_setWidth_of_le _ fits]
/-- An actual source reduction supplies narrowing validity internally. The
empty real record leaves machine registers and source memory unchanged, while
its retained alias binding establishes the demanded/available original result. -/
theorem stock_lower_reduce_available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.ireduce ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some rule_lower_2146.id)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {val : Clif.Val} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some val)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm'))
    (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) :
    ∃ nx,event.ctx.valueReg? x = some (.vreg nx .int) ∧ step.results = [[.vreg nx .int]] ∧
      record.output.emitted = #[] ∧ aliasNum result.final.alias a = aliasNum result.final.alias nx ∧
      cm' = cm ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ ∧
      VHolds ⟨ty,Clif.Sem.ireduce ty.width val.bits⟩ (ρ (aliasNum result.final.alias a)) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ (aliasNum result.final.alias k)) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have rawEval : Clif.evalInst fr cm (.ireduce ty x) = .ok (vals,cm') := by
    simpa only [instOutcome] using evaluated
  obtain ⟨input,inputLookup,narrow,valuesEq,memEq⟩ := evalInst_ireduce_ok rawEval
  have availableX := restrict_regs_isSome (by rw [getX]; rfl)
  have originalX : fr.regs x = some val := by
    have known := getX
    rw [restrict_regs_of_mem availableX] at known
    exact known
  have sameInput := Option.some.inj (inputLookup.symm.trans originalX)
  subst input
  obtain ⟨nx,sourceMap,output,code,demand,endpoints⟩ := stock_lower_reduce_record_receipts
    run scope dominated events records source clif results mapped recorded emitted selectedId
  have bound := (Extent.lower_mapped_demand_bounds run scope events records sourceMap).1
  have neededX : Demanded record.output.state x := by
    rw [Demanded,demand,(mark_demand record.input x bound).1]
    omega
  have inputValue := held.read ⟨neededX,availableX⟩ originalX sourceMap
  have value := stock_reduce_holds (Nat.le_of_lt narrow) inputValue
  have resultValue : VHolds ⟨ty,Clif.Sem.ireduce ty.width val.bits⟩ (ρ (aliasNum result.final.alias a)) := by
    rw [endpoints]; exact value
  have installed : ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
      (withValue fr z ⟨ty,Clif.Sem.ireduce ty.width val.bits⟩) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro v required oldVal lookup
    by_cases equal : v = z
    · subst v
      simp only [withValue,eq_self,ite_true] at lookup
      cases lookup
      exact ⟨a,mapped,resultValue⟩
    · simp only [withValue,ite_eq_right equal] at lookup
      have before := available_before_of_after_not_result block statement required.2
        (by simpa only [statementResults,List.mem_singleton] using equal)
      have needed : Demanded record.output.state v := by
        intro zero
        have count := stock_lower_record_demand_mono run events records recorded emitted v
        change record.output.state.demand[v]! = 0 at zero
        rw [zero] at count
        exact required.1 (Nat.eq_zero_of_le_zero count)
      exact held v ⟨needed,before⟩ oldVal lookup
  have evaluatedValue := evaluated
  rw [valuesEq] at evaluatedValue
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  refine ⟨nx,sourceMap,output,code,endpoints,memEq,?_,resultValue,post⟩
  rw [code]
  exact prun_nil _
end Backend.Stock.Proof.ScalarCast.Reduce

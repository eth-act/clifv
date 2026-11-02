import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockBmaskRecord
import FV.Backend.Proof.StockGuardedRecordValues

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual retained bmask records consume original available values through
the final resolver and install their bound result in the guarded post-frame.
The input/output types remain independent. -/
theorem stock_lower_bmask_available_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.bmask ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {value : Clif.Val} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some value) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world
        (fun ρ' _ => VHolds ⟨ty,Clif.Sem.bmask value.bits⟩ (ρ' d) ∧
          (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx (withValue fr z ⟨ty,Clif.Sem.bmask value.bits⟩)
              (fun k => ρ' (aliasNum result.final.alias k))) := by
  obtain ⟨wi,nx,next,width,typed,mapX,_,output,nextEq,stateEq,code,frontier⟩ :=
    stock_lower_bmask_record run scope events records source clif results mapped recorded emitted
  let d := bmaskResultNum wi record.input.base.nextVreg
  have fresh : record.input.base.nextVreg ≤ d := by
    rcases width with rfl | rfl | rfl | rfl <;> simp [d,bmaskResultNum]
  have inside : d < record.output.state.base.nextVreg := by
    rw [frontier]
    rcases width with rfl | rfl | rfl | rfl <;> simp [d,bmaskResultNum,bmaskAlloc]
  have extent := (Extent.lower_mapped_demand_bounds run scope events records mapX).1
  have needed : Demanded record.output.state x := by
    rw [stateEq,nextEq]
    change ((scanState record.input record.inst).mark x).demand[x]! ≠ 0
    have marked := (mark_demand (scanState record.input record.inst) x
      (by simpa only [scanState_demands] using extent)).1
    omega
  have available := restrict_regs_isSome (by rw [getX]; rfl)
  have originalLookup := getX
  rw [restrict_regs_of_mem available] at originalLookup
  have inputValue := held.read ⟨needed,available⟩ originalLookup mapX
  have inputType := dfg.2 x _ value typed getX
  have inv := (stock_lower_record_context run scope events).1
  have outputType := (stock_bmask_source_data inv source clif).1
  have boundedScan := stock_lower_blockScanAliasBounds run event events record records
  have scanFrontier : (scanState record.input record.inst).base.nextVreg = record.input.base.nextVreg := by
    unfold scanState; dsimp only; split <;> rfl
  have bounded : result.final.alias.size ≤ record.input.base.nextVreg := by
    simpa only [scanFrontier] using boundedScan
  have defs : ∀ m ∈ record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs m,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
    rw [code,frontier]
    exact stock_bmask_defs bounded
  refine ⟨d,output,⟨fresh,inside⟩,?_⟩
  intro world
  have execution := stock_bmask_resolved refines width outputType inputType bounded inputValue world
  rw [← code] at execution
  refine execution.imp ?_
  intro ρ' w' executed ⟨valueHeld,kept⟩
  refine ⟨valueHeld,?_,?_⟩
  · simpa only [frontier] using kept
  · exact stock_lower_fresh_record_values_auto_demand run scope dominated events records block statement current
      source clif results statementResults mapped recorded emitted output fresh held defs executed valueHeld

/-- The actual original source step supplies its operand and memory behavior;
retained selection/binding then transports the demanded and available values
to that step's real post-frame. -/
theorem stock_lower_bmask_available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.bmask ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (value : Clif.Val) (d : Nat),fr.regs x = some value ∧ cm' = cm ∧
      step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world
        (fun ρ' _ => VHolds ⟨ty,Clif.Sem.bmask value.bits⟩ (ρ' d) ∧
          (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k))) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.bmask ty x) = .ok (vals,cm') := by
    simpa [instOutcome] using evaluated
  obtain ⟨value,lookup,values,memory⟩ := evalInst_bmask_ok plain
  have available := stock_lower_record_args_available run scope dominated events block statement
    current source clif x (by simp [Driver.instArgs])
  have input : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some value := by
    rw [restrict_regs_of_mem available]; exact lookup
  obtain ⟨d,output,bounds,execution⟩ := stock_lower_bmask_available_values run scope dominated events records
    block statement current source clif results statementResults mapped recorded emitted refines dfg held input
  refine ⟨value,d,lookup,memory,output,bounds,?_⟩
  intro world
  refine (execution world).imp ?_
  intro ρ' w' executed ⟨valueHeld,kept,post⟩
  refine ⟨valueHeld,kept,?_⟩
  apply source_single_result_values source clif results sourceStep _ post
  rw [values] at evaluated
  exact evaluated

end Backend.Stock.Proof.ScalarMask

import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockCmpZero8OriginalLeftRecordValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual retained comparison execution transfers the original guarded source
relation to the real original source-step frame, not merely a constructed result
frame. Original restricted DFG and demanded/available guards are retained. -/
theorem stock_lower_cmp_zero8_original_left_source_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} (nonzero : Bool) {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp (if nonzero then .ne else .eq) .i8 y x))
    (typeX : event.ctx.valueType? x = some (.int 8))
    
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : event.ctx.defInst? y = some constantJ) (constantFound : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (normalized : u64 literal = 0)
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV} {u v : BitVec 8}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x .i8 = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y .i8 = .ok v)
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ d,step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (if nonzero then .ne else .eq) v u)⟩ (ρ' d) ∧ (∀ k,k ≠ d → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have rawGetX : fr.getAs x .i8 = .ok u :=
    (getAs_congr (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (fr' := fr)
      (x := x) (ty := .i8) (restrict_regs_of_mem availableX).symm).trans getX
  have rawGetY : fr.getAs y .i8 = .ok v :=
    (getAs_congr (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (fr' := fr)
      (x := y) (ty := .i8) (restrict_regs_of_mem availableY).symm).trans getY
  have restored := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have eval' : instOutcome env cp fr cm (.icmp (if nonzero then .ne else .eq) .i8 y x) =
      .ok ([⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (if nonzero then .ne else .eq) v u)⟩],cm) := by
    simp [instOutcome,Clif.evalInst,rawGetX,rawGetY,Clif.Sem.icmp]
    exact ⟨v,rfl,u,rfl,rfl⟩
  rw [eval'] at evaluated
  cases evaluated
  obtain ⟨d,output,lower,upper,execution⟩ := stock_lower_cmp_zero8_original_left_available_values run scope dominated events records
    foundBlock foundStmt current nonzero source clif typeX defined constantFound data normalized results statementResults mapped
    recorded emitted refines dfg getX getY held
  refine ⟨d,output,lower,upper,rfl,?_⟩
  intro world
  exact (execution world).imp (fun ρ' _ _ ⟨value,kept,post⟩ =>
    ⟨value,kept,source_single_result_values source clif results restored eval' post⟩)
/-- Successful original source execution and original dominance derive both
availability-restricted comparison getters internally. -/
theorem stock_lower_cmp_zero8_original_left_source_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {info : IInfo} (nonzero : Bool) {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp (if nonzero then .ne else .eq) .i8 y x))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u v,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x .i8 = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y .i8 = .ok v := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.icmp (if nonzero then .ne else .eq) .i8 y x) = .ok (vals,cm') := evaluated
  obtain ⟨v,u,getY,getX,values,memory⟩ := evalInst_icmp_ok plain
  have availableX := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif x (by simp [Driver.instArgs])
  have availableY := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif y (by simp [Driver.instArgs])
  exact ⟨u,v,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := .i8) (restrict_regs_of_mem availableX)).trans getX,
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := .i8) (restrict_regs_of_mem availableY)).trans getY⟩
/-- Original source execution supplies both getters internally; the earlier
getter-explicit source-transfer theorem remains available unchanged. -/
theorem stock_lower_cmp_zero8_original_left_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} (nonzero : Bool) {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp (if nonzero then .ne else .eq) .i8 y x))
    (typeX : event.ctx.valueType? x = some (.int 8))
    
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : event.ctx.defInst? y = some constantJ) (constantFound : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (normalized : u64 literal = 0)
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u : BitVec 8,∃ v : BitVec 8,∃ d,step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (if nonzero then .ne else .eq) v u)⟩ (ρ' d) ∧ (∀ k,k ≠ d → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨u,v,getX,getY⟩ := stock_lower_cmp_zero8_original_left_source_operands run scope dominated events
    foundBlock foundStmt current nonzero source clif sourceStep
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_cmp_zero8_original_left_source_values run scope dominated events records
    foundBlock foundStmt current nonzero source clif typeX defined constantFound data normalized results statementResults mapped
    recorded emitted refines dfg getX getY held sourceStep
  exact ⟨u,v,d,output,lower,upper,memory,execution⟩
end Backend.Stock.Proof.ScalarCmp

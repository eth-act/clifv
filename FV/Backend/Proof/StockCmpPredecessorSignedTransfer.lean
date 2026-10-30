import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockCmpPredecessorSignedRecordValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual retained comparison execution transfers the original guarded source
relation to the real original source-step frame, not merely a constructed result
frame. Original restricted DFG and demanded/available guards are retained. -/
theorem stock_lower_cmp_predecessor_signed_source_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp .sge ty x y))
    (width : ty.width = 32 ∨ ty.width = 64)
    (typeX : event.ctx.valueType? x = some (.int (szOf ty.width).bits))
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int} {imm : Imm12}
    (defined : event.ctx.defInst? y = some constantJ) (constantFound : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (odd : u64 literal % 2 = 1) (encoded : Imm12.ofNat? (u64 (literal-1)) = some imm)
    (nonencodable : Imm12.ofNat? (u64 literal) = none)
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV} {u v : BitVec ty.width}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ d,step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .sge u v)⟩ (ρ' d) ∧ (∀ k,k ≠ d → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have rawGetX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (fr' := fr)
      (x := x) (ty := ty) (restrict_regs_of_mem availableX).symm).trans getX
  have rawGetY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (fr' := fr)
      (x := y) (ty := ty) (restrict_regs_of_mem availableY).symm).trans getY
  have restored := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have eval' : instOutcome env cp fr cm (.icmp .sge ty x y) =
      .ok ([⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .sge u v)⟩],cm) := by
    simp [instOutcome,Clif.evalInst,rawGetX,rawGetY,Clif.Sem.icmp]
  rw [eval'] at evaluated
  cases evaluated
  obtain ⟨d,output,lower,upper,execution⟩ := stock_lower_cmp_predecessor_signed_available_values run scope dominated events records
    foundBlock foundStmt current source clif width typeX defined constantFound data odd encoded nonencodable results statementResults mapped
    recorded emitted refines dfg getX getY held
  refine ⟨d,output,lower,upper,rfl,?_⟩
  intro world
  exact (execution world).imp (fun ρ' _ _ ⟨value,kept,post⟩ =>
    ⟨value,kept,source_single_result_values source clif results restored eval' post⟩)
/-- Successful original source execution and original dominance derive both
availability-restricted comparison getters internally. -/
theorem stock_lower_cmp_predecessor_signed_source_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {info : IInfo} {ty : Clif.Ty} {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp .sge ty x y))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u v,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.icmp .sge ty x y) = .ok (vals,cm') := evaluated
  obtain ⟨u,v,getX,getY,values,memory⟩ := evalInst_icmp_ok plain
  have availableX := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif x (by simp [Driver.instArgs])
  have availableY := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif y (by simp [Driver.instArgs])
  exact ⟨u,v,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).trans getX,
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).trans getY⟩
/-- Original source execution supplies both getters internally; the earlier
getter-explicit source-transfer theorem remains available unchanged. -/
theorem stock_lower_cmp_predecessor_signed_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp .sge ty x y))
    (width : ty.width = 32 ∨ ty.width = 64)
    (typeX : event.ctx.valueType? x = some (.int (szOf ty.width).bits))
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int} {imm : Imm12}
    (defined : event.ctx.defInst? y = some constantJ) (constantFound : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (odd : u64 literal % 2 = 1) (encoded : Imm12.ofNat? (u64 (literal-1)) = some imm)
    (nonencodable : Imm12.ofNat? (u64 literal) = none)
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
    ∃ u : BitVec ty.width,∃ v : BitVec ty.width,∃ d,step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .sge u v)⟩ (ρ' d) ∧ (∀ k,k ≠ d → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨u,v,getX,getY⟩ := stock_lower_cmp_predecessor_signed_source_operands run scope dominated events
    foundBlock foundStmt current source clif sourceStep
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_cmp_predecessor_signed_source_values run scope dominated events records
    foundBlock foundStmt current source clif width typeX defined constantFound data odd encoded nonencodable results statementResults mapped
    recorded emitted refines dfg getX getY held sourceStep
  exact ⟨u,v,d,output,lower,upper,memory,execution⟩
end Backend.Stock.Proof.ScalarCmp

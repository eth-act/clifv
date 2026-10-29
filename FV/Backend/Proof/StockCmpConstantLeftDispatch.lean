module

public import FV.Backend.Proof.StockCmpWideConstantLeftSourceValues
public import FV.Backend.Proof.StockCmpNarrowConstantLeftOriginalSourceValues
public import FV.Backend.Proof.StockCmpNonconstantSourceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Unified original-source transfer for a nonzero constant left and nonconstant right.
The actual original scope derives scalar width internally; all old variants remain. -/
theorem stock_lower_cmp_constant_left_source_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {cc : Clif.IntCC} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    (typeX : event.ctx.valueType? x = some (.int ty.width))
    (typeY : event.ctx.valueType? y = some (.int ty.width))
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : event.ctx.defInst? x = some constantJ) (constantFound : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal]) (nonzero : u64 literal ≠ 0)
    (notConstantY : NonConstantSource event.ctx y)
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
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  have inv := (stock_lower_record_context run scope events).1
  have widths := (stock_cmp_source_data inv source clif).1
  cases ty with
  | i8 =>
    exact stock_lower_cmp_narrow_constant_left_source_values run scope dominated events records foundBlock foundStmt current
      source clif false rfl typeX typeY defined constantFound data nonzero notConstantY results statementResults mapped
      recorded emitted refines dfg getX getY held sourceStep
  | i16 =>
    exact stock_lower_cmp_narrow_constant_left_source_values run scope dominated events records foundBlock foundStmt current
      source clif true rfl typeX typeY defined constantFound data nonzero notConstantY results statementResults mapped
      recorded emitted refines dfg getX getY held sourceStep
  | i32 =>
    obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_cmp_wide_constant_left_source_values run scope dominated events records
      foundBlock foundStmt current source clif (Or.inl rfl) typeX typeY defined constantFound data nonzero notConstantY
      results statementResults mapped recorded emitted refines dfg getX getY held sourceStep
    refine ⟨d,output,lower,upper,memory,?_⟩
    intro world
    exact (execution world).imp (fun ρ' _ _ ⟨value,kept,post⟩ => ⟨value,fun k outside => kept k (by omega),post⟩)
  | i64 =>
    obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_cmp_wide_constant_left_source_values run scope dominated events records
      foundBlock foundStmt current source clif (Or.inr rfl) typeX typeY defined constantFound data nonzero notConstantY
      results statementResults mapped recorded emitted refines dfg getX getY held sourceStep
    refine ⟨d,output,lower,upper,memory,?_⟩
    intro world
    exact (execution world).imp (fun ρ' _ _ ⟨value,kept,post⟩ => ⟨value,fun k outside => kept k (by omega),post⟩)
  | i128 => simp [Clif.Ty.width] at widths
  | f32 | f64 =>
    have accepted := inv.instE _ info _ source clif
    simp [Compile.instE, Compile.tyE] at accepted
/-- Original source execution supplies both getters internally; the earlier
getter-explicit source-transfer theorem remains available unchanged. -/
theorem stock_lower_cmp_constant_left_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {cc : Clif.IntCC} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    (typeX : event.ctx.valueType? x = some (.int ty.width))
    (typeY : event.ctx.valueType? y = some (.int ty.width))
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : event.ctx.defInst? x = some constantJ) (constantFound : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal]) (nonzero : u64 literal ≠ 0)
    (notConstantY : NonConstantSource event.ctx y)
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
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨u,v,getX,getY⟩ := stock_lower_cmp_nonconstant_source_operands run scope dominated events
    foundBlock foundStmt current source clif sourceStep
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_cmp_constant_left_source_values run scope dominated events records
    foundBlock foundStmt current source clif typeX typeY defined constantFound data nonzero notConstantY results statementResults mapped
    recorded emitted refines dfg getX getY held sourceStep
  exact ⟨u,v,d,output,lower,upper,memory,execution⟩
end Backend.Stock.Proof.ScalarCmp

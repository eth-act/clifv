import FV.Backend.Proof.StockCastSourceValues
import FV.Backend.Proof.StockReduceSourceValues
import FV.Backend.Proof.StockCastDispatch
import FV.Backend.Proof.StockGuardedRecordValues
namespace Backend.Stock.Proof.CastComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Original source execution and actual selection establish the cast's complete
guarded source transfer. Narrowing retains its real zero-code alias binding. -/
theorem extend_source_of_formats_framed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastBody.SafeFormat stm.inst) (sg : Bool)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_lower_cast_selected_rule_of_formats run scope events family sg source clif receipt.selected
  have selectedId : step.rules.getLast? = some (ScalarCast.extendRule sg).id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.extend (ScalarCast.extendOp sg) ty x) = .ok (vals,cm') := by
    simpa only [instOutcome] using evaluated
  obtain ⟨input,getX,grows,unchanged,values⟩ := evalInst_extend_ok plain
  have available := stock_lower_record_args_available run scope dominated events block statement current
    source clif x (by simp [Driver.instArgs])
  have restricted : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some input := by
    rw [restrict_regs_of_mem available]; exact getX
  obtain ⟨d,ρ',output,bounds,execution,value,kept,post⟩ := ScalarCast.stock_lower_extend_available_source
    run scope dominated events records block statement current sg source clif results statementResults mapped
    recorded emitted selectedId refines dfg held restricted sourceStep
  exact ⟨ρ',execution,unchanged,post,kept⟩

/-- Retained original interface. -/
theorem extend_source_of_formats {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastBody.SafeFormat stm.inst) (sg : Bool)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨ρ',execution,unchanged,post,_⟩ := extend_source_of_formats_framed run scope dominated events records block statement current family sg source clif results statementResults mapped recorded emitted refines dfg held sourceStep
  exact ⟨ρ',execution,unchanged,post⟩

/-- Original source execution and actual selection establish the cast's complete
guarded source transfer. Narrowing retains its real zero-code alias binding. -/

theorem extend_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastBody.Family stm.inst) (sg : Bool)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  exact extend_source_of_formats run scope dominated events records block statement current (fun b block stm statement => CastBody.family_formats (family b block stm statement)) sg source clif results statementResults mapped recorded emitted refines dfg held sourceStep

theorem reduce_source_framed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.ireduce ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_reduce_selected_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have selectedId : step.rules.getLast? = some rule_lower_2146.id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.ireduce ty x) = .ok (vals,cm') := by
    simpa only [instOutcome] using evaluated
  obtain ⟨input,getX,narrow,values,unchanged⟩ := evalInst_ireduce_ok plain
  have available := stock_lower_record_args_available run scope dominated events block statement current
    source clif x (by simp [Driver.instArgs])
  have restricted : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some input := by
    rw [restrict_regs_of_mem available]; exact getX
  obtain ⟨nx,map,outputs,code,aliases,memory,execution,value,post⟩ := ScalarCast.Reduce.stock_lower_reduce_available_source
    run scope dominated events records block statement current source clif results statementResults mapped
    recorded emitted selectedId held restricted sourceStep F isem
  exact ⟨ρ,execution,memory,post,fun _ _ => rfl⟩

/-- Retained original interface. -/
theorem reduce_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.ireduce ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨ρ',execution,unchanged,post,_⟩ := reduce_source_framed run scope dominated events records block statement current source clif results statementResults mapped recorded emitted held sourceStep
  exact ⟨ρ',execution,unchanged,post⟩

end Backend.Stock.Proof.CastComplete

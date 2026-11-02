import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockLogicalRecordValues
import FV.Backend.Proof.StockLogicalNotRecord
import FV.Backend.Proof.StockGuardedRecordValues
import FV.Backend.Proof.IselFamALUA

namespace Backend.Stock.Proof.LogicalComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open LogicalSelected
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

theorem source_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {ty : Clif.Ty} {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u v,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.binary kind.cop ty x y) = .ok (vals,cm') := by
    cases kind <;> simpa [Kind.cop,instOutcome] using evaluated
  obtain ⟨u,v,getX,getY,_⟩ := evalInst_binary_inv (by cases kind <;> rfl) plain
  have availableX : x ∈ availOf f (availIn f result.ctx) bi j := stock_lower_record_args_available
    run scope dominated events block statement current source clif x (by simp [Driver.instArgs])
  have availableY : y ∈ availOf f (availIn f result.ctx) bi j := stock_lower_record_args_available
    run scope dominated events block statement current source clif y (by simp [Driver.instArgs])
  exact ⟨u,v,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).trans getX,
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).trans getY⟩
theorem available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some kind.rule.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm) := by
    cases kind <;> simp [Kind.cop,instOutcome,Clif.evalInst,Clif.BinaryOp.isShift,originalX,originalY]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨ρ',execution,value,kept,installed⟩ := LogicalSelected.stock_lower_logical_available_values
    run scope dominated events records block statement current kind source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post⟩
theorem source_from_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some kind.rule.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨u,v,getX,getY⟩ := source_operands run scope dominated events block statement current kind source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post⟩ := available_source
    run scope dominated events records block statement current kind source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY sourceStep
  exact ⟨u,v,ρ',getX,getY,execution,value,memEq,kept,post⟩
private theorem not_values_same_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (left : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (LogicalNot.notRule kind left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (sourceX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (sourceY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary kind.cop u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  cases left with
  | false =>
    exact LogicalNot.stock_lower_logical_not_available_values
      run scope dominated events records block statement current kind false source clif results statementResults
      mapped recorded emitted selectedId refines dfg held sourceX sourceY
  | true =>
    exact LogicalNot.stock_lower_logical_not_available_values (x := y) (y := x)
      run scope dominated events records block statement current kind true source clif results statementResults
      mapped recorded emitted selectedId refines dfg held sourceY sourceX

theorem not_available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (left : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (LogicalNot.notRule kind left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm) := by
    cases kind <;> simp [Kind.cop,instOutcome,Clif.evalInst,Clif.BinaryOp.isShift,originalX,originalY]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,Clif.Sem.binary kind.cop u v⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨ρ',execution,value,kept,installed⟩ := not_values_same_order
    run scope dominated events records block statement current kind left source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post⟩
theorem not_source_from_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (left : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (LogicalNot.notRule kind left).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨u,v,getX,getY⟩ := source_operands run scope dominated events block statement current kind source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post⟩ := not_available_source
    run scope dominated events records block statement current kind left source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY sourceStep
  exact ⟨u,v,ρ',getX,getY,execution,value,memEq,kept,post⟩

end Backend.Stock.Proof.LogicalComplete

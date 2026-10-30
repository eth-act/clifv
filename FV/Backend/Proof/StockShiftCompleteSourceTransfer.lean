import FV.Backend.Proof.StockShiftDispatch
import FV.Backend.Proof.StockShiftSourceTransfer
import FV.Backend.Proof.StockShiftBitfieldRecordValues
import FV.Backend.Proof.StockGuardedRecordValues
import FV.Backend.Proof.IselFamAluBShiftBase
namespace Backend.Stock.Proof.ShiftComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarShift
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Fused bitfield roots preserve original source execution under the original
demand and availability guard, including unmaterialized nested definitions. -/
theorem fused_source_framed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (signed : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (ShiftBitfield.fusedKind signed).cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ShiftBitfield.fusedRule signed).id)
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
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.binary (ShiftBitfield.fusedKind signed).cop ty x y) = .ok (vals,cm') := by
    cases signed <;> simpa [ShiftBitfield.fusedKind,Kind.cop,instOutcome] using evaluated
  obtain ⟨u,amount,value,getX,getY,shift,values,unchanged⟩ :=
    evalInst_shift_ok (by cases signed <;> rfl) plain
  have valueEq : value = (ShiftBitfield.fusedKind signed).value u amount := by
    cases signed <;> simp [ShiftBitfield.fusedKind,Kind.cop,Kind.value,Clif.Sem.shift] at shift ⊢ <;> exact shift.symm
  have availableX := stock_lower_record_args_available run scope dominated events block statement current
    source clif x (by simp [Driver.instArgs])
  have availableY := stock_lower_record_args_available run scope dominated events block statement current
    source clif y (by simp [Driver.instArgs])
  have restrictedX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (restrict_regs_of_mem availableX)).trans getX
  have restrictedY : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs y = some amount := by
    rw [restrict_regs_of_mem availableY]; exact getY
  obtain ⟨ρ',execution,heldValue,kept,installed⟩ :=
    ShiftBitfield.stock_lower_bitfield_available_values run scope dominated events records block statement current
      signed source clif results statementResults mapped recorded emitted selectedId refines dfg held restrictedX restrictedY
  have computed : instOutcome env cp fr cm (.binary (ShiftBitfield.fusedKind signed).cop ty x y) =
      .ok ([⟨ty,(ShiftBitfield.fusedKind signed).value u amount⟩],cm') := by
    rw [← valueEq,← values]; exact evaluated
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro key demanded val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held key ⟨demanded,available⟩ val lookup
  obtain ⟨_,_,_,_,upper,_⟩ := ShiftBitfield.stock_lower_bitfield_record_values
    run scope events records signed source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld restrictedX restrictedY
  refine ⟨ρ',execution,unchanged,source_single_result_values source clif results sourceStep computed installed,?_⟩
  intro key outside
  apply kept key
  omega

/-- Retained original interface. -/
theorem fused_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (signed : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (ShiftBitfield.fusedKind signed).cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ShiftBitfield.fusedRule signed).id)
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
  obtain ⟨ρ',execution,unchanged,post,_⟩ := fused_source_framed run scope dominated events records block statement current signed source clif results statementResults mapped recorded emitted selectedId refines dfg held sourceStep
  exact ⟨ρ',execution,unchanged,post⟩

/-- Every actual shift record transfers original source semantics. All eight
reachable roots are derived from the actual selection internally; the caller
supplies no selected-root, typed-count or materialization certificate. -/
theorem record_source_framed {f : Clif.Function} {result : Result}
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
  have ids := selected_rule_ids (stock_lower_record_context run scope events).1 kind source clif receipt.selected
  have last : step.rules.getLast? = some receipt.selected.rule.id := by
    rw [receipt.rules,receipt.selected.last_rule]
  cases kind with
  | lsl =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at ids
    rcases ids with id0 | id1
    · rw [id0] at last
      exact base_source_framed run scope dominated events records block statement current .lsl true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · rw [id1] at last
      exact base_source_framed run scope dominated events records block statement current .lsl false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
  | lsr =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at ids
    rcases ids with id0 | id1 | id2
    · rw [id0] at last
      exact fused_source_framed run scope dominated events records block statement current false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · rw [id1] at last
      exact base_source_framed run scope dominated events records block statement current .lsr true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · rw [id2] at last
      exact base_source_framed run scope dominated events records block statement current .lsr false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
  | asr =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at ids
    rcases ids with id0 | id1 | id2
    · rw [id0] at last
      exact fused_source_framed run scope dominated events records block statement current true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · rw [id1] at last
      exact base_source_framed run scope dominated events records block statement current .asr true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · rw [id2] at last
      exact base_source_framed run scope dominated events records block statement current .asr false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep

/-- Retained original interface. -/
theorem record_source {f : Clif.Function} {result : Result}
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
  obtain ⟨ρ',execution,unchanged,post,_⟩ := record_source_framed run scope dominated events records block statement current kind source clif results statementResults mapped recorded emitted refines dfg held sourceStep
  exact ⟨ρ',execution,unchanged,post⟩

end Backend.Stock.Proof.ShiftComplete

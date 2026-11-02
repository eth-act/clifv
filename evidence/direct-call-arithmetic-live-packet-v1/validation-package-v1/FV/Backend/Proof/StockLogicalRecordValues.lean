import FV.Backend.Proof.StockLogicalRootValues
import FV.Backend.Proof.StockDemandExtent

namespace Backend.Stock.Proof.LogicalSelected
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl
private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- A complete selected logical record executes its original binary operation.
Root selection, operand bounds, output binding and emitted code come from the
actual whole-driver run, rather than caller-supplied execution certificates. -/
theorem stock_lower_logical_record_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some kind.rule.id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons event.ctx fr) {ρ : Nat → CV}
    (held : ValuesHeld (Demanded record.output.state) event.ctx fr
      (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ (mi : MInst) (ρ' : Nat → CV),
      step.results = [[.vreg record.input.base.nextVreg .int]] ∧
      record.output.emitted = #[mi] ∧
      record.output.state.base.nextVreg = record.input.base.nextVreg + 1 ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      ∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨width,out,next,trace,rhsTrace,root,rhs⟩ :=
    stock_lower_logical_selected_receipts run scope events records kind source clif recorded emitted selectedId
  have same := Except.ok.inj (receipt.rootRun.symm.trans root)
  have outEq := Option.some.inj (congrArg Prod.fst same)
  have nextEq := congrArg (fun q => q.2.1) same
  change receipt.next = next at nextEq
  have bindingDemand := stock_bindResults_demand receipt.binding
  change receipt.bound.demand = receipt.next.demand at bindingDemand
  have demand : record.output.state.demand = next.demand := by
    rw [receipt.state,bindingDemand,nextEq]
  have rootHeld : ValuesHeld (Demanded next) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) := by
    simpa only [ValuesHeld,Demanded,demand] using held
  have bounded : result.final.alias.size ≤ (scanState record.input record.inst).base.nextVreg :=
    stock_lower_blockScanAliasBounds run event events record records
  have extent : ∀ x r, event.ctx.valueReg? x = some r → x < (scanState record.input record.inst).demand.size := by
    intro x r map
    simpa only [scanState_demands] using (Extent.lower_mapped_demand_bounds run scope events records map).1
  obtain ⟨mi,ρ',output,base,execution,value,kept⟩ := stock_logical_root_values
    (stock_lower_record_context run scope events).1 refines kind width dfg sourceX sourceY
    bounded extent rootHeld rhs
  simp only [scan_frontier] at output value kept
  have output' : receipt.out = .regsVec [[.vreg record.input.base.nextVreg .int]] := outEq.trans output
  have rss : receipt.results = [[.vreg record.input.base.nextVreg .int]] := by
    exact V.regsVec.inj (receipt.output.symm.trans output')
  have installed := bindResults_virtual event.ctx next [(z,a,record.input.base.nextVreg)] (by
    intro p member
    have equal := List.mem_singleton.mp member
    subst p
    exact mapped)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at installed
  have binding := receipt.binding
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  rw [infoBang,results,rss,nextEq] at binding
  simp only [List.zip_cons_cons,List.zip_nil_left] at binding
  rw [installed] at binding
  have boundEq := (Prod.mk.inj (Except.ok.inj binding)).1.symm
  have copiesEq := (Prod.mk.inj (Except.ok.inj binding)).2.symm
  have code : record.output.emitted = #[mi] := by
    rw [receipt.code,boundEq,copiesEq]
    change next.base.emitted ++ #[] = #[mi]
    rw [base]
    simp [LState.fresh,LState.emit,scan_empty]
  refine ⟨mi,ρ',receipt.resultRegs.trans rss,code,?_,?_,value,kept⟩
  · rw [receipt.state,boundEq]
    change next.base.nextVreg = _
    rw [base]
    simp only [LState.fresh,LState.emit,scan_frontier]
  · rw [code]
    exact execution

/-- Logical records preserve the baseline demanded-and-available relation.
DFG consistency is required only on the original availability-restricted frame;
fused operands need not have separate machine registers. -/
theorem stock_lower_logical_available_values {f : Clif.Function} {result : Result}
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
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro x needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held x ⟨needed,available⟩ val lookup
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_logical_record_values
    run scope events records kind source clif results mapped recorded emitted selectedId
    refines dfg restrictedHeld sourceX sourceY
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records
    source clif results mapped recorded emitted outputs (Nat.le_refl _)).2
  have maps := (stock_lower_record_context run scope events).2.1
  refine ⟨ρ',execution,value,kept,?_⟩
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue,eq_self,ite_true] at lookup
    cases lookup
    exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue,ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults,List.mem_singleton] using equal)
    have demand : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact required.1 (Nat.eq_zero_of_le_zero count)
    obtain ⟨key,map,old⟩ := held y ⟨demand,before⟩ val lookup
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current before (by rw [← maps]; exact map)
    have different : aliasNum result.final.alias key ≠ record.input.base.nextVreg := by
      rw [upper] at outside
      omega
    exact ⟨key,map,by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [kept _ different]; exact old⟩

end Backend.Stock.Proof.LogicalSelected

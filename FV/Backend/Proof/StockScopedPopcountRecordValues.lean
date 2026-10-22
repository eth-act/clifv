import FV.Backend.Proof.StockScopedPopcountSelected
import FV.Backend.Proof.StockCountRecordValues
import FV.Backend.Proof.StockGuardedRecordFrame
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm popcountBase

theorem available_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary .popcnt ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u : BitVec ty.width} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u) :
    ∃ (d : Nat) (ρ' : Nat → CV),step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .popcnt u⟩ (ρ' d) ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        (withValue fr z ⟨ty,Clif.Sem.unary .popcnt u⟩) (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨width,data,type⟩ := source_data inv source clif
  have boundBase := ScalarCount.stock_binding_base receipt.binding
  have recordBase : record.output.state.base = receipt.next.base := by rw [receipt.state,boundBase]
  have demand : record.output.state.demand = receipt.next.demand := by rw [receipt.state,stock_bindResults_demand receipt.binding]
  have maps := (stock_lower_record_context run scope events).2.1
  have restrictedHeld : ValuesHeld (Demanded receipt.next) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro v needed value lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held v ⟨by simpa only [Demanded,demand] using needed,available⟩ value lookup
  have bounded := stock_lower_blockScanAliasBounds run event events record records
  have extent : ∀ v r,event.ctx.valueReg? v = some r → v < (scanState record.input record.inst).demand.size := by
    intro v r map
    simpa only [scanState_demands] using (Extent.lower_mapped_demand_bounds run scope events records map).1
  obtain ⟨nx,ρ',sourceMap,output,nextEq,execution,value,kept⟩ := selected_values
    inv source clif refines getX
    receipt.selected bounded extent restrictedHeld
  let start := (scanState record.input record.inst).base.nextVreg
  let d := popcountResult ty.width start
  have starts : record.input.base.nextVreg = start := by simp only [start,ScalarCount.stock_scan_frontier]
  have fresh : record.input.base.nextVreg ≤ d := by
    rw [starts]
    rcases width with h | h | h | h <;> simp [d,popcountResult,popcountAlloc,h] <;> omega
  have high : record.output.state.base.nextVreg = start+popcountAlloc ty.width := by
    rw [recordBase,nextEq]
    exact (base_code width (scanState record.input record.inst).base nx).2
  have inside : d < start+popcountAlloc ty.width := by
    rcases width with h | h | h | h <;> simp [d,popcountResult,popcountAlloc,h] <;> omega
  have rss : receipt.results = [[.vreg d .int]] := V.regsVec.inj (receipt.output.symm.trans output)
  have installed := bindResults_virtual event.ctx receipt.next [(z,a,d)] (by
    intro p member; have same := List.mem_singleton.mp member; subst p; exact mapped)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at installed
  have binding := receipt.binding
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  rw [infoBang,results,rss] at binding
  simp only [List.zip_cons_cons,List.zip_nil_left] at binding
  rw [installed] at binding
  have boundEq := (Prod.mk.inj (Except.ok.inj binding)).1.symm
  have copiesEq := (Prod.mk.inj (Except.ok.inj binding)).2.symm
  have recordCode : record.output.emitted.toList = popcountCode ty.width start nx := by
    rw [receipt.code,boundBase,copiesEq,nextEq]
    change (popcountBase ty.width (scanState record.input record.inst).base (.vreg nx .int)).emitted.toList = _
    rw [(base_code width (scanState record.input record.inst).base nx).1]
    simp [ScalarCount.stock_scan_emitted_empty,start]
  have recordExec : PRun F isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' := by
    rw [recordCode]; exact execution
  refine ⟨d,ρ',receipt.resultRegs.trans rss,⟨fresh,by rw [high]; exact inside⟩,recordExec,value,?_,?_⟩
  · intro n outside
    apply kept
    rw [high,starts] at outside
    exact outside
  · apply stock_lower_fresh_record_values_of_frame run scope dominated events records block statement current
      source clif results statementResults mapped recorded emitted (receipt.resultRegs.trans rss) fresh held ?_ value
    intro n outside
    apply kept
    rwa [high,starts] at outside

end Backend.Stock.Proof.Popcount

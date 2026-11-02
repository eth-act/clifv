import FV.Backend.Proof.StockHighMulNarrowRecordValues
import FV.Backend.Proof.StockHighMulWideRecordValues
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- All four actual high-multiply roots transfer original values through retained
binding and original availability, deriving the wide/narrow case internally. -/
theorem stock_lower_highmul_available_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    (signed : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ (d : Nat) (ρ' : Nat → CV),step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' d) ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        (withValue fr z ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩) (fun k => ρ' (aliasNum result.final.alias k)) := by
  by_cases wide : ty = .i64
  · subst ty
    exact stock_lower_highmul_wide_available_values run scope dominated events records
      block statement current signed source clif results statementResults mapped recorded emitted
      refines dfg held getX getY
  · have inv := (stock_lower_record_context run scope events).1
    have accepted := inv.instE record.inst info _ source clif
    have supported : eTy ty = true := by
      cases signed <;> simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
    have small : ty.width ≤ 32 := by cases ty <;> simp [eTy,Clif.Ty.width] at supported wide ⊢
    exact stock_lower_highmul_narrow_available_values run scope dominated events records
      block statement current signed source clif results statementResults mapped recorded emitted small
      refines dfg held getX getY
end Backend.Stock.Proof.ScalarHighMul

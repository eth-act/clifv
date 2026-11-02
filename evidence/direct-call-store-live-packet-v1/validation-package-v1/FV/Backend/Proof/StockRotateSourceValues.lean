import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockRotateNarrowImmSourceValues
import FV.Backend.Proof.StockRotateWideImmSourceValues
import FV.Backend.Proof.StockRotateNarrowSourceValues
import FV.Backend.Proof.StockRotateWideSourceValues
import FV.Backend.Proof.StockRotateDispatch
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Actual successful source evaluation and original dominance derive both
operands at the restricted statement boundary. -/
theorem stock_lower_rotate_source_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (left : Bool)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u amount,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).regs y = some amount := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX : x ∈ availOf f (availIn f result.ctx) bi j :=
    stock_lower_record_args_available run scope dominated events block statement current source clif x (by simp [Driver.instArgs])
  have availableY : y ∈ availOf f (availIn f result.ctx) bi j :=
    stock_lower_record_args_available run scope dominated events block statement current source clif y (by simp [Driver.instArgs])
  have getter : ∃ u,fr.getAs x ty = .ok u := by
    cases get : fr.getAs x ty with
    | ok u => exact ⟨u,rfl⟩
    | trap code => simp [instOutcome,Clif.evalInst,get] at evaluated
    | stuck message => simp [instOutcome,Clif.evalInst,get] at evaluated
  obtain ⟨u,get⟩ := getter
  have count : ∃ amount,fr.regs y = some amount := by
    cases lookup : fr.regs y with
    | some amount => exact ⟨amount,rfl⟩
    | none => cases left <;> simp [instOutcome,Clif.evalInst,get,rotateOp,Clif.BinaryOp.isShift,Clif.Frame.get,lookup] at evaluated
  obtain ⟨amount,lookup⟩ := count
  exact ⟨u,amount,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
    (x := x) (ty := ty) (restrict_regs_of_mem availableX)).trans get,
    (restrict_regs_of_mem availableY).trans lookup⟩
/-- Original source transfer derives both restricted operands and actual
rule selection internally, preserving the prior explicit theorem variants. -/
theorem stock_lower_rotate_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (left : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
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
    ∃ (u : BitVec ty.width) (amount : Clif.Val) (d : Nat) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).regs y = some amount ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨immediate,chosen⟩ := stock_selected_rotate_rule (stock_lower_record_context run scope events).1 left source clif receipt.selected
  have selectedId : step.rules.getLast? = some (rotateRule left immediate ty.width).id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  obtain ⟨u,amount,getX,getY⟩ := stock_lower_rotate_source_operands
    run scope dominated left events block statement current source clif sourceStep
  by_cases narrow : ty.width = 8 ∨ ty.width = 16
  · cases immediate
    · simp only [rotateRule,narrow,ite_true] at selectedId
      obtain ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_rotate_narrow_register_available_source
        run scope dominated left events records block statement current source clif results statementResults
        mapped recorded emitted selectedId refines dfg held getX getY sourceStep
      exact ⟨u,amount,d,ρ',getX,getY,output,bounds,execution,value,memEq,kept,post⟩
    · simp only [rotateRule,narrow,ite_true] at selectedId
      obtain ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_rotate_narrow_immediate_available_source
        run scope dominated left events records block statement current source clif results statementResults
        mapped recorded emitted selectedId refines dfg held getX getY sourceStep
      exact ⟨u,amount,d,ρ',getX,getY,output,bounds,execution,value,memEq,kept,post⟩
  · cases immediate
    · simp only [rotateRule,narrow,ite_false,Bool.false_eq_true] at selectedId
      obtain ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_rotate_wide_register_available_source
        run scope dominated left (ty.width = 64) events records block statement current source clif results statementResults
        mapped recorded emitted selectedId refines dfg held getX getY sourceStep
      exact ⟨u,amount,d,ρ',getX,getY,output,bounds,execution,value,memEq,kept,post⟩
    · simp only [rotateRule,narrow,ite_false,ite_true] at selectedId
      obtain ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_rotate_wide_immediate_available_source
        run scope dominated left (ty.width = 64) events records block statement current source clif results statementResults
        mapped recorded emitted selectedId refines dfg held getX getY sourceStep
      exact ⟨u,amount,d,ρ',getX,getY,output,bounds,execution,value,memEq,kept,post⟩
end Backend.Stock.Proof.ScalarRotate

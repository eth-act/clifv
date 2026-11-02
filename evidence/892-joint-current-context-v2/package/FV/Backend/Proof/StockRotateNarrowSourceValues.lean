import FV.Backend.Proof.StockRotateNarrowRecordValues
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Actual scalar count source steps consume the original body and retain
source memory; the real selected record establishes the demanded/available
post-frame through its actual result binding and final resolver. -/
theorem stock_lower_rotate_narrow_register_available_source {f : Clif.Function} {result : Result}
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
    (selectedId : step.rules.getLast? = some (rotateNarrowRule left false).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u : BitVec ty.width} {amount : Clif.Val} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs y = some amount)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (d : Nat) (ρ' : Nat → CV),step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have originalX : fr.getAs x ty = .ok u := by
    have same := getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)
    exact same.symm.trans getX
  have availableY := restrict_regs_isSome (by rw [getY]; rfl)
  have originalY : fr.regs y = some amount := (restrict_regs_of_mem availableY).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary (rotateOp left) ty x y) = .ok ([⟨ty,rotateWideBits left u amount.bits.toNat⟩],cm) := by
    cases left <;> simp [instOutcome,Clif.evalInst,originalX,originalY,rotateOp,rotateWideBits,Clif.Sem.shift,Clif.Sem.rotl,Clif.Sem.rotr,Clif.Sem.shiftAmt,Clif.BinaryOp.isShift,Clif.Frame.get]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary (rotateOp left) ty x y) =
      .ok ([⟨ty,rotateWideBits left u amount.bits.toNat⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨d,ρ',output,bounds,execution,value,kept,installed⟩ := stock_lower_rotate_narrow_register_available_values
    run scope dominated left events records block statement current source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩
end Backend.Stock.Proof.ScalarRotate

import FV.Backend.Proof.StockHighMulRecordValues
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Successful original source execution and unchanged dominance derive both
restricted source operands internally. -/
theorem stock_lower_highmul_source_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    (signed : Bool) {info : IInfo} {ty : Clif.Ty} {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u v,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.binary (if signed then .smulhi else .umulhi) ty x y) = .ok (vals,cm') := by
    cases signed <;> simpa [instOutcome] using evaluated
  obtain ⟨u,v,getX,getY,_⟩ := evalInst_binary_inv (by cases signed <;> rfl) plain
  have availableX : x ∈ availOf f (availIn f result.ctx) bi j := stock_lower_record_args_available
    run scope dominated events block statement current source clif x (by simp [Driver.instArgs])
  have availableY : y ∈ availOf f (availIn f result.ctx) bi j := stock_lower_record_args_available
    run scope dominated events block statement current source clif y (by simp [Driver.instArgs])
  exact ⟨u,v,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).trans getX,
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).trans getY⟩
/-- Actual scalar high-multiply source steps consume the original body and retain
source memory; the real selected record establishes the demanded/available
post-frame through its actual result binding and final resolver. -/
theorem stock_lower_highmul_available_source {f : Clif.Function} {result : Result}
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
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (d : Nat) (ρ' : Nat → CV),step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' d) ∧ cm' = cm ∧
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
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  have computed : instOutcome env cp fr cm (.binary (if signed then .smulhi else .umulhi) ty x y) = .ok ([⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩],cm) := by
    cases signed <;> simp [instOutcome,Clif.evalInst,Clif.BinaryOp.isShift,originalX,originalY]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.binary (if signed then .smulhi else .umulhi) ty x y) =
      .ok ([⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨d,ρ',output,bounds,execution,value,kept,installed⟩ := stock_lower_highmul_available_values
    run scope dominated events records block statement current signed source clif results statementResults
    mapped recorded emitted refines dfg held getX getY
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩
/-- Original source transfer derives both operand getter and rule selection
internally; previous theorem variants remain available. -/
theorem stock_lower_highmul_source_by_instruction {f : Clif.Function} {result : Result}
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
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (d : Nat) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨u,v,getX,getY⟩ := stock_lower_highmul_source_operands run scope dominated events block statement current signed source clif sourceStep
  obtain ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_highmul_available_source
    run scope dominated events records block statement current signed source clif results statementResults
    mapped recorded emitted refines dfg held getX getY sourceStep
  exact ⟨u,v,d,ρ',getX,getY,output,bounds,execution,value,memEq,kept,post⟩

end Backend.Stock.Proof.ScalarHighMul

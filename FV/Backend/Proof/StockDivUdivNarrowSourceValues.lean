import FV.Backend.Proof.StockDivUdivNarrowRecordValues
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_lower_udiv_narrow_available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} (narrow : ty.width ≤ 32) {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div .udiv ty x y))
    (results : info.results = [z]) (statementResults : stmt.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k))) {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ d q,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      Clif.Sem.div .udiv u v = .ok q ∧ cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,q⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
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
  have computed : instOutcome env cp fr cm (.div .udiv ty x y) =
      Clif.Res.bind (Clif.Res.ofExcept (Clif.Sem.div .udiv u v)) (fun q => .ok ([⟨ty,q⟩],cm)) := by
    simp [instOutcome,Clif.evalInst,originalX,originalY]
    all_goals rfl
  cases division : Clif.Sem.div .udiv u v with
  | error code => rw [computed,division] at evaluated; cases evaluated
  | ok q =>
    have eval : instOutcome env cp fr cm (.div .udiv ty x y) = .ok ([⟨ty,q⟩],cm) := by
      rw [computed,division]; rfl
    have memory : cm' = cm := (Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans eval))).2
    have eval' : instOutcome env cp fr cm (.div .udiv ty x y) = .ok ([⟨ty,q⟩],cm') := by rw [memory]; exact eval
    obtain ⟨d,output,bounds,execution⟩ := stock_lower_udiv_narrow_available_values run scope dominated events records
      foundBlock foundStmt current narrow source clif results statementResults mapped recorded emitted refines dfg held getX getY
    refine ⟨d,q,output,bounds,rfl,memory,?_⟩
    intro world
    exact ((execution world).2 q division).imp (fun ρ' _ _ ⟨value,kept,post⟩ =>
      ⟨value,kept,source_single_result_values source clif results sourceStep eval' post⟩)
/-- Original successful source execution and dominance derive both available
operand getters internally, without a caller operand-match certificate. -/
theorem stock_lower_udiv_narrow_source_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} (narrow : ty.width ≤ 32) {info : IInfo} {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div .udiv ty x y))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u v,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.div .udiv ty x y) = .ok (vals,cm') := evaluated
  obtain ⟨u,v,lookupX,lookupY,_⟩ := evalInst_div_inv plain (fun _ impossible => by cases impossible)
  have availableX := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif x (by simp [Driver.instArgs])
  have availableY := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif y (by simp [Driver.instArgs])
  have getX : fr.getAs x ty = .ok u := by
    unfold Clif.Frame.getAs Clif.Frame.get
    rw [lookupX]
    simp [Clif.Res.ofOption]
  have getY : fr.getAs y ty = .ok v := by
    unfold Clif.Frame.getAs Clif.Frame.get
    rw [lookupY]
    simp [Clif.Res.ofOption]
  exact ⟨u,v,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).trans getX,
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).trans getY⟩
theorem stock_lower_udiv_narrow_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} (narrow : ty.width ≤ 32) {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div .udiv ty x y))
    (results : info.results = [z]) (statementResults : stmt.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u v d q,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      Clif.Sem.div .udiv u v = .ok q ∧ cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,q⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨u,v,getX,getY⟩ := stock_lower_udiv_narrow_source_operands run scope dominated events foundBlock foundStmt current narrow source clif sourceStep
  obtain ⟨d,q,output,bounds,division,memory,execution⟩ := stock_lower_udiv_narrow_available_source run scope dominated events records
    foundBlock foundStmt current narrow source clif results statementResults mapped recorded emitted refines dfg held getX getY sourceStep
  exact ⟨u,v,d,q,output,bounds,division,memory,execution⟩
end Backend.Stock.Proof.ScalarDiv

import FV.Backend.Proof.StockCallRecordFootprint
import FV.Backend.Proof.StockExplicitCallFrames
namespace Backend.Stock.Proof.CallResolvedFrameDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem alias_renaming (a : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve a (a.size+1)) (aliasNum a) := by
  refine ⟨fun n c => resolve_vreg _ _ n c,?_⟩
  intro r hr
  cases r with
  | vreg n c => exact False.elim (hr n c rfl)
  | _ => rfl
private theorem renamed_defs (a : Array (Option Nat)) (i : MInst) :
    vdefs (i.mapRegs (Backend.lowerFunction.resolve a (a.size+1))) = (vdefs i).map (aliasNum a) := by
  unfold vdefs
  rw [operands_mapRegs (alias_renaming a)]
  cases operands : i.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map,Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl
private theorem statement_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    {info : IInfo} {inst : Clif.Inst} (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst) :
    info.results = stm.results := by
  have global := (stock_lower_record_context run scope events).2.2 _ _ _ slot clif
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,rest⟩ := stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,old,spec,view⟩ := buildCtx_source build
  obtain ⟨other,found,originalClif,results⟩ := spec.facts.stmt bi b j stm block statement
  have actual : original.insts[blockStart f bi+j]? = some info := by rw [← view.insts,← current]; exact global
  cases Option.some.inj (found.symm.trans actual)
  exact results


/-- Shared actual-record composition: real fresh definitions, available source
uses, source result continuation and raw execution imply final alias-resolved
execution with EVERY result and all other demanded/available values preserved.
Rule-family wrappers derive the local facts from actual retained executions. -/
theorem stock_lower_record_resolved_source_frame {sem : Backend.Proof.Sem} (driver : DriverSem sem)
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    {info : IInfo} {inst : Clif.Inst}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {fr fr' : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (held : ValuesHeld (fun x => Demanded record.output.state x ∧ x ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    (source : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm'))
    (defs : ∀ m ∈ record.output.emitted.toList,∀ d ∈ vdefs m,
      record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg)
    (provenance : ∀ m ∈ record.output.emitted.toList,∀ u ∈ vuseNums m,
      ∃ x,x ∈ availOf f (availIn f result.ctx) bi j ∧ event.ctx.valueReg? x = some (.vreg u .int))
    (rawRun : ∃ (raw : Nat → CV) (w' : Arm.ArmState),
      seqRun sem record.output.emitted.toList (fun key => ρ (aliasNum result.final.alias key)) w = some (.fall raw w') ∧
      MR fr'.slots cm' w' ∧ ValuesHeld (fun x => x ∈ info.results) result.ctx fr' (fun key => raw (aliasNum result.final.alias key))) :
    ∃ (ρ' : Nat → CV) (w' : Arm.ArmState),
      seqRun sem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') ∧
      MR fr'.slots cm' w' ∧
      ValuesHeld (fun x => Demanded record.input x ∧ x ∈ availOf f (availIn f result.ctx) bi (j+1))
        result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) ∧
      ValuesHeld (fun x => x ∈ info.results) result.ctx fr' (fun key => ρ' (aliasNum result.final.alias key)) := by
  let gn := aliasNum result.final.alias
  let g := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  let D : Nat → Prop := fun n => record.input.base.nextVreg ≤ n ∧ n < record.output.state.base.nextVreg
  obtain ⟨raw,w',executed,relatedAfter,returned⟩ := rawRun
  have fix : ∀ n,D n → gn n = n := by
    intro n inside
    exact (stock_lower_freshAlias_terminal run (Nat.le_trans
      (stock_lower_blockScanInitialFrontier run event events record records) inside.1)).2
  have uses : ∀ m ∈ record.output.emitted.toList,∀ u ∈ vuseNums m,D u ∨ ¬ D (gn u) := by
    intro m member u used
    obtain ⟨x,available,mapped⟩ := provenance m member u used
    have outside := stock_lower_available_alias_outside_record run scope dominated events records block statement current available
      (by rw [← (stock_lower_record_context run scope events).2.1]; exact mapped)
    exact .inr (by dsimp [D,gn]; omega)
  obtain ⟨next,renamed,agree⟩ := (seqRun_rename (alias_renaming result.final.alias)
    (driver.rename g gn (alias_renaming result.final.alias)) fix defs uses (fun _ _ => rfl)).1 executed
  have idem := stock_lower_alias_idempotent run scope dominated
  have resolvedAgree : ∀ key,raw (gn key) = next (gn key) := by
    intro key
    have decision : D (gn key) ∨ ¬ D (gn (gn key)) := by
      by_cases inside : D (gn key)
      · exact .inl inside
      · exact .inr (by simpa only [gn,idem] using inside)
    have same := agree (gn key) decision
    simpa only [gn,idem] using same
  have allResults : ValuesHeld (fun x => x ∈ info.results) result.ctx fr' (fun key => next (gn key)) := by
    intro x member v lookup
    obtain ⟨key,map,value⟩ := returned x member v lookup
    exact ⟨key,map,by change VHolds v (next (gn key)); rw [← resolvedAgree]; exact value⟩
  have renamedDefs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs g),∀ n ∈ vdefs m,D n := by
    intro m member n defined
    obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
    rw [renamed_defs] at defined
    obtain ⟨d,rawDefined,rfl⟩ := List.mem_map.mp defined
    change D (gn d)
    rw [fix d (defs raw rawMember d rawDefined)]
    exact defs raw rawMember d rawDefined
  have sameResults := statement_results run scope events block statement current slot clif
  obtain ⟨info',inst',vals,regs,rest,slot',clif',body,evaluation,set,updated⟩ := source
  have same := Option.some.inj (slot'.symm.trans slot)
  subst info'
  dsimp only at updated set
  refine ⟨next,w',renamed,relatedAfter,?_,allResults⟩
  intro x required v lookup
  by_cases fresh : x ∈ info.results
  · obtain ⟨key,map,value⟩ := returned x fresh v lookup
    exact ⟨key,map,by change VHolds v (next (gn key)); rw [← resolvedAgree]; exact value⟩
  · have before := available_before_of_after_not_result block statement required.2 (by rwa [← sameResults])
    have demanded : Demanded record.output.state x := by
      intro zero
      have grows := stock_lower_record_demand_mono run events records recorded emitted x
      change record.output.state.demand[x]! = 0 at zero
      rw [zero] at grows
      exact required.1 (Nat.eq_zero_of_le_zero grows)
    have previous : fr.regs x = some v := by
      rw [updated] at lookup
      change regs x = some v at lookup
      rw [setMany_other set fresh] at lookup
      exact lookup
    obtain ⟨key,map,value⟩ := held x ⟨demanded,before⟩ v previous
    have global : result.ctx.valueReg? x = some (.vreg key .int) := by rw [← (stock_lower_record_context run scope events).2.1]; exact map
    have kept := stock_lower_available_fresh_frame run scope dominated events records block statement current before global renamedDefs renamed
    exact ⟨key,global,by change VHolds v (next (gn key)); rw [kept]; exact value⟩
end Backend.Stock.Proof.CallResolvedFrameDraft

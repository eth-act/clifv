import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockReturnRecordCalls
import FV.Backend.Proof.StockReturnSourceRuns

/-! Original dominance and real demand marks discharge return operand holding.
The retained source connection derives its helper execution internally. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem view_avail {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs, Ctx.defInst?, view.valDef, view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers, usersN, args, view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0, view.valDef, bytes, args]
  simp only [availIn, inFix_eq, users, bytes, work, view.valDef]


private theorem mapped_member {ctx : Ctx} {xs : List Nat} {rs : List Reg}
    (mapping : xs.mapM ctx.valueReg? = some rs) {x : Nat} (member : x ∈ xs) :
    ∃ r,ctx.valueReg? x = some r := by
  induction xs generalizing rs with
  | nil => cases member
  | cons y ys ih =>
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at mapping
    obtain ⟨r,lookup,rest,tail,equal⟩ := mapping
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨r,lookup⟩
    · exact ih tail member

/-- The original terminal availability guard includes implicit ABI operands;
actual helper demand and whole-run array bounds derive all requested holdings. -/
theorem stock_lower_return_guarded_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun x => Demanded record.output.state x ∧
      x ∈ availOf f (availIn f result.ctx) event.block b.body.length) event.ctx fr ρ) :
    ValuesHeld (fun x => x ∈ xs ++ sretRet f) event.ctx fr ρ := by
  obtain ⟨fuel,trace,rs,ps,enough,helper,root,mapped,pinned,state,code⟩ :=
    stock_lower_return_record_helper run scope events block ret records terminal recorded emitted
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  intro x member
  have available := (dominated.uses original ranges st0 oldBuild event.block b block).2 x
    (by simpa only [ret,abiTerm,Driver.termArgs] using member)
  have sourceAvailable : x ∈ availOf f (availIn f result.ctx) event.block b.body.length := by
    rw [view_avail view f]; exact available
  obtain ⟨r,lookup⟩ := mapped_member mapped member
  have bound := (Extent.lower_mapped_demand_bounds run scope events records lookup).1
  have normalized : (scanState record.input record.inst).demand.size = record.input.demand.size := by
    unfold scanState; dsimp only; split <;> rfl
  have demanded : Demanded record.output.state x := by
    rw [state]
    change Demanded ((xs ++ sretRet f).foldl State.mark (scanState record.input record.inst)) x
    exact (demanded_markList_iff _ _ x (by rwa [normalized])).mpr (Or.inl member)
  exact held x ⟨demanded,sourceAvailable⟩

/-- Successful original source returns refine the actual retained return code.
Helper execution, operand bounds, demand and availability are all derived from
the real whole-driver record; only the ordinary simulation invariant remains. -/
theorem stock_lower_return_record_source_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (func : s.frame.func = f) (callers : s.callers = [])
    (done : Clif.stepTerm env cp s (.ret xs) = .done vals cm)
    (defined : SourceDefinedAt f result.ctx event.block b.body.length s.frame)
    {ρ : Nat → CV} (held : ValuesHeld (fun x => Demanded record.output.state x ∧
      x ∈ availOf f (availIn f result.ctx) event.block b.body.length) event.ctx s.frame
      (fun key => ρ (aliasNum result.final.alias key)))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) :
    ∃ (rs ps : List Reg) (extra : List Clif.Val),
      record.output.emitted = #[.rets (rs.zip ps)] ∧ step.rules.getLast? = some rule_lower_2574.id ∧
      (xs ++ sretRet f).mapM event.ctx.valueReg? = some rs ∧
      returnPins f rs.length = some ps ∧ ps.length = rs.length ∧
      s.frame.getMany (xs ++ sretRet f) = .ok (vals ++ extra) ∧
      ∀ world,MR s.frame.slots s.mem world → ∃ ops world',
        seqRun isem (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
          some (.stop 0 ((.rets (rs.zip ps) : MInst).mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ops ρ world [] world' .ret) ∧
        AllHold (vals ++ extra) (vuses ops ρ) ∧ MR s.frame.slots s.mem world' := by
  obtain ⟨fuel,trace,actualRs,actualPs,enough,helper,root,mapped,pinned,state,code⟩ :=
    stock_lower_return_record_helper run scope events block ret records terminal recorded emitted
  have operands := stock_lower_return_guarded_operands run scope dominated events block ret records terminal recorded emitted held
  obtain ⟨rs,ps,extra,mapping,pins,count,read,full,unit,execution⟩ := stock_lower_return_source_run run scope dominated abi
    events block ret func callers done defined enough helper operands refines stable
  have sameRs := Option.some.inj (mapped.symm.trans mapping)
  subst actualRs
  have samePs := Option.some.inj (pinned.symm.trans pins)
  subst actualPs
  refine ⟨rs,ps,extra,code,root,mapping,pins,count,read,?_⟩
  intro world related
  simpa only [code,List.map_cons,List.map_nil] using execution world related
end Backend.Stock.Proof

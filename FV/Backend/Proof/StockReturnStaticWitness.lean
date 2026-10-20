import FV.Backend.Proof.StockReturnPlacedStatic
import FV.Backend.Proof.StockReturnStaticObservation
namespace Backend.Stock.Proof.ReturnStaticWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ReturnPlacedStaticDraft
open Backend.Stock.Proof.ReturnStaticDraft Backend.Stock.Proof.ReturnStaticFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower Stock.externCtor

/-- Complete original ordinary and implicit x8-return sources exercise actual
revised return construction, retained-record classification and final alias
static transport, with exact returned/prepared code and successful raw,
global-checked fallback and physical stages. -/
theorem stock_complete_return_static_witness (implicit : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (event : BlockScanEvent) (b : Clif.Block) (record : ScanRecord) (body : BlockScan) (rs ps : List Reg),
      Stock.lower (function implicit) = .ok result ∧ LowerScope (function implicit) ∧ Dominated (function implicit) ∧
      ArityOk (function implicit) ∧ sigAbiOk (function implicit).sig = true ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      event ∈ result.blockScans.toList ∧ SourceBodySplit (function implicit) event b record body ∧
      b.term = .ret (ReturnFixture.explicitXs (sourceCase implicit)) ∧
      record ∈ event.output.records ∧ record.inst = event.termInst ∧
      ((ReturnFixture.explicitXs (sourceCase implicit)) ++ sretRet (function implicit)).mapM event.ctx.valueReg? = some rs ∧
      (∀ r ∈ rs,∃ n,r = .vreg n .int) ∧ returnPins (function implicit) rs.length = some ps ∧
      (∀ xs ∈ rs.map (fun r => [r]),∀ r ∈ xs,∃ n,r = .vreg n .int) ∧
      Stock.externCtor event.ctx T.gen_return [.regsVec (rs.map (fun r => [r]))]
        (((ReturnFixture.explicitXs (sourceCase implicit)) ++ sretRet (function implicit)).foldl
          State.mark (scanState record.input record.inst)) = .ok (.op .unit,record.output.state) ∧
      record.output.emitted = #[.rets (rs.zip ps)] ∧ SpillInstOk (.rets (rs.zip ps)) ∧
      (∀ i ∈ (record.output.emitted.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))).toList,SpillInstOk i) ∧
      result.code.blocks[0]!.insts.back? = some (expected implicit) ∧
      p.code.blocks[0]!.insts.back? = some (expected implicit) ∧
      (∃ (label : Nat) (vb : VBlock) (k : Nat) (actualRs actualPs : List Reg),
        result.code.blocks[label]? = some vb ∧
        vb.insts[k]? = some ((.rets (actualRs.zip actualPs) : MInst).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ∧
        returnPins (function implicit) actualRs.length = some actualPs ∧
        SpillInstOk ((.rets (actualRs.zip actualPs) : MInst).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ∧
      (implicit = true → expected implicit = .rets [(.vreg 192 .int,.x 8)]) ∧
      (implicit = false → expected implicit = .rets [(.vreg 192 .int,.x 0),(.vreg 193 .int,.x 1)]) := by
  have actual := observed implicit
  unfold Observed at actual
  cases run : pipeline implicit with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨p,prepared,h⟩ := Except.bind_ok h
    obtain ⟨rf,allocated,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    cases h
    have checked := PerEdge.allocResultAt_checked allocated
    have fallback : rf = spillAllocAt p.code p.edges := by
      unfold allocResultAt checkedSpillAt at allocated
      simp only [bind,Except.bind] at allocated
      split at allocated <;> cases allocated
      rfl
    obtain ⟨scope,dominated,arity,abi⟩ := source_conditions implicit
    obtain ⟨other,event,oldRecord,step,extra,oldRun,oldScope,oldDom,oldAbi,events,oldRecords,rest⟩ :=
      ReturnSourceWitness.stock_return_complete_source_witness (sourceCase implicit) 0 0
    change Stock.lower (function implicit) = .ok other at oldRun
    rw [lowered] at oldRun
    cases oldRun
    obtain ⟨b,record,body,split⟩ := stock_lower_body_scan_split lowered scope events
    have bound := lt_of_getElem? split.block
    have length : (function implicit).blocks.length = 1 := rfl
    rw [length] at bound
    have zero : event.block = 0 := by omega
    have returned : b.term = .ret (ReturnFixture.explicitXs (sourceCase implicit)) := by
      have found := split.block
      rw [zero] at found
      have same : b = (function implicit).blocks[0]! := Option.some.inj (found.symm.trans (by rfl))
      rw [same]
      rfl
    have records : record ∈ event.output.records := by rw [split.records]; exact List.mem_cons_self ..
    obtain ⟨rs,ps,mapped,virtual,pins,code,gen,raw,resolved⟩ :=
      stock_lower_return_record_static lowered scope events split.block returned records split.termInst
    have matrix : ∀ xs ∈ rs.map (fun r => [r]),∀ r ∈ xs,∃ n,r = .vreg n .int := by
      intro xs member r inside
      obtain ⟨reg,present,rfl⟩ := List.mem_map.mp member
      have same := List.mem_singleton.mp inside
      subst r
      exact virtual reg present
    have helper := stock_gen_return_static matrix gen
    have position := stock_lower_return_instruction_static lowered scope events split.block returned records split.termInst
    exact ⟨result,p,rf,af,event,b,record,body,rs,ps,lowered,scope,dominated,arity,abi,
      prepared,fallback,checked,physical,events,split,returned,records,split.termInst,
      mapped,virtual,pins,matrix,gen,code,raw,resolved,actual.1,actual.2,position,
      by intro flag; subst implicit; rfl,by intro flag; subst implicit; rfl⟩
end Backend.Stock.Proof.ReturnStaticWitnessDraft

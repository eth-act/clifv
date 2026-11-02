import FV.Backend.Proof.StockFenceBodyFacts
import FV.Backend.Proof.StockMemoryOffsetSixteenScanRefines
import FV.Backend.Proof.StockMemoryIntegerScanRefines
import FV.Backend.Proof.StockMemoryOffsetEightStoreScanRefines
import FV.Backend.Proof.StockMemoryDivAccessRefines
import FV.Backend.Proof.StockFenceBodyRefines

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver
open Backend.Stock.Memory Backend.Stock.Memory.IntegerRoots Backend.Stock.Memory.StoreRoots
open MemoryFaults
set_option autoImplicit false
set_option Elab.async false

private theorem mapped_result {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {z : Nat} (source : event.ctx.insts[record.inst]? = some info)
    (results : info.results = [z]) {step : Step}
    (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ a,event.ctx.valueReg? z = some (.vreg a .int) := by
  obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan
    (stock_fence_record_execute run events records) recorded emitted
  have atInst : event.ctx.insts[record.inst]! = info := by
    simp only [getElem!_def,source,Option.getD_some]
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun (by rw [atInst]; exact results)
  obtain ⟨a,rfl⟩ := (stock_lower_record_context run scope events).1.valueReg z r mapped
  exact ⟨a,mapped⟩

/-- Every actual record of the unchanged mixed body refines successful source execution. -/
theorem mixed_record_fall_refines {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit function event b term body)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {sb : Nat} {syms : String → Option Nat} (memorySem : MemRefines F sb syms isem)
    {MR : MemRelT} (stable : MRStable F MR) (memoryOk : MemRelOk F sb syms function MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ∀ record ∈ body.records,ScanFallRefines (IndexedSourceInst env cp function event.ctx event.block)
      isem result.final.alias (GuardedScanRel function result event.ctx event.block MR) record := by
  have facts := mixed_actual_body_facts run events
  have lookup : function.blocks[0]? = some b := by simpa only [facts.1] using split.block
  have same : function.blocks[0]! = b := Option.some.inj lookup
  subst b
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  have bound : j < 7 := by
    have inside := (List.getElem?_eq_some_iff.mp statement).1
    exact inside
  have index : record.inst = j := by simpa [blockStart,facts.1] using current
  have retained := split.retained record member
  obtain ⟨step,recorded,emitted⟩ := facts.2.2.2 record retained (by omega)
  obtain ⟨info,source,original,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have inv := (stock_lower_record_context run scope events).1
  have casesJ : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have shape : stm = (function.blocks[0]!.body[0]!) := (Option.some.inj statement).symm
    subst stm
    obtain ⟨a,mapped⟩ := mapped_result run scope events retained source results recorded emitted
    have pointerType := inv.addr64 _ _ _ 7 source original rfl
    obtain ⟨nreg,pointer⟩ := inv.typedReg 7 _ pointerType
    exact stock_lower_integer_load_scan_fall_refines .w64 run scope dominated events retained split.block statement current
      source original results rfl mapped facts.2.2.1 pointer recorded emitted stable memorySem memoryOk
  · have shape : stm = (function.blocks[0]!.body[1]!) := (Option.some.inj statement).symm
    subst stm
    exact (stock_lower_fence_source_contract run scope dominated events retained source original).guarded
      refines env cp MR stable
  · have shape : stm = (function.blocks[0]!.body[2]!) := (Option.some.inj statement).symm
    subst stm
    obtain ⟨a,mapped⟩ := mapped_result run scope events retained source results recorded emitted
    exact stock_lower_addsub_scan_fall_refines run scope dominated events retained split.block statement current
      false source original results rfl mapped recorded emitted refines stable
  · have shape : stm = (function.blocks[0]!.body[3]!) := (Option.some.inj statement).symm
    subst stm
    have pointerType := inv.addr64 _ _ _ 7 source original rfl
    obtain ⟨pointerReg,pointer⟩ := inv.typedReg 7 _ pointerType
    obtain ⟨valueReg,value⟩ := inv.typedReg 100 _ facts.2.1
    exact stock_lower_integer_store_eight_scan_fall_refines .plain64 .i64 run scope dominated events retained
      split.block statement current source original (fun _ => facts.2.1) facts.2.2.1 pointer value
      recorded emitted stable (store_refines_of_mem memorySem) memoryOk
  · have shape : stm = (function.blocks[0]!.body[4]!) := (Option.some.inj statement).symm
    subst stm
    exact (stock_lower_fence_source_contract run scope dominated events retained source original).guarded
      refines env cp MR stable
  · have shape : stm = (function.blocks[0]!.body[5]!) := (Option.some.inj statement).symm
    subst stm
    obtain ⟨a,mapped⟩ := mapped_result run scope events retained source results recorded emitted
    exact stock_udiv_memory_fall_refines run scope dominated events retained split.block statement current
      source original results mapped recorded emitted refines rfl stable
  · have shape : stm = (function.blocks[0]!.body[6]!) := (Option.some.inj statement).symm
    subst stm
    obtain ⟨a,mapped⟩ := mapped_result run scope events retained source results recorded emitted
    have pointerType := inv.addr64 _ _ _ 7 source original rfl
    obtain ⟨nreg,pointer⟩ := inv.typedReg 7 _ pointerType
    exact stock_lower_integer_load_sixteen_scan_fall_refines .w64 run scope dominated events retained split.block statement current
      source original results rfl mapped facts.2.2.1 pointer recorded emitted stable memorySem memoryOk

end Backend.Stock.Proof.FenceFixture

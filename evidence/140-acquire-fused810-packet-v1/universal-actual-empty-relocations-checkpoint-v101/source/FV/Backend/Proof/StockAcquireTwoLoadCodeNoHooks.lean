import FV.Backend.Proof.StockAcquireTwoLoadEventNoHooks
import FV.Backend.Proof.StockAcquireAssemblyNoHooks
import FV.Backend.Proof.StockAcquireCodeBlockCount
import FV.Backend.Proof.StockEntryCode
import FV.Backend.Proof.StockAcquireTwoLoadCodeNoCall
import FV.Backend.Proof.PrepareSound

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Proof.Prep Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- Actual lowering and retained scans derive the raw preparation domain and complete code without model hooks. -/
theorem two_load_code_no_hook {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event) :
    PrepDomain result.code ∧
      ∀ block ∈ result.code.blocks.toList,∀ inst ∈ block.insts.toList,NoHookInst inst := by
  obtain ⟨ordered,count⟩ := stock_lower_code_block_count run
  obtain ⟨nodes,successors⟩ := two_load_order_shape ordered
  have one : result.code.blocks.size = 1 := by rw [count,nodes];rfl
  obtain ⟨ranges,params,before,data,core,raw,block,paramBytes,build,coreRun,assembled,
    coreEvents,present,blockCode⟩ := stock_lower_entry_assembly run scope
  have sameEvent : core.scan = event := actual_single_event size coreEvents events
  have ret : function.blocks[0]!.term = .ret [100,101] := rfl
  have coreCode := returned_core_code ret coreRun
  have coreNoCall : ∀ inst ∈ core.code.toList,NoHookInst inst := by
    rw [coreCode,sameEvent]
    exact two_load_event_no_hook run scope dominated events schedule
  have rawNoCall := assembled_entry_no_hook assembled coreNoCall
  have blockNoCall : ∀ inst ∈ block.insts.toList,NoHookInst inst := by
    intro inst member
    rw [blockCode] at member
    simp only [Array.toList_map,List.mem_map] at member
    obtain ⟨original,originalMember,rfl⟩ := member
    exact noHookInst_mapRegs (rawNoCall original originalMember) _
  obtain ⟨locs,stack,rows,signature,mapped,orderedRows,lookups,rawCode⟩ := assemble_entry_source_rows assembled
  have label : block.label = 0 := by rw [blockCode,rawCode]
  have arguments : block.branchArgs = #[] := by
    rw [blockCode,rawCode,successors]
    simp
  have single : result.code.blocks.toList = [block] := by
    obtain ⟨only,parts⟩ := List.length_eq_one_iff.mp (show result.code.blocks.toList.length = 1 by simpa using one)
    have member : block ∈ result.code.blocks.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? present)
    rw [parts] at member
    have equal := List.mem_singleton.mp member
    rwa [← equal] at parts
  have onlyBlock : ∀ b ∈ result.code.blocks.toList,b = block := by
    intro b member
    rw [single] at member
    exact List.mem_singleton.mp member
  constructor
  · refine ⟨by omega,?_,?_⟩
    · change (result.code.blocks.toList.map VBlock.label).Nodup
      rw [single]
      simp
    · intro b vb inst located last multi
      have equal := onlyBlock vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? located))
      rw [equal]
      exact arguments
  · intro b member
    rw [onlyBlock b member]
    exact blockNoCall

/-- Actual preparation in both original modes excludes every model-hook family internally. -/
theorem two_load_prepared_no_hook_insts {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {cleanup : Bool} {prepared : VCode}
    (preparedRun : prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared) :
    ∀ block ∈ prepared.blocks.toList,∀ inst ∈ block.insts.toList,NoHookInst inst := by
  obtain ⟨domain,noHook⟩ := two_load_code_no_hook run scope dominated size events schedule
  exact stage_prepare_no_hook_insts preparedRun domain noHook

end Backend.Stock.Proof.AcquireTwoLoadPrefix

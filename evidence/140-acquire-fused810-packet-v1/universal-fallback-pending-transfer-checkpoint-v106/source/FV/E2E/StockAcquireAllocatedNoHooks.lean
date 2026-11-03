import FV.E2E.StockAcquireAllocationNoHooks
import FV.Backend.Proof.StockAcquireTwoLoadCodeNoHooks

namespace Backend.Proof
open Backend E2E Backend.Proof.Driver Backend.Stock.Proof.Acquire810 Backend.Stock.Proof.AcquireTwoLoadPrefix
set_option autoImplicit false
set_option Elab.async false

/-- Actual allocator lowering adds only hook-free moves and frame markers. -/
theorem lowerRFunc_no_hooks {vc : VCode} {rf : RFunc} {af : AFunc}
    (run : lowerRFunc vc rf = .ok af)
    (noHook : ∀ block ∈ vc.blocks.toList, ∀ inst ∈ block.insts.toList, NoHookInst inst) :
    ∀ block ∈ af.blocks.toList, ∀ inst ∈ block.2.toList, NoHookAInst inst := by
  obtain ⟨⟨_, _, sizes, blocks⟩, _, _⟩ := lowerRFunc_ok run
  intro block member inst instMember
  obtain ⟨index, located⟩ := List.mem_iff_getElem?.mp member
  rw [Array.getElem?_toList] at located
  have bound := (Array.getElem?_eq_some_iff.1 located).1
  rw [sizes, Array.size_zip] at bound
  have vbBound : index < vc.blocks.size := by omega
  have rfBound : index < rf.blocks.size := by omega
  have vbLookup : vc.blocks[index]? = some vc.blocks[index] := Array.getElem?_eq_getElem vbBound
  have rfLookup : rf.blocks[index]? = some rf.blocks[index] := Array.getElem?_eq_getElem rfBound
  obtain ⟨code, codeRun, output⟩ := blocks index _ _ vbLookup rfLookup
  rw [located] at output
  cases output
  simp only [List.toList_toArray, List.mem_append] at instMember
  rcases instMember with prelude | body
  · split at prelude <;> simp_all [NoHookAInst]
  · exact itemsCode_no_hooks (noHook _ (by simpa using Array.mem_of_getElem? vbLookup)) codeRun inst body

/-- The fixed fixture derives the instruction-family fact in both actual preparation modes. -/
theorem two_load_allocated_no_hooks
    {result : Backend.Stock.Result} {cleanup : Bool} {prepared : VCode} {rf : RFunc} {af : AFunc}
    (run : Backend.Stock.lower Backend.Stock.Proof.AcquireTwoLoadPrefix.function = .ok result)
    (scope : LowerScope Backend.Stock.Proof.AcquireTwoLoadPrefix.function)
    (dominated : Dominated Backend.Stock.Proof.AcquireTwoLoadPrefix.function)
    (size : result.blockScans.size = 1) {event : Backend.Stock.BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    (preparedRun : prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared)
    (allocatedRun : lowerRFunc prepared rf = .ok af) :
    ∀ block ∈ af.blocks.toList, ∀ inst ∈ block.2.toList, NoHookAInst inst := by
  exact lowerRFunc_no_hooks allocatedRun
    (Backend.Stock.Proof.AcquireTwoLoadPrefix.two_load_prepared_no_hook_insts run scope dominated size events schedule preparedRun)

end Backend.Proof

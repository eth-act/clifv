import FV.Backend.StockCallStoreCheck
import FV.Backend.Proof.StockCallStoreSource
import FV.Backend.Proof.StockSourceEntry
import FV.E2E.StockLiveCallPrelude

namespace Backend.Stock.CallStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

structure Layout (f : Clif.Function) (result : Stock.Result) where
  data : SourceData
  source : sourceB f data = true
  records : result.blockScans.toList.all (scanB data result) = true
  reads : codeCheck f.sig result.code = true

theorem Layout.source_fields {f : Clif.Function} {result : Stock.Result} (layout : Layout f result) :
    f.blocks = [layout.data.block] ∧
    layout.data.block.params = [(layout.data.pointer,.i64),(layout.data.argument,.i64)] ∧
    layout.data.block.body = [⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩,
      ⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩] ∧
    layout.data.block.term = .ret [layout.data.called] ∧ f.sig.params.map (·.ty) = [.i64,.i64] ∧
    f.sig.returns.map (·.ty) = [.i64] ∧ layout.data.ext.sig.params.map (·.ty) = [.i64] ∧
    layout.data.ext.sig.returns = [layout.data.returned] ∧ layout.data.returned.ty = .i64 ∧
    f.extern? layout.data.fn = some layout.data.ext ∧ returnPins f 1 = some [.x 0] ∧
    layout.data.pointer ≠ layout.data.called ∧ layout.data.argument ≠ layout.data.called ∧
    layout.data.pointer ≠ layout.data.argument ∧ layout.data.flags = {} ∧
    (sigParamBytes layout.data.ext.sig).toOption = some [8] := by
  simpa only [sourceB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using layout.source

theorem Layout.scan_fields {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {event : Stock.BlockScanEvent} (member : event ∈ result.blockScans.toList) (entry : event.block = 0) :
    ∃ scan : ScanData,
      event.ctx.valueReg? layout.data.pointer = some (.vreg scan.pointer .int) ∧
      event.ctx.valueReg? layout.data.argument = some (.vreg scan.argument .int) ∧
      event.ctx.valueReg? layout.data.called = some (.vreg scan.calledRoot .int) ∧
      event.output.code = #[
        .call ⟨.sym layout.data.ext.name,retPairs [(scan.argument,.x 0)],callDefs [(.x 0,scan.calledDestination)]⟩,
        .store .store64 (.vreg scan.calledRoot .int) (.unsignedOffset (.vreg scan.pointer .int) 8) layout.data.flags,
        .rets (retPairs [(scan.calledRoot,.x 0)])] ∧
      aliasNum result.final.alias scan.calledRoot = aliasNum result.final.alias scan.calledDestination ∧
      aliasNum result.final.alias scan.pointer ≠ aliasNum result.final.alias scan.calledDestination := by
  have checked := List.all_eq_true.mp layout.records event member
  simp only [scanB,entry,beq_self_eq_true,↓reduceIte,Option.any_eq_true] at checked
  obtain ⟨scan,found,good⟩ := checked
  exact ⟨scan,by simpa only [scanFactsB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using good⟩

theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Stock.lower f = .ok result ∧ result.code = vc ∧ LowerScope f ∧ Dominated f ∧
      sigAbiOk f.sig = true ∧ Nonempty (Layout f result) ∧
      result.edgeArgs.all (fun row => row.all (·.isEmpty)) = true := by
  unfold check at checked
  cases data : sourceData? f with
  | none => simp only [data,Bool.false_eq_true] at checked
  | some source =>
    simp only [data] at checked
    cases lowered : Stock.lower f with
    | error message => simp only [lowered,Bool.and_false,Bool.false_eq_true] at checked
    | ok result =>
      simp only [lowered,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at checked
      obtain ⟨sourceOk,scope,dominated,abi,equal,records,reads,edges⟩ := checked
      exact ⟨result,rfl,equal,lowerScope_of scope,dominated_of dominated,abi,
        ⟨⟨source,sourceOk,records,by rwa [equal]⟩⟩,edges⟩

/-- The old generic prefix proof supplies the exact ABI reads before the call. -/
theorem prelude_read_checks {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) {block : VBlock} (placed : vc.blocks[0]? = some block)
    {prelude body : Array MInst} (pieces : block.insts = prelude ++ body)
    (noCalls : ∀ inst ∈ prelude.toList,∀ info,inst ≠ .call info) :
    ∀ j inst,prelude.toList[j]? = some inst → Backend.ABIReadOnly.instruction sig 0 j inst = true := by
  have blockMember : (block,0) ∈ vc.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using placed)
  have admitted := List.all_eq_true.mp checked (block,0) blockMember
  have admittedPrefix : LiveCall.prefixReads sig 0 0 (prelude.toList ++ body.toList) = true := by
    have first := Bool.and_eq_true_iff.mp admitted
    simpa only [pieces,Array.toList_append] using first.1
  simpa only [Nat.zero_add] using LiveCall.prefixReads_of_append admittedPrefix noCalls

end Backend.Stock.CallStore

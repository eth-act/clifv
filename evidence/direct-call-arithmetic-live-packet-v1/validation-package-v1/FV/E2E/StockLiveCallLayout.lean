import FV.Backend.StockLiveCallCheck
import FV.Backend.Proof.StockLiveCallSource
import FV.Backend.Proof.StockSourceEntry

namespace Backend.Stock.LiveCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

structure Layout (f : Clif.Function) (result : Stock.Result) where
  data : SourceData
  source : sourceB f data = true
  records : result.blockScans.toList.all (scanB data result) = true
  reads : codeCheck f.sig result.code = true

theorem Layout.source_fields {f : Clif.Function} {result : Stock.Result} (layout : Layout f result) :
    f.blocks = [layout.data.block] ∧ layout.data.block.params = [(layout.data.live,.i64)] ∧
    layout.data.block.body = [⟨[layout.data.called],.call layout.data.fn [layout.data.live]⟩,
      ⟨[layout.data.sum],.binary .iadd .i64 layout.data.called layout.data.live⟩] ∧
    layout.data.block.term = .ret [layout.data.sum] ∧ f.sig.params.map (·.ty) = [.i64] ∧
    f.sig.returns.map (·.ty) = [.i64] ∧ layout.data.ext.sig.params.map (·.ty) = [.i64] ∧
    layout.data.ext.sig.returns = [layout.data.returned] ∧ layout.data.returned.ty = .i64 ∧
    f.extern? layout.data.fn = some layout.data.ext ∧ returnPins f 1 = some [.x 0] ∧
    layout.data.live ≠ layout.data.called ∧ layout.data.sum ≠ layout.data.called ∧
    layout.data.sum ≠ layout.data.live ∧ (sigParamBytes layout.data.ext.sig).toOption = some [8] := by
  simpa only [sourceB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using layout.source

theorem Layout.scan_fields {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {event : Stock.BlockScanEvent} (member : event ∈ result.blockScans.toList) (entry : event.block = 0) :
    ∃ scan : ScanData,
      event.ctx.valueReg? layout.data.live = some (.vreg scan.live .int) ∧
      event.ctx.valueReg? layout.data.called = some (.vreg scan.calledRoot .int) ∧
      event.ctx.valueReg? layout.data.sum = some (.vreg scan.sumRoot .int) ∧
      event.output.code = #[
        .call ⟨.sym layout.data.ext.name,retPairs [(scan.live,.x 0)],callDefs [(.x 0,scan.calledDestination)]⟩,
        .aluRRR .add .size64 (.vreg scan.sumDestination .int) (.vreg scan.calledRoot .int) (.vreg scan.live .int),
        .rets (retPairs [(scan.sumRoot,.x 0)])] ∧
      aliasNum result.final.alias scan.calledRoot = aliasNum result.final.alias scan.calledDestination ∧
      aliasNum result.final.alias scan.sumRoot = aliasNum result.final.alias scan.sumDestination ∧
      aliasNum result.final.alias scan.live ≠ aliasNum result.final.alias scan.calledDestination := by
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

end Backend.Stock.LiveCall

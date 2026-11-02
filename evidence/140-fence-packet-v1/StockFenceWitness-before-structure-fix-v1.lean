import FV.Backend.Proof.StockFenceSemantics
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- A complete source function mixes trapping memory, arithmetic and two fences. -/
def function : Clif.Function := {
  name := "stock_fence_mixed"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [
    ⟨[63],.load .load .i64 {} 7 0⟩,
    ⟨[],.fence⟩,
    ⟨[100],.binary .iadd .i64 63 31⟩,
    ⟨[],.store .store .i64 {} 100 7 8⟩,
    ⟨[],.fence⟩,
    ⟨[],.trapz 31 .intDivz⟩,
    ⟨[128],.load .load .i64 {} 7 16⟩],term := .ret [128]}]}

private def observed : Option Bool :=
  (Stock.lower function).toOption.map fun result =>
    lowerScopeB function && dominatedB function &&
    result.blockScans.toList.any fun event =>
      [1,4].all fun i => event.output.records.any fun record =>
        decide (record.inst = i) &&
        (event.ctx.insts[i]?).any fun info => decide (info.clif = some .fence) &&
          decide (record.output.emitted = #[.fence]) &&
          decide (record.input.entryColor[i]! ≠ 0)

private theorem observed_true : observed = some true := by native_decide

private theorem successful_exists {α : Type} (value : Except String α) (test : α → Bool)
    (success : value.toOption.map test = some true) :
    ∃ result,value = .ok result ∧ test result = true := by
  cases value with
  | error message => cases success
  | ok result => exact ⟨result,rfl,Option.some.inj success⟩

/-- The complete mixed function inhabits both universal fence-record contracts. -/
theorem mixed_records :
    ∃ (result : Result) (event : BlockScanEvent), Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ event ∈ result.blockScans.toList ∧
      ∀ i ∈ [1,4], ∃ (record : ScanRecord) (info : IInfo), record ∈ event.output.records ∧
        record.inst = i ∧ event.ctx.insts[record.inst]? = some info ∧ info.clif = some .fence ∧
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.results = [] ∧ step.rules.getLast? = some 1024 ∧
          record.output.emitted = #[.fence] ∧
          record.output.state = {scanState record.input record.inst with
            base := (scanState record.input record.inst).base.emit .fence} := by
  have actual := observed_true
  unfold observed at actual
  obtain ⟨result,run,checked⟩ := successful_exists (Stock.lower function) _ actual
  obtain ⟨scopeB,domB,event,events,all⟩ := (by
    simpa only [Bool.and_eq_true,List.any_eq_true] using checked :
      lowerScopeB function = true ∧ dominatedB function = true ∧
      ∃ event ∈ result.blockScans.toList,
        [1,4].all (fun i => event.output.records.any fun record =>
          decide (record.inst = i) && (event.ctx.insts[i]?).any fun info =>
            decide (info.clif = some .fence) && decide (record.output.emitted = #[.fence]) &&
              decide (record.input.entryColor[i]! ≠ 0)) = true)
  refine ⟨result,event,run,lowerScope_of scopeB,dominated_of domB,events,?_⟩
  intro i member
  have row := List.all_eq_true.mp all i member
  obtain ⟨record,records,index,info,found,source,code,color⟩ := (by
    simpa only [List.any_eq_true,Option.any_eq_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using row :
      ∃ record ∈ event.output.records,record.inst = i ∧ ∃ info,
        event.ctx.insts[i]? = some info ∧ info.clif = some .fence ∧
          record.output.emitted = #[.fence] ∧ record.input.entryColor[i]! ≠ 0)
  have found' : event.ctx.insts[record.inst]? = some info := by rw [index]; exact found
  exact ⟨record,info,records,index,found',source,
    stock_lower_fence_record_exact run (lowerScope_of scopeB) events records found' source⟩

end Backend.Stock.Proof.FenceFixture

import FV.Backend.Proof.StockPatternSink
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- Preserve the accepted atomic i8/default-flags input and give its value one real consumer. -/
def function : Clif.Function := {
  name := "stock_acquire_fused810"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(1,.i64)],body := [
    ⟨[0],.atomicLoad .i8 {} 1⟩,
    ⟨[2],.extend .uextend .i64 0⟩],term := .ret [2]}]}

private def selected : Option Bool :=
  (Stock.lower function).toOption.map fun result => lowerScopeB function && dominatedB function &&
    result.blockScans.toList.any fun event =>
      event.output.records.any fun record => decide (record.inst = 1) &&
        record.output.step.any (fun step => step.rules.contains 810) &&
        record.output.emitted.toList.any (fun inst => match inst with
          | .loadAcquire ty _ _ flags => decide (ty = .int 8 ∧ flags = ({} : Clif.MemFlags))
          | _ => false)

private theorem selected_true : selected = some true := by native_decide -- witness: native_decide

private theorem successful_exists {α : Type} (value : Except String α) (test : α → Bool)
    (success : value.toOption.map test = some true) :
    ∃ result,value = .ok result ∧ test result = true := by
  cases value with
  | error message => cases success
  | ok result => exact ⟨result,rfl,Option.some.inj success⟩

/-- Root810 is reached in an actual original-scope Stock function.
The real retained consumer emits the acquire helper's original i8 memory operation. -/
theorem original_scope_selects810 :
    ∃ (result : Stock.Result) (event : BlockScanEvent) (record : ScanRecord),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.inst = 1 ∧
      (∃ step,record.output.step = some step ∧ 810 ∈ step.rules) ∧
      ∃ ty d pointer flags,.loadAcquire ty d pointer flags ∈ record.output.emitted.toList ∧
        ty = .int 8 ∧ flags = ({} : Clif.MemFlags) := by
  have observed := selected_true
  unfold selected at observed
  obtain ⟨result,lowered,observed⟩ := successful_exists (Stock.lower function) _ observed
  simp only [Bool.and_eq_true,List.any_eq_true,Option.any_eq_true,List.contains_eq_mem,decide_eq_true_eq] at observed
  obtain ⟨⟨scope,dominated⟩,event,events,record,records,parts⟩ := observed
  obtain ⟨⟨current,step,recorded,root⟩,inst,emitted,kind⟩ := parts
  refine ⟨result,event,record,lowered,lowerScope_of scope,dominated_of dominated,
    events,records,current,⟨step,recorded,?_⟩,?_⟩
  · simpa using root
  · cases inst <;> simp_all
    exact ⟨_,_,emitted⟩

end Backend.Stock.Proof.Acquire810

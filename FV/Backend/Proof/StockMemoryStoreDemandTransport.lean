import FV.Backend.Proof.StockMemoryComputedStoreRecordSpec
import FV.Backend.Proof.StockDemandedScan
import FV.Backend.Proof.StockMemoryStoreCoverage

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

private theorem scans_between {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti branch) indices input output)
    (ordered : indices.Pairwise (fun a b => b < a)) :
    ∀ first ∈ output.records, ∀ second ∈ output.records, second.inst < first.inst →
      DemandedUnsunkLe ctx first.output.state second.input ∧
      DemandedUnsunkLe ctx first.output.state second.output.state := by
  induction cert with
  | nil input => simp
  | @cons i indices input scan tail head rest ih =>
    obtain ⟨less,tailOrdered⟩ := List.pairwise_cons.mp ordered
    intro first firstMember second secondMember before
    rcases List.mem_cons.mp firstMember with rfl | firstMember
    · rcases List.mem_cons.mp secondMember with rfl | secondMember
      · exact False.elim (Nat.lt_irrefl _ before)
      · exact (stock_scans_demanded_unsunk rest).2 second secondMember
    · rcases List.mem_cons.mp secondMember with rfl | secondMember
      · have member : first.inst ∈ indices := by
          rw [← rest.order]
          exact List.mem_map.mpr ⟨first,firstMember,rfl⟩
        have smaller := less first.inst member
        change i < first.inst at before
        exact False.elim (by omega)
      · exact ih tailOrdered first firstMember second secondMember before

/-- Actual backward scans carry store demand to every earlier source record.
The same scan relation protects any definition that is unsunk after the store. -/
theorem stock_retained_store_demand_before (kind : Kind) (ty : Clif.Ty)
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {j value pointer : Nat} {flags : Clif.MemFlags}
    (spec : RetainedStoreReturnSpec kind ty f result event b j value pointer flags)
    {record : ScanRecord} (member : record ∈ spec.body.records)
    (earlier : record.inst < spec.record.inst) :
    Demanded spec.record.output.state value ∧
      Demanded record.input value ∧ Demanded record.output.state value ∧
      DemandedUnsunkLe event.ctx spec.record.output.state record.input ∧
      DemandedUnsunkLe event.ctx spec.record.output.state record.output.state := by
  have ordered : (sourceBodyIndices f event.block b).Pairwise (fun a b => b < a) := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b before => by omega) List.pairwise_lt_range
  obtain ⟨pre,post⟩ := scans_between spec.split.scanned ordered
    spec.record spec.bodyMember record member earlier
  obtain ⟨position,stm,statement,current⟩ := spec.split.positions spec.record spec.bodyMember
  have equal : position = j := by have h := current.symm.trans spec.current; omega
  subst position
  have wanted := (stock_lower_integer_store_operand_coverage kind run scope dominated events spec.records
    spec.split.block statement
    spec.current spec.source spec.clif spec.typed spec.parameter spec.pointerMapped spec.valueMapped
    spec.recorded spec.emitted value (Or.inl rfl)).1
  refine ⟨wanted,?_,?_,pre,post⟩
  · have grows := pre.1 value
    change record.input.demand[value]! ≠ 0
    change spec.record.output.state.demand[value]! ≠ 0 at wanted
    omega
  · have grows := post.1 value
    change record.output.state.demand[value]! ≠ 0
    change spec.record.output.state.demand[value]! ≠ 0 at wanted
    omega

/-- A successful retained store forces its earlier source definition to be emitted.
The actual RHS supplies its sink guard, including for loaded stored values. -/
theorem stock_retained_stored_definition_emitted (kind : Kind) (ty : Clif.Ty)
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {j value pointer : Nat} {flags : Clif.MemFlags}
    (spec : RetainedStoreReturnSpec kind ty f result event b j value pointer flags)
    {i : Nat} {stm : Clif.Stmt} (statement : b.body[i]? = some stm)
    (earlier : i < j) (definition : value ∈ stm.results) :
    ∃ (record : ScanRecord) (step : Step),
      record ∈ spec.body.records ∧ record.inst = blockStart f event.block+i ∧
      record.input.sunk[record.inst]! = false ∧ Demanded record.input value ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input =
        .ok record.output ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have indexed : blockStart f event.block+i ∈ sourceBodyIndices f event.block b := by
    unfold sourceBodyIndices
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr inside,rfl⟩
  rw [← spec.split.scanned.order] at indexed
  obtain ⟨record,member,current⟩ := List.mem_map.mp indexed
  have before : record.inst < spec.record.inst := by rw [current,spec.current]; omega
  obtain ⟨wanted,demanded,_,frame,_⟩ := stock_retained_store_demand_before kind ty
    run scope dominated events spec member before
  have defined := stock_lower_source_result_definition run dominated events spec.split.block statement definition
  obtain ⟨_,guard,_,state,_,_,_,_⟩ := stock_lower_integer_store_record_full kind run scope events
    spec.records spec.source spec.clif spec.typed spec.parameter spec.pointerMapped spec.valueMapped
    spec.recorded spec.emitted
  have safeAfter : spec.record.output.state.sunk[blockStart f event.block+i]! = false := by
    rw [state]
    exact guard _ defined
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events spec.split statement current
  have resultMember : value ∈ event.ctx.insts[record.inst]!.results := by
    simp only [getElem!_def,source,results]
    exact definition
  have safe : record.input.sunk[record.inst]! = false :=
    frame.2 record.inst value resultMember wanted (by simpa only [current] using safeAfter)
  have actual := scans_execute spec.split.scanned record member
  have ordinary : record.inst ≠ event.termInst := by rw [current,spec.split.termIndex]; omega
  obtain ⟨step,recorded,which⟩ := stock_ordinary_unsunk_decision safe ordinary actual
  have emitted : step.decision = .emitted := by
    rcases which with omitted | remembered | emitted
    · have zero := (scan_omitted actual recorded omitted).2.2.1 value resultMember
      exact False.elim (demanded (by simpa only [current] using zero))
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (spec.split.retained record member) recorded) remembered)
    · exact emitted
  exact ⟨record,step,member,current,safe,demanded,actual,spec.split.retained record member,recorded,emitted⟩

end Backend.Stock.Memory.StoreRoots

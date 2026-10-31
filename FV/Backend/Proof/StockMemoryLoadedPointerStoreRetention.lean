import FV.Backend.Proof.StockMemoryLoadedPointerStoreCoverage
import FV.Backend.Proof.StockMemoryStoreDemandTransport

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

/-- Actual computed-pointer stores retain every earlier definition of either operand.
The successful RHS derives both guards. Original source order carries their demand and unsunkness. -/
theorem stock_lower_loaded_pointer_store_definition_emitted (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {store : ScanRecord} (storeMember : store ∈ body.records) {j : Nat}
    (storeCurrent : store.inst = blockStart f event.block+j)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[store.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    {pointerInst sourcePointer : Nat} {pointerInfo : IInfo} {pointerFlags : Clif.MemFlags} {pointerOffset : Int}
    (pointerDefinition : event.ctx.defInst? pointer = some pointerInst)
    (pointerSource : event.ctx.insts[pointerInst]? = some pointerInfo)
    (pointerData : pointerInfo.data = .data 152 16
      [.data 151 29 [],.value sourcePointer,.op (.memFlags pointerFlags),.int pointerOffset])
    (pointerType : pointerInfo.resTys.head? = some (.int 64))
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {storeStep : Step} (storeRecorded : store.output.step = some storeStep)
    (storeEmitted : storeStep.decision = .emitted)
    {i key : Nat} {stm : Clif.Stmt} (statement : b.body[i]? = some stm)
    (earlier : i < j) (definition : key ∈ stm.results) (used : key = value ∨ key = pointer) :
    ∃ (record : ScanRecord) (step : Step),
      record ∈ body.records ∧ record.inst = blockStart f event.block+i ∧
      event.ctx.defInst? key = some record.inst ∧
      record.input.sunk[record.inst]! = false ∧ Demanded record.input key ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input =
        .ok record.output ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  have records := split.retained store storeMember
  obtain ⟨position,storeStm,storeStatement,current⟩ := split.positions store storeMember
  have same : position = j := by have eq := current.symm.trans storeCurrent; omega
  subst position
  have wanted := (stock_lower_loaded_pointer_store_operand_coverage kind run scope dominated events
    records split.block storeStatement storeCurrent source clif typed pointerDefinition pointerSource
    pointerData pointerType pointerMapped valueMapped storeRecorded storeEmitted key used).1
  have defined := stock_lower_source_result_definition run dominated events split.block statement definition
  obtain ⟨_,pointerGuard,valueGuard,_,state,_,_,_,_⟩ := stock_lower_loaded_pointer_store_record kind run scope
    events records source clif typed pointerDefinition pointerSource pointerData pointerType pointerMapped
    valueMapped storeRecorded storeEmitted
  have safeBefore : (scanState store.input store.inst).sunk[blockStart f event.block+i]! = false := by
    rcases used with rfl | rfl
    · exact valueGuard _ defined
    · exact pointerGuard _ defined
  have safeAfter : store.output.state.sunk[blockStart f event.block+i]! = false := by
    rw [state]
    exact safeBefore
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have indexed : blockStart f event.block+i ∈ sourceBodyIndices f event.block b := by
    unfold sourceBodyIndices
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr inside,rfl⟩
  rw [← split.scanned.order] at indexed
  obtain ⟨record,member,current⟩ := List.mem_map.mp indexed
  have ordered : (sourceBodyIndices f event.block b).Pairwise (fun a b => b < a) := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b before => by omega) List.pairwise_lt_range
  have before : record.inst < store.inst := by rw [current,storeCurrent]; omega
  have frame := (scans_between split.scanned ordered store storeMember record member before).1
  have demanded : Demanded record.input key := by
    have grows := frame.1 key
    change record.input.demand[key]! ≠ 0
    change store.output.state.demand[key]! ≠ 0 at wanted
    omega
  obtain ⟨producerInfo,producerSource,producerClif,producerResults⟩ :=
    ArithmeticBody.body_source_info run events split statement current
  have resultMember : key ∈ event.ctx.insts[record.inst]!.results := by
    simp only [getElem!_def,producerSource,producerResults]
    exact definition
  have safe : record.input.sunk[record.inst]! = false :=
    frame.2 record.inst key resultMember wanted (by simpa only [current] using safeAfter)
  have actual := scans_execute split.scanned record member
  have ordinary : record.inst ≠ event.termInst := by rw [current,split.termIndex]; omega
  obtain ⟨step,recorded,which⟩ := stock_ordinary_unsunk_decision safe ordinary actual
  have emitted : step.decision = .emitted := by
    rcases which with omitted | remembered | emitted
    · have zero := (scan_omitted actual recorded omitted).2.2.1 key resultMember
      exact False.elim (demanded zero)
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (split.retained record member) recorded) remembered)
    · exact emitted
  exact ⟨record,step,member,current,by simpa only [current] using defined,safe,demanded,actual,
    split.retained record member,recorded,emitted⟩

end Backend.Stock.Memory.StoreRoots

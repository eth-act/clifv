import FV.Backend.Proof.StockAcquireLayoutEncoding

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original availability only grows within a block; no later source step must execute. -/
theorem availOf_index_mono {f : Clif.Function} {entries : Array (List Clif.ValueId)}
    {bi before after : Nat} (order : before ≤ after) :
    ∀ value,value ∈ availOf f entries bi before → value ∈ availOf f entries bi after := by
  intro value available
  cases blockAt : f.blocks[bi]? with
  | none => simp only [availOf,blockAt,List.not_mem_nil] at available
  | some block =>
    simp only [availOf,blockAt,List.mem_filter,decide_eq_true_eq] at available ⊢
    obtain ⟨member,notLater⟩ := available
    constructor
    · rcases List.mem_append.mp member with entry | defined
      · exact List.mem_append_left _ entry
      · obtain ⟨statement,present,result⟩ := List.mem_flatMap.mp defined
        exact List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨statement,(List.take_prefix_take_left order).subset present,result⟩)
    · intro later
      obtain ⟨statement,present,result⟩ := List.mem_flatMap.mp later
      exact notLater (List.mem_flatMap.mpr
        ⟨statement,List.drop_subset_drop_left block.body order present,result⟩)

/-- Actual fresh code preserves the pending relation at an earlier fixed source boundary.
The original source frame, memory, captures, and source position do not advance after a fault. -/
theorem stock_lower_pending_frozen_source_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {statement : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statementAt : block.body[j]? = some statement)
    (current : record.inst = blockStart f bi+j)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {program : Clif.Program} {point : SourcePoint}
    {history : List (SunkReadSnapshot event.ctx env program)} {regs nextRegs : Nat → CV}
    {world nextWorld : Arm.ArmState} {sem : Backend.Proof.Sem}
    (order : point.1 ≤ j)
    (prior : PendingGuardedScanRel f result event.ctx bi env program MR history record.output.state point regs world)
    (defs : ∀ instruction ∈ record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs instruction,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg)
    (executed : seqRun sem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
      some (.fall nextRegs nextWorld))
    (same : SameWorld F nextWorld world) :
    PendingGuardedScanRel f result event.ctx bi env program MR history record.input point nextRegs nextWorld := by
  obtain ⟨function,dfg,memory,values⟩ := prior
  refine ⟨function,dfg,stable _ _ _ _ same.toNF memory,?_⟩
  have maps := (stock_lower_record_context run scope events).2.1
  intro value required notSuspended sourceValue lookup
  have decreased := stock_lower_record_demand_mono run events records recorded emitted value
  have demanded : Demanded record.output.state value := by
    have needed := required.1
    change record.input.demand[value]! ≠ 0 at needed
    change record.output.state.demand[value]! ≠ 0
    omega
  obtain ⟨key,mapped,held⟩ := values value ⟨demanded,required.2⟩ notSuspended sourceValue lookup
  have atRecord := availOf_index_mono order value required.2
  have preserved := stock_lower_available_fresh_frame run scope dominated events records blockAt statementAt current
    atRecord (by rw [← maps];exact mapped) defs executed
  exact ⟨key,mapped,by change VHolds sourceValue (nextRegs (aliasNum result.final.alias key));rw [preserved];exact held⟩

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockAcquireConsumedDemandRecovery

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Capture history remains exact when the ordered outstanding frontier consumes a read. -/
structure ReadEffectFrontier (ctx : Ctx) (env : Clif.Env) (program : Clif.Program) where
  history : List (SunkReadSnapshot ctx env program)
  retired : List (SunkReadSnapshot ctx env program)
  pending : List (SunkReadSnapshot ctx env program)
  split : history = retired++pending

/-- A real capture appends to both history and the outstanding ordered frontier. -/
def ReadEffectFrontier.capture {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (frontier : ReadEffectFrontier ctx env program) (captured : SunkReadSnapshot ctx env program) :
    ReadEffectFrontier ctx env program :=
  ⟨frontier.history++[captured],frontier.retired,frontier.pending++[captured],by rw [frontier.split,List.append_assoc]⟩

/-- Consumption keeps the complete history and retires only the actual queue head. -/
def ReadEffectFrontier.retire {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (frontier : ReadEffectFrontier ctx env program) (captured : SunkReadSnapshot ctx env program)
    (tail : List (SunkReadSnapshot ctx env program)) (head : frontier.pending = captured::tail) :
    ReadEffectFrontier ctx env program :=
  ⟨frontier.history,frontier.retired++[captured],tail,by rw [frontier.split,head,List.append_assoc];rfl⟩

/-- Every retired capture must recover its demanded bindings; zero demand is proved at its real consumer. -/
def RetiredUndemanded {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (frontier : ReadEffectFrontier ctx env program) (state : State) : Prop :=
  ∀ captured ∈ frontier.retired,∀ value ∈ ctx.insts[captured.record.inst]!.results,state.demand[value]! = 0

/-- Earlier retired results stay undemanded as the actual forward boundary decreases demand. -/
theorem retired_undemanded_of_le {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {frontier : ReadEffectFrontier ctx env program} {before after : State}
    (retired : RetiredUndemanded frontier before) (decreases : ∀ (value : Nat),after.demand[value]! ≤ before.demand[value]!) :
    RetiredUndemanded frontier after := by
  intro captured member value result
  have zero := retired captured member value result
  have bound := decreases value
  omega

/-- The actual emitted acquire retires its producer without hiding any demanded result in history. -/
theorem stock_lower_acquire_retired_undemanded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} (frontier : ReadEffectFrontier event.ctx env program)
    (captured : SunkReadSnapshot event.ctx env program) (tail : List (SunkReadSnapshot event.ctx env program))
    (head : frontier.pending = captured::tail) (producer : captured.record.inst = R.producer)
    (prior : RetiredUndemanded frontier record.output.state) :
    RetiredUndemanded (frontier.retire captured tail head) record.input := by
  have previous := retired_undemanded_of_le prior
    (stock_lower_record_demand_mono run events records recorded emitted)
  intro actual member value resultMember
  change actual ∈ frontier.retired++[captured] at member
  rcases List.mem_append.mp member with old | last
  · exact previous actual old value resultMember
  · have same := List.mem_singleton.mp last
    subst actual
    exact stock_lower_acquire_consumed_results_undemanded run scope dominated events records recorded emitted selectedId R
      value (by simpa only [producer] using resultMember)

/-- Retired history cannot suppress a current demanded binding. Only outstanding captures remain suspended. -/
theorem frontier_pending_values {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {frontier : ReadEffectFrontier ctx env program} {state : State} {available : Nat → Prop}
    {frame : Clif.Frame} {regs : Nat → CV}
    (held : PendingValuesHeld frontier.history (fun value => Demanded state value ∧ available value) frame regs)
    (retired : RetiredUndemanded frontier state) :
    PendingValuesHeld frontier.pending (fun value => Demanded state value ∧ available value) frame regs := by
  intro value required notPending
  apply held value required
  rintro ⟨captured,member,result⟩
  rw [frontier.split] at member
  rcases List.mem_append.mp member with old | pending
  · exact required.1 (retired captured old value result)
  · exact notPending ⟨captured,pending,result⟩

/-- Empty outstanding effects recover every original demanded available binding, despite retained history. -/
theorem frontier_final_values {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {frontier : ReadEffectFrontier ctx env program} {state : State} {available : Nat → Prop}
    {frame : Clif.Frame} {regs : Nat → CV}
    (held : PendingValuesHeld frontier.history (fun value => Demanded state value ∧ available value) frame regs)
    (retired : RetiredUndemanded frontier state) (finished : frontier.pending = []) :
    ValuesHeld (fun value => Demanded state value ∧ available value) ctx frame regs := by
  have pending := frontier_pending_values held retired
  rw [finished] at pending
  exact pending_values_nil.mp pending

/-- Final invariant recovery preserves the complete old source, DFG, memory and value fields. -/
theorem frontier_final_guarded {f : Clif.Function} {result : Result} {ctx : Ctx} {bi : Nat}
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT}
    {frontier : ReadEffectFrontier ctx env program} {state : State} {point : SourcePoint}
    {regs : Nat → CV} {world : Arm.ArmState}
    (held : PendingGuardedScanRel f result ctx bi env program MR frontier.history state point regs world)
    (retired : RetiredUndemanded frontier state) (finished : frontier.pending = []) :
    GuardedScanRel f result ctx bi MR state point regs world := by
  obtain ⟨func,dfg,memory,values⟩ := held
  exact ⟨func,dfg,memory,frontier_final_values values retired finished⟩

end Backend.Stock.Proof.Acquire810

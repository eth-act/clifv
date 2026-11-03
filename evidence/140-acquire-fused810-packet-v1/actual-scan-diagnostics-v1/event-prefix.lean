import FV.Backend.Proof.StockAcquireOpportunisticMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private def SunkDelta (before after : State) : Prop :=
  ∃ pending : List Nat,
    after.sunk = pending.foldl (fun bits producer => bits.set! producer true) before.sunk ∧
    ∀ target : Nat,before.sunk[target]! = true → after.sunk[target]! = true

private theorem delta_same {before after : State} (sunk : after.sunk = before.sunk) :
    SunkDelta before after := ⟨[],sunk,fun target marked => by rwa [sunk]⟩

private theorem delta_trans {before middle after : State}
    (first : SunkDelta before middle) (second : SunkDelta middle after) : SunkDelta before after := by
  obtain ⟨left,first,firstMono⟩ := first
  obtain ⟨right,second,secondMono⟩ := second
  refine ⟨left++right,?_,fun target marked => secondMono target (firstMono target marked)⟩
  rw [List.foldl_append,← first]
  exact second

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (spec : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction spec with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- Every retained event contains the actual successful scan, including all real decision paths. -/
theorem stock_lower_event_scan_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    scanBlock event.ctx event.block event.termInst event.isBranch event.indices event.input = .ok event.output := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeIndex,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq]
  exact (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2


end Backend.Stock.Proof.Acquire810

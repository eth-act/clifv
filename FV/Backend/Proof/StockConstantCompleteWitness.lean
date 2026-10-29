module

public import FV.Backend.Proof.StockConstantScanRefines
public import FV.Backend.Proof.StockConstantBoundaryWitness
public import FV.Backend.Proof.RefinesCSem
public import FV.E2E.RegLevelDriverSem

@[expose] public section

namespace Backend.Stock.Proof.ConstantComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

private theorem record_execute {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) :
    scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq] at records ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record records

/-- One actual source step and nonempty retained body inhabit unique constant
dispatch, receipt-free source transfer, scan refinement and mixed body composition.
The initial guarded relation holds for every world; the result is installed by
real emitted code. The saved stale-result/live-parameter witness also remains. -/
theorem complete_boundary_witness (X : ExtSem) :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord)
      (body : BlockScan) (s t : SourcePoint),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      body.records = [record] ∧
      (∃ step, record.output.step = some step ∧ step.decision = .emitted ∧
        step.rules.getLast? = some rule_lower_53.id) ∧
      ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
        [record.inst] record.input body ∧
      (∀ r ∈ body.records, MixedConstantOrOmittedRecord f event.ctx 0 r) ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} f event.ctx 0) [record.inst] s t ∧
      ScanFallRefines (IndexedSourceInst Clif.Env.empty {funcs := []} f event.ctx 0)
        (csem (fun _ => False) ⟨0,0⟩ X) result.final.alias
        (GuardedScanRel f result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)) record ∧
      ∀ w, GuardedScanRel f result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
        body.state s (fun _ => 0) w ∧
        ∃ ρ' w', seqRun (csem (fun _ => False) ⟨0,0⟩ X)
          (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
          (fun _ => 0) w = some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty) record.input t ρ' w' := by
  obtain ⟨f,result,event,record,b,info,step,oldFrame,oldPost,oldRegs,
    run,scope,dominated,events,records,block,statement,current,source,clif,results,mapped,
    recorded,emitted,oldSource,oldHeld⟩ := stock_lower_constant_record_boundary_witness
  let fr : Clif.Frame := {
    func := f
    regs := fun _ => none
    slots := []
    body := [⟨[2],.iconst .i8 9⟩]
    term := b.term }
  let fr' : Clif.Frame := {fr with regs := fr.regs.set 2 (.ofInt .i8 9),body := []}
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
      (fr,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨info,.iconst .i8 9,[.ofInt .i8 9],fr.regs.set 2 (.ofInt .i8 9),[],source,clif,
      by rw [results],rfl,by rw [results]; rfl,rfl⟩
  have dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) 0 0)) := by
    constructor
    · intro x j inf inst v defined found original pure lookup
      simp [restrict,fr] at lookup
    · intro x ty v typed lookup
      simp [restrict,fr] at lookup
  have held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) 0 0) event.ctx fr
      (fun k => (0 : CV)) := by
    intro y needed v lookup
    cases lookup
  let s : SourcePoint := (0,fr,Clif.Mem.empty)
  let t : SourcePoint := (1,fr',Clif.Mem.empty)
  have indexed : IndexedSourceInst Clif.Env.empty {funcs := []} f event.ctx 0 record.inst s t :=
    ⟨current,rfl,sourceStep⟩
  have steps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} f event.ctx 0)
      [record.inst] s t := .cons indexed (.nil t)
  let body : BlockScan := ⟨record.output.state,[record],record.output.emitted⟩
  have rebuild : (⟨record.inst,record.input,record.output⟩ : ScanRecord) = record := by cases record; rfl
  have scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      [record.inst] record.input body := by
    simpa only [body,Array.empty_append,rebuild] using
      (ScansSpec.cons (record_execute run events records) (ScansSpec.nil record.output.state))
  have families : ∀ r ∈ body.records, MixedConstantOrOmittedRecord f event.ctx 0 r := by
    intro r member
    have equal := List.mem_singleton.mp member
    subst r
    exact Or.inr ⟨0,b,⟨[2],.iconst .i8 9⟩,block,statement,current,step,recorded,emitted,
      info,.i8,9,2,193,source,clif,results,rfl,mapped⟩
  have retained : ∀ r ∈ body.records, r ∈ event.output.records := by
    intro r member
    have equal := List.mem_singleton.mp member
    subst r
    exact records
  have stable : MRStable (fun _ => False) (fun _ cm _ => cm = Clif.Mem.empty) :=
    fun _ _ _ _ _ memory => memory
  have scan := stock_lower_constant_scan_fall_refines run scope dominated events records
    block statement current source clif results rfl mapped recorded emitted
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable
    (env := Clif.Env.empty) (cp := {funcs := []})
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := selected_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have last : step.rules.getLast? = some rule_lower_53.id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  refine ⟨f,result,event,record,body,s,t,run,scope,dominated,events,records,rfl,
    ⟨step,recorded,emitted,last⟩,scanned,families,steps,scan,?_⟩
  intro w
  have initial : GuardedScanRel f result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
      body.state s (fun _ => 0) w := ⟨rfl,dfg,rfl,held⟩
  refine ⟨initial,?_⟩
  apply stock_lower_mixed_constant_body_fall_refines run scope dominated events scanned retained families
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable s t
    (by simpa using steps) _ w initial

end Backend.Stock.Proof.ConstantComplete

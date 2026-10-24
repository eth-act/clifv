import FV.Backend.Proof.StockAddSubScanRefines
import FV.Backend.Proof.StockActualAddSubBodyRefines
import FV.Backend.Proof.StockScalarAddWitness
import FV.Backend.Proof.StockPureUnsunk
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockPureRecordCoverage
import FV.Backend.Proof.LowerValueRelations

/-! Real retained-record and body non-vacuity witness for the arithmetic scan
composition. Native checks describe this fixed compiler trace only. -/
set_option autoImplicit false
namespace Backend.Stock.Proof.ScalarAddScanWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private def function := ScalarAdd.source "scalar_add_scan" .systemVI64 []
private theorem success : (Stock.lower function).isOk = true :=
  (ScalarAdd.code_and_success "scalar_add_scan" [] .systemVI64).1
private theorem option_some : (Stock.lower function).toOption.isSome := by
  have h := success
  cases hr : Stock.lower function with
  | error e => rw [hr] at h; change false = true at h; cases h
  | ok r => rfl
private def result : Result := (Stock.lower function).toOption.get option_some
private theorem get_ok {α : Type} (e : Except String α) (h : e.toOption.isSome) :
    e = .ok (e.toOption.get h) := by
  cases e with
  | error e => cases h
  | ok a => rfl
theorem event_bound : 0 < result.blockScans.size := by native_decide
private def event : BlockScanEvent := result.blockScans[0]'event_bound
theorem record_bound : 1 < event.output.records.length := by native_decide
private def record : ScanRecord := event.output.records[1]'record_bound
theorem step_some : record.output.step.isSome := by native_decide
private def step : Step := record.output.step.get step_some
theorem info_bound : 0 < event.ctx.insts.size := by native_decide
private def info : IInfo := event.ctx.insts[0]'info_bound
private def frame := ScalarAdd.Source.frame "scalar_add_scan" .systemVI64 [] 7 5
private def after : Clif.Frame := {frame with regs := frame.regs.set 2 ⟨.i64,12⟩,body := []}
private def registers (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+7) else if n = 193 then BitVec.ofNat 128 (2^100+5) else 0
private def body : BlockScan := ⟨record.output.state,[record],record.output.emitted⟩
private def s : SourcePoint := ⟨0,frame,Clif.Mem.empty⟩
private def t : SourcePoint := ⟨1,after,Clif.Mem.empty⟩

private theorem run : Stock.lower function = .ok result := get_ok _ option_some
private theorem events : event ∈ result.blockScans.toList := by
  exact Array.getElem_mem_toList event_bound
private theorem records : record ∈ event.output.records := List.getElem_mem record_bound
private theorem found : event.ctx.insts[0]? = some info := Array.getElem?_eq_getElem info_bound

theorem facts :
    record.inst = 0 ∧ info.clif = some (.binary .iadd .i64 0 1) ∧ info.results = [2] ∧
    event.ctx.valueReg? 2 = some (.vreg 194 .int) ∧ record.output.step = some step ∧
    step.decision = .emitted ∧
    event.ctx.defInst? 0 = none ∧ event.ctx.defInst? 1 = none ∧
    event.ctx.valueType? 0 = some (.int 64) ∧ event.ctx.valueType? 1 = some (.int 64) ∧
    event.ctx.valueReg? 0 = some (.vreg 192 .int) ∧ event.ctx.valueReg? 1 = some (.vreg 193 .int) ∧
    aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 193 = 193 ∧
    scanInstruction event.ctx event.block 0 event.termInst event.isBranch record.input = .ok record.output := by
  native_decide

private theorem source_step : IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx 0 0 s t := by
  obtain ⟨cur,clif,results,mapped,recorded,emitted,rest⟩ := facts
  refine ⟨rfl,rfl,?_⟩
  exact ⟨info,.binary .iadd .i64 0 1,[⟨.i64,12⟩],after.regs,[],found,clif,
    by rw [results]; rfl,by rfl,by rw [results]; rfl,rfl⟩

private theorem frame_available :
    (restrict frame (availOf function (availIn function result.ctx) 0 0)).regs = frame.regs := by
  funext x
  by_cases h0 : x = 0
  · subst x; exact restrict_regs_of_mem (by simp [availOf,function,ScalarAdd.source,D0.source,defsBefore,defsFrom])
  · by_cases h1 : x = 1
    · subst x; exact restrict_regs_of_mem (by simp [availOf,function,ScalarAdd.source,D0.source,defsBefore,defsFrom])
    · simp [restrict,frame,ScalarAdd.Source.frame,Clif.Regs.set,Clif.Regs.empty,h0,h1]

private theorem dfg : DFGCons event.ctx frame := by
  obtain ⟨_,_,_,_,_,_,d0,d1,t0,t1,rest⟩ := facts
  constructor
  · intro x j ii cl val defined lookup original pure value
    by_cases h0 : x = 0
    · subst x; rw [d0] at defined; cases defined
    · by_cases h1 : x = 1
      · subst x; rw [d1] at defined; cases defined
      · simp [frame,ScalarAdd.Source.frame,Clif.Regs.set,Clif.Regs.empty,h0,h1] at value
  · intro x ty val typed value
    by_cases h0 : x = 0
    · subst x; rw [t0] at typed; cases typed
      change some ⟨.i64,7⟩ = some val at value; cases value; rfl
    · by_cases h1 : x = 1
      · subst x; rw [t1] at typed; cases typed
        change some ⟨.i64,5⟩ = some val at value; cases value; rfl
      · simp [frame,ScalarAdd.Source.frame,Clif.Regs.set,Clif.Regs.empty,h0,h1] at value

private theorem held : ValuesHeld (fun _ => True) event.ctx frame
    (fun k => registers (aliasNum result.final.alias k)) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,m0,m1,a0,a1,rest⟩ := facts
  intro x _ val lookup
  by_cases h0 : x = 0
  · subst x
    change some ⟨.i64,7⟩ = some val at lookup; cases lookup
    refine ⟨192,m0,?_⟩
    dsimp only; rw [a0]; unfold VHolds registers; decide +kernel
  · by_cases h1 : x = 1
    · subst x
      change some ⟨.i64,5⟩ = some val at lookup; cases lookup
      refine ⟨193,m1,?_⟩
      dsimp only; rw [a1]; unfold VHolds registers; decide +kernel
    · simp [frame,ScalarAdd.Source.frame,Clif.Regs.set,Clif.Regs.empty,h0,h1] at lookup

/-- A real, nonempty, emitted add record and its actual one-statement body
inhabit both scan-composition roots, with dirty source operand registers. -/
theorem actual_scan_body_witness :
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
    ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      [0] record.input body ∧
    (∀ r ∈ body.records, SelectAddSubOrOmittedRecord function event.ctx 0 r) ∧
    IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx 0 0 s t ∧
    ∀ w, GuardedScanRel function result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
      body.state s registers w ∧
      ∃ ρ' w', seqRun ispec (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) registers w =
        some (.fall ρ' w') ∧
        GuardedScanRel function result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
          record.input t ρ' w' := by
  obtain ⟨cur,clif,results,mapped,recorded,emitted,_,_,_,_,_,_,_,_,actual⟩ := facts
  have scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
      [0] record.input body := by
    have build : ({inst := 0,input := record.input,output := record.output} : ScanRecord) = record := by
      cases hrec : record with
      | mk i input output =>
        have hi := cur
        rw [hrec] at hi
        simp only at hi
        cases hi
        rfl
    simpa only [body,Array.empty_append,build] using
      (ScansSpec.cons (exec := fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch) actual (ScansSpec.nil record.output.state))
  have family : SelectAddSubOrOmittedRecord function event.ctx 0 record := by
    right
    exact ⟨0,function.blocks[0]!,⟨[2],.binary .iadd .i64 0 1⟩,rfl,rfl,cur,step,recorded,emitted,
      false,info,.i64,0,1,2,194,by simpa [cur] using found,clif,results,rfl,mapped⟩
  have families : ∀ r ∈ body.records, SelectAddSubOrOmittedRecord function event.ctx 0 r := by
    intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact family
  have retained : ∀ r ∈ body.records, r ∈ event.output.records := by
    intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact records
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := by intro _ _ _ _ _ h; exact h
  have dom := ScalarAdd.lowering_domain "scalar_add_scan" [] .systemVI64
  have pre : ∀ w, GuardedScanRel function result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
      body.state s registers w := by
    intro w
    refine ⟨rfl,?_,rfl,?_⟩
    · have hp := dfgCons_congr (ctx := event.ctx) (fr := frame)
        (fr' := restrict frame (availOf function (availIn function result.ctx) 0 0))
        rfl rfl frame_available dfg
      exact hp
    · exact held.mono (fun _ _ => trivial)
  refine ⟨run,dom.2,dom.1,events,records,scanned,families,source_step,?_⟩
  intro w
  refine ⟨pre w,?_⟩
  have steps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx 0) [0] s t :=
    .cons source_step (.nil t)
  exact stock_lower_select_addsub_omitted_body_fall_refines run dom.2 dom.1 events scanned retained families
    self stable s t steps registers w (pre w)
theorem actual_record_tail : event.output.records.drop 1 = [record] := by native_decide
theorem actual_body_state : event.output.state = body.state := by native_decide
theorem actual_event_block : event.block = 0 := by native_decide

theorem actual_body_split_witness :
    ∃ b term scanned, SourceBodySplit function event b term scanned ∧
      (∀ r ∈ scanned.records, SelectAddSubOrOmittedRecord function event.ctx event.block r) ∧
      ∀ w, GuardedScanRel function result event.ctx event.block
        (fun _ cm _ => cm = Clif.Mem.empty) event.output.state s registers w ∧
        ∃ ρ' w', seqRun ispec (scanned.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) registers w =
            some (.fall ρ' w') ∧
          GuardedScanRel function result event.ctx event.block
            (fun _ cm _ => cm = Clif.Mem.empty) term.output.state t ρ' w' := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := by
    intro _ _ _ _ _ h; exact h
  have dom := ScalarAdd.lowering_domain "scalar_add_scan" [] .systemVI64
  obtain ⟨b,term,scanned,split,refines⟩ :=
    stock_lower_actual_select_addsub_omitted_body_refines run dom.2 dom.1 events self stable
  have recs : scanned.records = [record] := by
    have h := congrArg (List.drop 1) split.records
    simpa only [List.drop_succ_cons,List.drop_zero,actual_record_tail] using h.symm
  obtain ⟨_,_,_,_,_,_,family,source,behaviour⟩ := actual_scan_body_witness
  have families : ∀ r ∈ scanned.records,
      SelectAddSubOrOmittedRecord function event.ctx event.block r := by
    intro r member
    rw [recs] at member
    have same := List.mem_singleton.mp member
    subst r
    rw [actual_event_block]
    exact family record (by simp [body])
  have block := split.block
  rw [actual_event_block] at block
  have lookup : function.blocks[0]? = some function.blocks[0]! := rfl
  rw [lookup] at block
  have beq := (Option.some.inj block).symm
  subst b
  have indices : (List.range (function.blocks[0]!).body.length).map (blockStart function 0 + ·) = [0] := rfl
  have steps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx 0) [0] s t :=
    .cons source (.nil t)
  refine ⟨_,term,scanned,split,families,?_⟩
  intro w
  have pre : GuardedScanRel function result event.ctx event.block
      (fun _ cm _ => cm = Clif.Mem.empty) event.output.state s registers w := by
    rw [actual_event_block,actual_body_state]
    exact (behaviour w).1
  refine ⟨pre,?_⟩
  apply refines families s t ?_ registers w pre
  simpa only [actual_event_block,indices] using steps



theorem actual_pure_color_data :
    event.input.entryColor[0]! = 0 ∧ event.input.sunk[0]! = false := by native_decide

/-- The original pure arithmetic slot remains unsunk through the actual
terminator, ordinary body and every retained body-record boundary. -/
theorem actual_zeroColor_body_witness :
    ∃ b term scanned, SourceBodySplit function event b term scanned ∧
      scanBlock event.ctx event.block event.termInst event.isBranch
        (sourceBodyIndices function event.block b) term.output.state = .ok scanned ∧
      ZeroColorLe event.input term.output.state ∧
      ZeroColorLe term.output.state scanned.state ∧
      (∀ r ∈ scanned.records, r.input.sunk[0]! = false ∧ r.output.state.sunk[0]! = false) ∧
      scanned.state.sunk[0]! = false := by
  have dom := ScalarAdd.lowering_domain "scalar_add_scan" [] .systemVI64
  obtain ⟨b,term,scanned,split⟩ := stock_lower_body_scan_split run dom.2 events
  have initial := stock_scan_zeroColorLe split.termRun
  rw [split.termInput] at initial
  have actualRun : scanBlock event.ctx event.block event.termInst event.isBranch
      (sourceBodyIndices function event.block b) term.output.state = .ok scanned := by
    unfold scanBlock
    rw [runScans_ref]
    exact split.scanned.runScansRef
  have blockFrame := stock_scanBlock_zeroColorLe actualRun
  have frames := stock_scans_zeroColorLe split.scanned
  obtain ⟨zero,safe⟩ := actual_pure_color_data
  have termZero : term.output.state.entryColor[0]! = 0 := by rw [initial.1]; exact zero
  have termSafe := initial.2 0 zero safe
  refine ⟨b,term,scanned,split,actualRun,initial,blockFrame,?_,blockFrame.2 0 termZero termSafe⟩
  intro r member
  obtain ⟨pre,post⟩ := frames.2 r member
  exact ⟨pre.2 0 termZero termSafe,post.2 0 termZero termSafe⟩


/-- The whole-driver source corollary is inhabited by an actual compiled pure
function, with standard axioms only rather than fixed native trace premises. -/
theorem actual_whole_driver_pure_witness :
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    result.initial.entryColor[0]! = 0 ∧ result.final.sunk[0]! = false ∧
      ∀ e ∈ result.blockScans.toList, e.input.sunk[0]! = false ∧
        ∀ r ∈ e.output.records, r.input.sunk[0]! = false ∧ r.output.state.sunk[0]! = false := by
  have dom := ScalarAdd.lowering_domain "scalar_add_scan" [] .systemVI64
  refine ⟨run,dom.2,dom.1,?_⟩
  apply stock_lower_pure_single_block_unsunk run (b := function.blocks[0]!) rfl
  · intro stm member
    change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
    have same := List.mem_singleton.mp member
    subst stm
    rfl
  · decide


/-- Actual nonempty pure compilation inhabits source-derived scan-decision
coverage without a per-record or fixed-native decision premise. -/
theorem actual_pure_body_decisions_witness :
    Stock.lower function = .ok result ∧ LowerScope function ∧
      ∀ e ∈ result.blockScans.toList,
        ∃ term body, SourceBodySplit function e function.blocks[0]! term body ∧
          ∀ r ∈ body.records, ∃ step, r.output.step = some step ∧
            (step.decision = .omitted ∨ step.decision = .emitted) := by
  have dom := ScalarAdd.lowering_domain "scalar_add_scan" [] .systemVI64
  refine ⟨run,dom.2,?_⟩
  intro e events
  apply stock_lower_pure_body_decisions run dom.2 (b := function.blocks[0]!) rfl ?_ events
  intro stm member
  change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
  have same := List.mem_singleton.mp member
  subst stm
  rfl

end Backend.Stock.Proof.ScalarAddScanWitness

import FV.Backend.Proof.StockLocalSourceContinuation
import FV.Backend.Proof.StockMaskBlockRecords

namespace Backend.Stock.Proof.MaskBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

/-- Original source return and trap behavior through the complete body. -/
theorem actual_body_refines_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      (∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w') ∧
      (∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
        (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s code →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          TrapRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code) := by
  obtain ⟨term,body,split,classified⟩ := actual_families_at_block run scope family events block
  have formats : ∀ b' ∈ f.blocks,∀ stm ∈ b'.body,CastComplete.MemoryFormat stm.inst := by
    intro b' member stm present
    exact family_formats (family b' member stm present)
  have normal : ∀ r ∈ body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact Record.fall_refines run scope dominated events
      (split.retained r member) (classified r member) formats refines driver stable
  have trapping : ∀ r ∈ body.records,LocalScanTrapRefines
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact Record.trap_refines run scope dominated events
      (split.retained r member) (classified r member) refines
  refine ⟨term,body,split,?_,?_⟩
  · intro s s' source ρ w held
    apply split.scanned.fall_refines normal s s'
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held
  · intro s code source ρ w held
    apply split.scanned.local_trap_refines normal trapping s code
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held

end Backend.Stock.Proof.MaskBody

namespace Backend.Stock.Proof.MaskBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem block_local_family {b : Clif.Block} (family : ∀ stm ∈ b.body,Family stm.inst) :
    ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

/-- An actual complete source return supplies the current original block's
body execution; subsequent control flow remains in the source continuation. -/
theorem executable_body_return_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (remaining : s.frame.body = b.body) {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w) :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∃ t left,left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .returned vals mem ∧
        t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
        ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state
            (b.body.length,t.frame,t.mem) ρ' w' := by
  obtain ⟨term,body,split,normal,trapping⟩ := actual_body_refines_at_block run scope dominated family
    events block refines driver stable
  obtain ⟨t,left,total,continues,empty,steps,frame⟩ := LocalBody.actual_local_source_execution_frame
    run events split (block_local_family (family b (List.mem_of_getElem? block)))
    (j := 0) (by omega) (by simpa using remaining) returned
  obtain ⟨ρ',w',executed,post⟩ := normal (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
  exact ⟨term,body,split,t,left,by simpa using total,continues,empty,frame,ρ',w',executed,post⟩

/-- A real trapped source run either executes the current body's trap or
executes that body normally and retains the later trap in its continuation.
No return-only or empty-caller-stack premise is introduced. -/
theorem executable_body_trap_or_continue_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (remaining : s.frame.body = b.body) {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w) :
    ∃ term body,SourceBodySplit f event b term body ∧
      (TrapRun isem (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code ∨
       ∃ t left,left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .trapped code ∧
         t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
         ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
           (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
             some (.fall ρ' w') ∧
           GuardedScanRel f result event.ctx event.block MR term.output.state
             (b.body.length,t.frame,t.mem) ρ' w') := by
  obtain ⟨term,body,split,normal,trapping⟩ := actual_body_refines_at_block run scope dominated family
    events block refines driver stable
  refine ⟨term,body,split,?_⟩
  rcases LocalBody.actual_local_source_trap_or_continue run events split
    (block_local_family (family b (List.mem_of_getElem? block)))
    (j := 0) (by omega) (by simpa using remaining) trapped with failed | ⟨t,left,total,continues,empty,steps,frame⟩
  · left
    apply trapping (0,s.frame,s.mem) code _ ρ w held
    simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using failed
  · right
    obtain ⟨ρ',w',executed,post⟩ := normal (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
    exact ⟨t,left,by simpa using total,continues,empty,frame,ρ',w',executed,post⟩

end Backend.Stock.Proof.MaskBody

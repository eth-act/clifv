import FV.Backend.Proof.StockMaskBodyRecords

namespace Backend.Stock.Proof.MaskBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

private theorem body_formats {f : Clif.Function} {b : Clif.Block}
    (blocks : f.blocks = [b]) (family : ∀ stm ∈ b.body,Family stm.inst) :
    ∀ b' ∈ f.blocks,∀ stm ∈ b'.body,CastComplete.MemoryFormat stm.inst := by
  intro b' member stm present
  have same : b' = b := by simpa only [blocks,List.mem_singleton] using member
  subst b'
  exact family_formats (family stm present)

private theorem local_family {b : Clif.Block} (family : ∀ stm ∈ b.body,Family stm.inst) :
    ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  · simp [LocalBody.LocalInst,shape]
  · simp [LocalBody.LocalInst,shape]
  · simp [LocalBody.LocalInst,shape]

/-- Original source return and trap behavior through the complete body. -/
theorem actual_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
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
  obtain ⟨term,body,split,classified⟩ := actual_families run scope blocks family events
  have formats := body_formats blocks family
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

/-- Actual ABI entry and return for arbitrary proved scalar/division bodies, retaining arbitrary original values and original slots. -/
theorem actual_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body,Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  apply PureBody.actual_local_entry_return_refines_frame run scope dominated abi blocks
    (local_family family) ret entered returned refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_body_refines run scope dominated blocks family events refines driver stable
  exact ⟨term,body,split,normal⟩

/-- Actual ABI entry and the original trapped source prefix reach the selected
real coded trap inside the complete mixed function. -/
theorem actual_entry_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body,Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code := by
  apply LocalBody.actual_local_entry_trap_refines_frame run scope dominated blocks
    (local_family family) ret entered trapped refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_body_refines run scope dominated blocks family events refines driver stable
  exact ⟨term,body,split,trapping⟩

end Backend.Stock.Proof.MaskBody

namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem mixed_memory_formats {f : Clif.Function} {b : Clif.Block}
    (blocks : f.blocks = [b]) {front : List Clif.Stmt} {stm : Clif.Stmt}
    (shape : b.body = front ++ [stm]) (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat} (division : stm.inst = .div op ty x y) :
    ∀ b' ∈ f.blocks,∀ item ∈ b'.body,CastComplete.MemoryFormat item.inst := by
  intro b' member item present
  have same : b' = b := by simpa only [blocks,List.mem_singleton] using member
  subst b'
  rw [shape] at present
  rcases List.mem_append.mp present with earlier | final
  · exact HighMulBody.family_formats (family item earlier)
  · have same : item = stm := by simpa only [List.mem_singleton] using final
    subst item
    rw [division]
    cases op <;> cases ty <;> simp [CastComplete.MemoryFormat,instNames]

private theorem mixed_local_family {b : Clif.Block} {front : List Clif.Stmt} {stm : Clif.Stmt}
    (shape : b.body = front ++ [stm]) (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat} (division : stm.inst = .div op ty x y) :
    ∀ item ∈ b.body,LocalBody.LocalInst item.inst := by
  intro item member
  rw [shape] at member
  rcases List.mem_append.mp member with earlier | final
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure (family item earlier))
  · have same : item = stm := by simpa only [List.mem_singleton] using final
    subst item
    simp [LocalBody.LocalInst,division]

/-- The complete real mixed body preserves successful source execution and
all original coded traps through one actual scan and one guarded relation. -/
theorem actual_mixed_div_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
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
  obtain ⟨term,body,split,classified⟩ := actual_mixed_div_families run scope dominated blocks
    shape family division results ret events
  have formats := mixed_memory_formats blocks shape family division
  have normal : ∀ r ∈ body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact MixedDivRecord.fall_refines run scope dominated events
      (split.retained r member) (classified r member) formats refines driver stable
  have trapping : ∀ r ∈ body.records,ScanTrapRefines
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact MixedDivRecord.trap_refines run scope dominated events
      (split.retained r member) (classified r member) refines
  refine ⟨term,body,split,?_,?_⟩
  · intro s s' source ρ w held
    apply split.scanned.fall_refines normal s s'
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held
  · intro s code source ρ w held
    apply split.scanned.trap_refines normal trapping s code
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held

/-- Actual ABI entry and return for any proved scalar prefix followed by a
returned division, retaining arbitrary original values and original slots. -/
theorem actual_mixed_div_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  apply PureBody.actual_local_entry_return_refines_frame run scope dominated abi blocks
    (mixed_local_family shape family division) ret entered returned refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_mixed_div_body_refines run scope dominated blocks
    shape family division results ret events refines driver stable
  exact ⟨term,body,split,normal⟩

/-- Actual ABI entry and the original trapped source prefix reach the selected
real coded trap inside the complete mixed function. -/
theorem actual_mixed_div_entry_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code := by
  apply LocalBody.actual_local_entry_trap_refines_frame run scope dominated blocks
    (mixed_local_family shape family division) ret entered trapped refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_mixed_div_body_refines run scope dominated blocks
    shape family division results ret events refines driver stable
  exact ⟨term,body,split,trapping⟩

end Backend.Stock.Proof.DivBody
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_body_refines
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_entry_return_refines_frame
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_entry_trap_refines_frame

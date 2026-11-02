import FV.Backend.Proof.StockMemoryAccessPlacement
import FV.Backend.Proof.StockMemoryAccessSourcePrefix
import FV.Backend.Proof.StockMemoryAccessReach
import FV.Backend.Proof.StockEntryPrelude

/-! Draft: source-only ABI/whole-function trap composition.
No kernel command ran; the mixed-body provider still needs its derived record proofs. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem body_segment {vb : VBlock} {pre chunk post : Array MInst}
    (parts : vb.insts = pre ++ chunk ++ post) : SegAt vb pre.size chunk.toList := by
  intro k hk
  have bound : k < chunk.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- Compose actual ABI materialization and a proved local body with a genuine
source trap. Family handlers are internal proof obligations; the resulting
production domain retains the original input and executable source run. -/
theorem actual_ordinary_entry_access_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, OrdinaryBody.OrdinaryInst stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (property : BitVec 64 → Nat → Prop)
    (bodyProvider : ∀ event, event ∈ result.blockScans.toList →
      ∃ term body, SourceBodySplit f event b term body ∧
        ∀ s code, SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
          (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
          ((List.range b.body.length).map (blockStart f event.block+·)) s code →
          ∀ ρ w, ReachedGuardedRel f result event.ctx event.block MR env cp ⟨fr,[],cm⟩ event.output.state s ρ w →
            TrapOrAccessRun sb isem (body.code.toList.map (·.mapRegs
              (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code property)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code ∨
      VAccessTrapFrom sb result.code isem ⟨0,0,ρ,w⟩ code property := by
  obtain ⟨event,vb,pre,chunk,ρ',w',events,zero,placed,pieces,execution,mem',values,same,
    after,bodyCode⟩ := stock_lower_entry_prelude_refines_frame run scope dominated entered driver
      memorySem stable memory arguments
  obtain ⟨term,body,split,bodyRun⟩ := bodyProvider event events
  have facts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := facts
  have sameBlock : b' = b := by
    have found : some b = some b' := by
      simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  have sourceTrap := actual_ordinary_source_trap_execution run events split family
    (s := ⟨fr,[],cm⟩) (j := 0) (by omega) (by rw [frame]; simp)
    rfl (by rw [frame]; exact ret) trapped
  have held := stock_lower_entered_values_guarded_frame run scope dominated events entered values
    event.output.state w' mem'
  have reached : ReachedGuardedRel f result event.ctx event.block MR env cp ⟨fr,[],cm⟩
      event.output.state (0,fr,cm) ρ' w' := ⟨held,.refl _⟩
  have trap := bodyRun (0,fr,cm) code
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using sourceTrap) ρ' w' reached
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have parts : vb.insts = pre ++ body.code.map (·.mapRegs resolve) ++
      (term.output.emitted.map (·.mapRegs resolve) ++ after) := by
    rw [pieces,bodyCode,split.code,Array.map_append]
    simp only [Array.append_assoc,resolve]
  have segment : SegAt vb pre.size (body.code.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.toList_map] using body_segment parts
  have finished := trapOrAccessRun_at placed segment trap
  have room : pre.size < vb.insts.size := trapOrAccessRun_inbounds segment trap
  have preSegment : SegAt vb 0 pre.toList := by
    intro k bounded
    have inside : k < pre.size := by simpa only [Array.length_toList] using bounded
    rw [Nat.zero_add,pieces,Array.getElem?_append_left inside]
    simp [inside]
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed preSegment
    (by simpa only [Nat.zero_add,Array.length_toList] using room) execution
  rcases finished with explicit | access
  · exact ⟨entrySeed event.ctx fr,.inl (explicit.prefix
      (by simpa only [Nat.zero_add,Array.length_toList] using path))⟩
  · exact ⟨entrySeed event.ctx fr,.inr (VAccessTrapFrom.prefix
      (by simpa only [Nat.zero_add,Array.length_toList] using path) access)⟩

end Backend.Stock.Proof.MemoryFaults

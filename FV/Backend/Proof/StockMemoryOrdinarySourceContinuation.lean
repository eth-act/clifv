import FV.Backend.Proof.StockMemoryOrdinarySourceTrap

namespace Backend.Stock.Proof.OrdinaryBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem continuation_step {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : OrdinaryInst stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
  exact Clif.step_inst env cp s stm rest remaining family.1 family.2

/-- A trapped complete source run either traps in the current local body or
finishes that body and traps later. Arbitrary branch terminators and caller
stacks are retained; a later block's trap is never attributed to this body. -/
theorem actual_ordinary_source_trap_or_continue {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, OrdinaryInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    {code : Clif.TrapCode} (trapped : Clif.runLoop env cp fuel s = .trapped code) :
    SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (List.range' (blockStart f event.block+j) (b.body.length-j)) (j,s.frame,s.mem) code ∨
    ∃ t left,left+(b.body.length-j) = fuel ∧ Clif.runLoop env cp left t = .trapped code ∧
      t.frame.body = [] ∧
      SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        (List.range' (blockStart f event.block+j) (b.body.length-j))
        (j,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧ SourceFrameEq s t := by
  induction fuel generalizing j s with
  | zero => cases trapped
  | succ fuel ih =>
    by_cases done : j = b.body.length
    · subst j
      right
      refine ⟨s,fuel+1,by omega,trapped,?_,?_,rfl,rfl,rfl,rfl⟩
      · simpa using remaining
      · simp only [Nat.sub_self,List.range'_zero]
        exact .nil _
    · have inside : j < b.body.length := by omega
      let stm := b.body[j]
      have statement : b.body[j]? = some stm := List.getElem?_eq_getElem inside
      have head : s.frame.body = stm :: b.body.drop (j+1) := by
        rw [remaining,List.drop_eq_getElem_cons inside]
      have instFamily := family stm (List.mem_of_getElem? statement)
      have length : b.body.length-j = (b.body.length-(j+1))+1 := by omega
      rw [length,List.range'_succ]
      rw [Clif.runLoop_succ,continuation_step head instFamily] at trapped
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c =>
        simp only [evaluated,Clif.StepResult.ofRes,Clif.Outcome.trapped.injEq] at trapped
        cases trapped
        left
        apply SourceTrapSteps.here
        apply actual_ordinary_source_trap run events split statement instFamily head
        rw [continuation_step head instFamily,evaluated]
        rfl
      | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
      | ok pair =>
        obtain ⟨vs,cm⟩ := pair
        simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at trapped
        cases written : s.frame.regs.setMany stm.results vs with
        | none => simp only [written] at trapped; cases trapped
        | some regs =>
          simp only [written] at trapped
          let t : Clif.State := {s with frame := {s.frame with regs,body := b.body.drop (j+1)},mem := cm}
          have next : Clif.step env cp s = .next t := by
            rw [continuation_step head instFamily,evaluated]
            simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
            rfl
          have source := actual_ordinary_source_step run events split
            (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head next
          rcases ih (s := t) (j := j+1) (by omega) rfl trapped with failed | ⟨final,left,total,ends,empty,tail,frame⟩
          · left
            simpa only [Nat.add_assoc,Nat.add_comm 1 j] using SourceTrapSteps.next source failed
          · right
            refine ⟨final,left,by omega,ends,empty,?_,?_⟩
            · simpa only [Nat.add_assoc,Nat.add_comm 1 j] using SourceSteps.cons source tail
            · exact frame

end Backend.Stock.Proof.OrdinaryBody

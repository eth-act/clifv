import FV.Backend.Proof.StockMemoryOrdinarySourceTrap
import FV.Backend.Proof.StockMemoryNotrap

/-! Draft: generalize the existing source-prefix proof to ordinary memory effects.
No kernel command ran for this source. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem ordinary_step {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : OrdinaryBody.OrdinaryInst stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) :=
  Clif.step_inst env cp s stm rest remaining family.1 family.2

/-- A real trapped original run supplies the complete executable prefix up to
its first trapping local instruction. The empty returned body cannot trap. -/
theorem actual_ordinary_source_trap_execution {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, OrdinaryBody.OrdinaryInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    (callers : s.callers = []) {xs : List Nat} (ret : s.frame.term = .ret xs)
    {code : Clif.TrapCode} (trapped : Clif.runLoop env cp fuel s = .trapped code) :
    SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (List.range' (blockStart f event.block+j) (b.body.length-j)) (j,s.frame,s.mem) code := by
  induction fuel generalizing j s with
  | zero => cases trapped
  | succ fuel ih =>
    by_cases done : j = b.body.length
    · have empty : s.frame.body = [] := by simpa [done] using remaining
      exact False.elim (PureBody.pure_source_notrap (fuel+1) s callers
        (by simp [empty]) ret code trapped)
    · have inside : j < b.body.length := by omega
      let stm := b.body[j]
      have statement : b.body[j]? = some stm := List.getElem?_eq_getElem inside
      have head : s.frame.body = stm :: b.body.drop (j+1) := by
        rw [remaining,List.drop_eq_getElem_cons inside]
      have instFamily := family stm (List.mem_of_getElem? statement)
      have length : b.body.length-j = (b.body.length-(j+1))+1 := by omega
      rw [length,List.range'_succ]
      rw [Clif.runLoop_succ,ordinary_step head instFamily] at trapped
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c =>
        simp only [evaluated,Clif.StepResult.ofRes,Clif.Outcome.trapped.injEq] at trapped
        cases trapped
        apply SourceTrapSteps.here
        apply OrdinaryBody.actual_ordinary_source_trap run events split statement instFamily head
        rw [ordinary_step head instFamily,evaluated]
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
            rw [ordinary_step head instFamily,evaluated]
            simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
            rfl
          have source := OrdinaryBody.actual_ordinary_source_step run events split
            (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head next
          have tail := ih (s := t) (j := j+1) (by omega) rfl callers ret trapped
          have prefixStep := SourceTrapSteps.next source tail
          simpa only [Nat.add_assoc,Nat.add_comm 1 j] using prefixStep

end Backend.Stock.Proof.MemoryFaults

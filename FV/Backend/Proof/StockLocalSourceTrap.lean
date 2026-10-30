import FV.Backend.Proof.StockLocalSourceExecution
import FV.Backend.Proof.StockPureNotrap
import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.StockGuardedOmission
import FV.Backend.Proof.StockPureSourceColors
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockBlockScan
import FV.Backend.Proof.StockScanTrapSemantics



/-! Extract a genuine trapped prefix from the original executable source.
This is independent of the single-division shape and preserves original input
values, memory and trap code. The eventual compiler domain derives its record
obligations internally. -/
namespace Backend.Stock.Proof.LocalBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The previous pure family remains a local source family. -/
theorem LocalInst.of_pure {inst : Clif.Inst} (pure : pureInst inst = true) : LocalInst inst := by
  cases inst <;> simp_all [LocalInst,pureInst]

/-- A source position evaluates the actual installed original instruction to
its real trap. No success, nonzero, or no-overflow premise is introduced. -/
def IndexedSourceTrap (env : Clif.Env) (cp : Clif.Program) (f : Clif.Function)
    (ctx : Ctx) (bi i : Nat) (s : SourcePoint) (code : Clif.TrapCode) : Prop :=
  i = blockStart f bi + s.1 ∧ ∃ (info : IInfo) (inst : Clif.Inst) (rest : List Clif.Stmt),
    ctx.insts[i]? = some info ∧ info.clif = some inst ∧
    s.2.1.body = ⟨info.results,inst⟩ :: rest ∧
    instOutcome env cp s.2.1 s.2.2 inst = .trap code

private theorem local_step {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : LocalInst stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
  cases shape : stm.inst <;> simp only [shape,LocalInst,pureInst] at family <;> try cases family
  all_goals unfold Clif.step; simp only [remaining,shape]

theorem local_outcome {env : Clif.Env} {cp : Clif.Program}
    {fr : Clif.Frame} {cm : Clif.Mem} {inst : Clif.Inst} (family : LocalInst inst) :
    instOutcome env cp fr cm inst = Clif.evalInst fr cm inst := by
  cases inst <;> simp only [LocalInst,pureInst] at family <;> try cases family
  all_goals rfl

/-- Original execution provides a real instruction trap at the actual source
metadata position, using the same source-results identity as normal execution. -/
theorem actual_local_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (family : LocalInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) {code : Clif.TrapCode}
    (trapped : Clif.step env cp s = .trapped code) :
    IndexedSourceTrap env cp f event.ctx event.block (blockStart f event.block+j)
      (j,s.frame,s.mem) code := by
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split
    (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl
  refine ⟨rfl,info,stm.inst,rest,source,clif,?_,?_⟩
  · rw [remaining,results]
  · rw [local_outcome family]
    rw [local_step remaining family] at trapped
    cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
    | trap c =>
      simp only [evaluated,Clif.StepResult.ofRes,Clif.StepResult.trapped.injEq] at trapped
      cases trapped
      rfl
    | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok pair =>
      obtain ⟨vs,cm⟩ := pair
      simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at trapped
      cases written : s.frame.regs.setMany stm.results vs <;> simp only [written] at trapped <;> cases trapped


/-- A real trapped original run supplies the complete executable prefix up to
its first trapping local instruction. The empty returned body cannot trap. -/
theorem actual_local_source_trap_execution {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, LocalInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    (callers : s.callers = []) {xs : List Nat} (ret : s.frame.term = .ret xs)
    {code : Clif.TrapCode} (trapped : Clif.runLoop env cp fuel s = .trapped code) :
    SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (IndexedSourceTrap env cp f event.ctx event.block)
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
      rw [Clif.runLoop_succ,local_step head instFamily] at trapped
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c =>
        simp only [evaluated,Clif.StepResult.ofRes,Clif.Outcome.trapped.injEq] at trapped
        cases trapped
        apply SourceTrapSteps.here
        apply actual_local_source_trap run events split statement instFamily head
        rw [local_step head instFamily,evaluated]
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
            rw [local_step head instFamily,evaluated]
            simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
            rfl
          have source := actual_local_source_step run events split
            (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head next
          have tail := ih (s := t) (j := j+1) (by omega) rfl callers ret trapped
          have prefixStep := SourceTrapSteps.next source tail
          simpa only [Nat.add_assoc,Nat.add_comm 1 j] using prefixStep

end Backend.Stock.Proof.LocalBody


import FV.Backend.Proof.StockArithmeticSourceRefines
namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Frame components untouched by the arithmetic source body. -/
def SourceFrameEq (s t : Clif.State) : Prop :=
  t.callers = s.callers ∧ t.frame.func = s.frame.func ∧
    t.frame.slots = s.frame.slots ∧ t.frame.term = s.frame.term

private theorem SourceFrameEq.trans {s t u : Clif.State}
    (first : SourceFrameEq s t) (second : SourceFrameEq t u) : SourceFrameEq s u :=
  ⟨second.1.trans first.1,second.2.1.trans first.2.1,
    second.2.2.1.trans first.2.2.1,second.2.2.2.trans first.2.2.2⟩

private theorem arithmetic_next_of_returned_frame {env : Clif.Env} {cp : Clif.Program}
    {fuel : Nat} {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (subtract : Bool) {ty : Clif.Ty} {x y : Nat}
    (shape : stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp (fuel+1) s = .returned vals mem) :
    ∃ t, Clif.step env cp s = .next t ∧ t.frame.body = rest ∧
      Clif.runLoop env cp fuel t = .returned vals mem ∧ SourceFrameEq s t := by
  have step : Clif.step env cp s =
      Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
        (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
    unfold Clif.step
    simp only [remaining,shape]
  rw [Clif.runLoop_succ,step] at returned
  cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
  | trap code => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
  | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
  | ok value =>
    obtain ⟨vs,cm⟩ := value
    simp only [evaluated,Clif.StepResult.ofRes] at returned
    unfold Clif.continueWith at returned
    cases written : s.frame.regs.setMany stm.results vs with
    | none => simp only [written] at returned; cases returned
    | some regs =>
      simp only [written] at returned
      refine ⟨{s with frame := {s.frame with regs,body := rest},mem := cm},?_,rfl,returned,rfl,rfl,rfl,rfl⟩
      rw [step,evaluated]
      simp only [Clif.StepResult.ofRes,Clif.continueWith,written]

/-- The actual reference run supplies every ordinary arithmetic source step,
including the residual fuel and the exact state at the terminator. -/
theorem actual_arithmetic_source_execution_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem) :
    ∃ t left, left + (b.body.length-j) = fuel ∧
      Clif.runLoop env cp left t = .returned vals mem ∧ t.frame.body = [] ∧
      SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        (List.range' (blockStart f event.block+j) (b.body.length-j))
        (j,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧ SourceFrameEq s t := by
  induction fuel generalizing j s with
  | zero => cases returned
  | succ fuel ih =>
    by_cases done : j = b.body.length
    · subst j
      refine ⟨s,fuel+1,by omega,returned,?_,?_,rfl,rfl,rfl,rfl⟩
      · simpa using remaining
      · simp only [Nat.sub_self,List.range'_zero]
        exact .nil _
    · have inside : j < b.body.length := by omega
      let stm := b.body[j]
      have statement : b.body[j]? = some stm := List.getElem?_eq_getElem inside
      have head : s.frame.body = stm :: b.body.drop (j+1) := by
        rw [remaining,List.drop_eq_getElem_cons inside]
      obtain ⟨subtract,ty,x,y,shape⟩ := family stm (List.mem_of_getElem? statement)
      obtain ⟨next,stepped,rest,returned',frame⟩ := arithmetic_next_of_returned_frame head subtract shape returned
      obtain ⟨t,left,total,ends,empty,tail,tailFrame⟩ := ih (by omega) rest returned'
      have current := actual_arithmetic_source_step run events split
        (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl subtract shape head stepped
      refine ⟨t,left,by omega,ends,empty,?_,SourceFrameEq.trans frame tailFrame⟩
      have length : b.body.length-j = (b.body.length-(j+1))+1 := by omega
      rw [length,List.range'_succ]
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using SourceSteps.cons current tail

end Backend.Stock.Proof.ArithmeticBody

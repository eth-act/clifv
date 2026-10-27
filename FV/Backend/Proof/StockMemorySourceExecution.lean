import FV.Backend.Proof.StockLocalSourceExecution

/-! Additive source execution for ordinary instructions, including memory effects.
Only call-free step shape is used; memory and trap behavior remain unrestricted. -/
namespace Backend.Stock.Proof.OrdinaryBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Ordinary source instructions use evalInst directly. Calls retain their
separate source/external semantics and are not included in this step-shape predicate. -/
def OrdinaryInst (inst : Clif.Inst) : Prop :=
  (∀ fn args,inst ≠ .call fn args) ∧
  (∀ sig callee args,inst ≠ .callIndirect sig callee args)

private theorem step_of_family {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : OrdinaryInst stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
  exact Clif.step_inst env cp s stm rest remaining family.1 family.2

private theorem outcome_of_family {env : Clif.Env} {cp : Clif.Program}
    {fr : Clif.Frame} {cm : Clif.Mem} {inst : Clif.Inst} (family : OrdinaryInst inst) :
    instOutcome env cp fr cm inst = Clif.evalInst fr cm inst := by
  cases inst <;> try rfl
  all_goals first
    | exact False.elim (family.1 _ _ rfl)
    | exact False.elim (family.2 _ _ _ rfl)

/-- The original executable source step supplies the local-family indexed step. -/
theorem actual_ordinary_source_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord} {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block + j)
    (family : OrdinaryInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {s t : Clif.State} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (next : Clif.step env cp s = .next t) :
    IndexedSourceInst env cp f event.ctx event.block record.inst
      (j,s.frame,s.mem) (j+1,t.frame,t.mem) := by
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have remaining' : s.frame.body = ⟨info.results,stm.inst⟩ :: rest := by
    rw [remaining,results]
  rw [step_of_family remaining family] at next
  cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
  | trap code => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | ok value =>
    obtain ⟨vals,mem⟩ := value
    simp only [evaluated,Clif.StepResult.ofRes] at next
    unfold Clif.continueWith at next
    cases written : s.frame.regs.setMany stm.results vals with
    | none => simp only [written] at next; cases next
    | some regs =>
      simp only [written] at next
      cases next
      refine ⟨current,rfl,info,stm.inst,vals,regs,rest,source,clif,remaining',?_,?_,rfl⟩
      · rw [outcome_of_family family]; exact evaluated
      · rw [results]; exact written

abbrev SourceFrameEq := PureBody.SourceFrameEq

private theorem SourceFrameEq.trans {s t u : Clif.State}
    (first : SourceFrameEq s t) (second : SourceFrameEq t u) : SourceFrameEq s u :=
  ⟨second.1.trans first.1,second.2.1.trans first.2.1,
    second.2.2.1.trans first.2.2.1,second.2.2.2.trans first.2.2.2⟩

private theorem ordinary_next_of_returned_frame {env : Clif.Env} {cp : Clif.Program}
    {fuel : Nat} {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : OrdinaryInst stm.inst)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp (fuel+1) s = .returned vals mem) :
    ∃ t, Clif.step env cp s = .next t ∧ t.frame.body = rest ∧
      Clif.runLoop env cp fuel t = .returned vals mem ∧ SourceFrameEq s t := by
  have step : Clif.step env cp s =
      Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
        (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
    exact step_of_family remaining family
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

/-- The actual reference run supplies every ordinary local source step,
including the residual fuel and the exact state at the terminator. -/
theorem actual_ordinary_source_execution_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, OrdinaryInst stm.inst)
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
      have instFamily := family stm (List.mem_of_getElem? statement)
      obtain ⟨next,stepped,rest,returned',frame⟩ := ordinary_next_of_returned_frame head instFamily returned
      obtain ⟨t,left,total,ends,empty,tail,tailFrame⟩ := ih (by omega) rest returned'
      have current := actual_ordinary_source_step run events split
        (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head stepped
      refine ⟨t,left,by omega,ends,empty,?_,SourceFrameEq.trans frame tailFrame⟩
      have length : b.body.length-j = (b.body.length-(j+1))+1 := by omega
      rw [length,List.range'_succ]
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using SourceSteps.cons current tail

end Backend.Stock.Proof.OrdinaryBody

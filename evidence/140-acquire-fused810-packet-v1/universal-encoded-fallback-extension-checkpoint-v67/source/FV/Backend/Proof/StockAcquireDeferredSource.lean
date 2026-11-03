import FV.Backend.Proof.StockAcquireColorSegment
import FV.Backend.Proof.StockOmission

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A color-quiet source instruction preserves memory and cannot trap.
This fact also covers the original call-aware source outcome semantics. -/
theorem acquire_quiet_source_outcome {env : Clif.Env} {p : Clif.Program}
    {fr : Clif.Frame} {memory : Clif.Mem} {inst : Clif.Inst}
    (quiet : colored inst = false) :
    (∀ values nextMemory,instOutcome env p fr memory inst = .ok (values,nextMemory) → nextMemory = memory) ∧
      ∀ code,instOutcome env p fr memory inst ≠ .trap code := by
  have mandatory : mustLower inst = false := by
    unfold colored at quiet
    exact (Bool.or_eq_false_iff.mp quiet).1
  exact mustLower_outcome_quiet mandatory

private theorem quiet_step {env : Clif.Env} {p : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (quiet : colored stm.inst = false) :
    Clif.step env p s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (values,memory) => Clif.continueWith s rest stm.results values memory) := by
  cases shape : stm.inst <;> simp only [shape,colored,mustLower] at quiet <;> try cases quiet
  all_goals unfold Clif.step; simp only [remaining,shape]

/-- Actual source execution across a quiet instruction cannot introduce an earlier fault. -/
theorem acquire_quiet_source_step {env : Clif.Env} {p : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (quiet : colored stm.inst = false) :
    (∀ t,Clif.step env p s = .next t → t.mem = s.mem) ∧
      ∀ code,Clif.step env p s ≠ .trapped code := by
  have mandatory : mustLower stm.inst = false := by
    unfold colored at quiet
    exact (Bool.or_eq_false_iff.mp quiet).1
  have preserved := mustLower_quiet (fr := s.frame) (mem := s.mem) mandatory
  rw [quiet_step remaining quiet]
  cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
  | trap code => exact False.elim (preserved.2 code evaluated)
  | stuck message => simp [Clif.StepResult.ofRes]
  | ok value =>
    obtain ⟨values,memory⟩ := value
    have memoryEq := preserved.1 values memory evaluated
    simp only [Clif.StepResult.ofRes,Clif.continueWith]
    cases written : s.frame.regs.setMany stm.results values with
    | none => simp
    | some regs =>
      simp only [Clif.StepResult.next.injEq]
      constructor
      · intro t same
        cases same
        exact memoryEq
      · intro code impossible
        cases impossible

/-- The actual metadata interval excludes every source memory change and earlier source trap.
Its endpoint equality remains an internal metadata obligation of the selected record proof. -/
theorem acquire_color_interval_source {env : Clif.Env} {p : Clif.Program}
    (start : Nat) (xs : List (Clif.Stmt × Nat)) (colors : FenceColors.Colors)
    (unchanged : (xs.foldl (FenceColors.bodyNext start) colors).2 = colors.2) :
    ∀ x ∈ xs,∀ (fr : Clif.Frame) (memory : Clif.Mem),
      (∀ values nextMemory,instOutcome env p fr memory x.1.inst = .ok (values,nextMemory) →
        nextMemory = memory) ∧ ∀ code,instOutcome env p fr memory x.1.inst ≠ .trap code := by
  intro x member fr memory
  exact acquire_quiet_source_outcome (body_unchanged_color_quiet start xs colors unchanged x member)

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockParameterLoopCheck
import FV.Backend.Proof.StockParameterLoopProbe

/-! Non-vacuity of the loop parameter class (#140, T7b-5) on the `while` loop `%f0` of
`cranelift/filetests/filetests/inline/control-flow.clif` (`Probe.whileLoop`).

The forward class rejects its back edge `block2 → block1` (`forward_rejects_while_loop`). The
loop checker accepts the actual Stock lowering, so `check_sound` derives the unchanged production
domain. The source run from `(5, 7)` takes the back edge once and returns `5`. -/

namespace Backend.Stock.ParameterLoopCfg.Probe
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- The source outcome of the `while` loop from two argument words. -/
def sourceOutcome (x y : BitVec 32) : Option Clif.Outcome :=
  match Clif.enterFunc whileLoop [⟨.i32,x⟩,⟨.i32,y⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 16 ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  (match sourceOutcome 5 7 with | some (.returned vals _) => decide (vals = [⟨.i32,5⟩]) | _ => false) &&
  match Stock.lower whileLoop with
  | .error _ => false
  | .ok result => check whileLoop result.code

-- witness: native_decide (the fixed function's source run, lowering and loop checker only)
private theorem checks_true : checks = true := by native_decide

/-- **The `while` loop is in the checked loop class.** Its actual Stock lowering passes the loop
checker, which the forward checker rejects; `check_sound` derives `Scalar.Domain`; and its
source run, through the back edge, returns. -/
theorem while_loop_witness : Scalar.Domain whileLoop ∧
    (∃ mem,sourceOutcome 5 7 = some (.returned [⟨.i32,5⟩] mem)) ∧
    ∃ result,Stock.lower whileLoop = .ok result ∧ check whileLoop result.code = true ∧
      ParameterCfg.check whileLoop result.code = false := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨returns,lowered⟩ := h
  cases run : Stock.lower whileLoop with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨result',domain,run',_⟩ := check_sound lowered
    refine ⟨domain,?_,result,rfl,lowered,?_⟩
    · cases outcome : sourceOutcome 5 7 with
      | none => rw [outcome] at returns; cases returns
      | some o =>
        rw [outcome] at returns
        cases o with
        | returned vals mem =>
          simp only [decide_eq_true_eq] at returns
          exact ⟨mem,by rw [returns]⟩
        | _ => cases returns
    · simp [ParameterCfg.check,forward_rejects_while_loop]

end Backend.Stock.ParameterLoopCfg.Probe

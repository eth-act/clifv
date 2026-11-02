import FV.Backend.Proof.StockComparisonLoopCheck

/-! Non-vacuity of the comparison loop class (#140, T7b-7) on a `while (i < n)` loop whose
header branches on `icmp slt` of its own parameter and an entry parameter.

The parameter loop class rejects it, because the `brif` condition is not a parameter
(`parameter_loop_rejects_while_less`). The comparison loop checker accepts the actual Stock
lowering, so `check_sound` derives the unchanged production domain. The source run from
`(2, 5)` takes the back edge three times and returns `5`. -/

namespace Backend.Stock.ComparisonLoopCfg.Probe
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- `while (i < n) i += 1; return i`:
```
block0(v0: i64, v1: i64): jump block1(v0)
block1(v2: i64): v3 = icmp slt v2, v1; brif v3, block2, block3
block2: v4 = iconst.i64 1; v5 = iadd v2, v4; jump block1(v5)
block3: return v2
```
Block 1 is the loop header; the back edge `block2 → block1` carries `v5`, and the loop carries
the entry parameter `v1` of the comparison. -/
def whileLess : Clif.Function := {
  name := "while_less"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64),(1,.i64)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(2,.i64)], body := [⟨[3],.icmp .slt .i64 2 1⟩],
      term := .brif 3 ⟨2,[]⟩ ⟨3,[]⟩ },
    { id := 2, params := [],
      body := [⟨[4],.iconst .i64 1⟩,⟨[5],.binary .iadd .i64 2 4⟩],
      term := .jump ⟨1,[5]⟩ },
    { id := 3, params := [], body := [], term := .ret [2] }] }

/-- The parameter loop class rejects the `brif` on the comparison result `v3`. -/
theorem parameter_loop_rejects_while_less : ParameterLoopCfg.sourceOk whileLess = false := by decide

/-- The source outcome of the loop from two argument words. -/
def sourceOutcome (x y : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc whileLess [⟨.i64,x⟩,⟨.i64,y⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 32 ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  (match sourceOutcome 2 5 with | some (.returned vals _) => decide (vals = [⟨.i64,5⟩]) | _ => false) &&
  match Stock.lower whileLess with
  | .error _ => false
  | .ok result => check whileLess result.code

-- witness: native_decide (the fixed function's source run, lowering and comparison loop checker only)
private theorem checks_true : checks = true := by native_decide

/-- **The `while (i < n)` loop is in the checked comparison loop class.** Its actual Stock
lowering passes the comparison loop checker, which the parameter loop checker rejects;
`check_sound` derives `Scalar.Domain`; and its source run, through the back edge, returns. -/
theorem while_less_witness : Scalar.Domain whileLess ∧
    (∃ mem,sourceOutcome 2 5 = some (.returned [⟨.i64,5⟩] mem)) ∧
    ∃ result,Stock.lower whileLess = .ok result ∧ check whileLess result.code = true ∧
      ParameterLoopCfg.check whileLess result.code = false := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨returns,lowered⟩ := h
  cases run : Stock.lower whileLess with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨result',domain,run',_⟩ := check_sound lowered
    refine ⟨domain,?_,result,rfl,lowered,?_⟩
    · cases outcome : sourceOutcome 2 5 with
      | none => rw [outcome] at returns; cases returns
      | some o =>
        rw [outcome] at returns
        cases o with
        | returned vals mem =>
          simp only [decide_eq_true_eq] at returns
          exact ⟨mem,by rw [returns]⟩
        | _ => cases returns
    · simp [ParameterLoopCfg.check,parameter_loop_rejects_while_less]

end Backend.Stock.ComparisonLoopCfg.Probe

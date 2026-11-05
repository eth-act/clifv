import FV.Backend.Proof.StockComparisonComputedLoopCheck

/-! Non-vacuity of the computed comparison loop class (#140, CB-8) on a loop whose header
compares a computed value, as the loop header of `runtests/fibonacci.clif` does
(`v14 = iadd v10, v24` with `v24 = iconst -1`, then `icmp eq v14, _`).

The comparison loop class rejects it, because the first `icmp` operand is not a parameter
(`comparison_loop_rejects_countdown`). The computed comparison loop checker accepts the actual
Stock lowering (`sub`, `subs xzr`, `b.eq` in the header), so `check_sound` derives the unchanged
production domain. The source run from `(5, 2)` takes the back edge twice and returns `3`. -/

namespace Backend.Stock.ComparisonComputedLoopCfg.Probe
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- `while (i - 1 != n) i -= 1; return i`:
```
block0(v0: i64, v1: i64): jump block1(v0)
block1(v2: i64): v3 = iconst.i64 -1; v4 = iadd v2, v3; v5 = icmp eq v4, v1; brif v5, block3, block2
block2: jump block1(v4)
block3: return v2
```
Block 1 is the loop header; it compares the computed value `v4` with the entry parameter `v1`,
and the back edge `block2 → block1` carries `v4`. -/
def countdown : Clif.Function := {
  name := "countdown_until"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64),(1,.i64)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(2,.i64)],
      body := [⟨[3],.iconst .i64 (-1)⟩,⟨[4],.binary .iadd .i64 2 3⟩,⟨[5],.icmp .eq .i64 4 1⟩],
      term := .brif 5 ⟨3,[]⟩ ⟨2,[]⟩ },
    { id := 2, params := [], body := [], term := .jump ⟨1,[4]⟩ },
    { id := 3, params := [], body := [], term := .ret [2] }] }

/-- The comparison loop class rejects the `brif` on `icmp eq v4, v1`: `v4` is not a parameter. -/
theorem comparison_loop_rejects_countdown : ComparisonLoopCfg.sourceOk countdown = false := by decide

/-- The source outcome of the loop from two argument words. -/
def sourceOutcome (x y : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc countdown [⟨.i64,x⟩,⟨.i64,y⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 32 ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  (match sourceOutcome 5 2 with | some (.returned vals _) => decide (vals = [⟨.i64,3⟩]) | _ => false) &&
  match Stock.lower countdown with
  | .error _ => false
  | .ok result => check countdown result.code

-- witness: native_decide (the fixed function's source run, lowering and computed comparison loop checker only)
private theorem checks_true : checks = true := by native_decide

/-- **The countdown loop is in the checked computed comparison loop class.** Its actual Stock
lowering passes the computed comparison loop checker, which the comparison loop checker
rejects; `check_sound` derives `Scalar.Domain`; and its source run, through the back edge,
returns. -/
theorem countdown_witness : Scalar.Domain countdown ∧
    (∃ mem,sourceOutcome 5 2 = some (.returned [⟨.i64,3⟩] mem)) ∧
    ∃ result,Stock.lower countdown = .ok result ∧ check countdown result.code = true ∧
      ComparisonLoopCfg.check countdown result.code = false := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨returns,lowered⟩ := h
  cases run : Stock.lower countdown with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨result',domain,run',_⟩ := check_sound lowered
    refine ⟨domain,?_,result,rfl,lowered,?_⟩
    · cases outcome : sourceOutcome 5 2 with
      | none => rw [outcome] at returns; cases returns
      | some o =>
        rw [outcome] at returns
        cases o with
        | returned vals mem =>
          simp only [decide_eq_true_eq] at returns
          exact ⟨mem,by rw [returns]⟩
        | _ => cases returns
    · simp [ComparisonLoopCfg.check,comparison_loop_rejects_countdown]

end Backend.Stock.ComparisonComputedLoopCfg.Probe

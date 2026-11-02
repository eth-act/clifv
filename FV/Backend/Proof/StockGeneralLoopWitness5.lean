import FV.Clif.Parse
import FV.Backend.Proof.StockGeneralLoopCheck5
import FV.Backend.Proof.StockGeneralSubsumption5

/-! Non-vacuity of the legacy loop class with one-bit tests and zero extensions as conditions
(#140, CB-13): one loop per new condition form, each with a header branch that passes no block
arguments and a back edge that is a jump with an argument.

```
function %bit_loop(i32) -> i32 {          ; tbnz: band v1, (iconst 1)
block0(v0: i32):
    jump block1(v0)
block1(v1: i32):
    v2 = iconst.i32 1
    v3 = band v1, v2
    brif v3, block2, block3
block2:
    v4 = iadd v1, v1
    jump block1(v4)
block3:
    return v1
}
```

`%zero_bit_loop` branches on `icmp eq (band v1, (iconst 4)), (iconst 0)` (`tbz v1, #2`),
`%uext_cmp_loop` on `uextend.i32 (icmp slt v2, v1)` of two `i32` parameters (`subs` and `b.lt`
through `maybe_uextend`), and `%uext_plain_loop` on `uextend.i32 v1` of an `i8` parameter (`uxtb`
and `cbnz`). The CB-12b classes `GeneralLoopCfg4` and `GeneralArgsLoopCfg4` reject each function
(`earlier_classes_reject`): none of these conditions is one of theirs. The new selector accepts
each, and the checker accepts the actual unsplit code, whose per-edge vectors agree with the legacy
branch arguments. The source runs return `6` from `3`, `4` from `1`, `2` from `(0,2)` and `0` from
`3`. -/

namespace Backend.Stock.GeneralLoopCfg5.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%bit_loop`. -/
def bitSource : String := "function %bit_loop(i32) -> i32 {
block0(v0: i32):
    jump block1(v0)

block1(v1: i32):
    v2 = iconst.i32 1
    v3 = band v1, v2
    brif v3, block2, block3

block2:
    v4 = iadd v1, v1
    jump block1(v4)

block3:
    return v1
}
"

/-- `%bit_loop` as a `Clif.Function` literal. -/
def bitLoop : Clif.Function := {
  name := "bit_loop"
  sig := { params := [⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(1,.i32)],
      body := [⟨[2],.iconst .i32 1⟩,⟨[3],.binary .band .i32 1 2⟩],
      term := .brif 3 ⟨2,[]⟩ ⟨3,[]⟩ },
    { id := 2, params := [], body := [⟨[4],.binary .iadd .i32 1 1⟩], term := .jump ⟨1,[4]⟩ },
    { id := 3, params := [], body := [], term := .ret [1] }] }

/-- The text of `%zero_bit_loop`. -/
def zeroBitSource : String := "function %zero_bit_loop(i64) -> i64 {
block0(v0: i64):
    jump block1(v0)

block1(v1: i64):
    v2 = iconst.i64 4
    v3 = band v1, v2
    v4 = iconst.i64 0
    v5 = icmp eq v3, v4
    brif v5, block2, block3

block2:
    v6 = iadd v1, v1
    jump block1(v6)

block3:
    return v1
}
"

/-- `%zero_bit_loop` as a `Clif.Function` literal. -/
def zeroBitLoop : Clif.Function := {
  name := "zero_bit_loop"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(1,.i64)],
      body := [⟨[2],.iconst .i64 4⟩,⟨[3],.binary .band .i64 1 2⟩,⟨[4],.iconst .i64 0⟩,
        ⟨[5],.icmp .eq .i64 3 4⟩],
      term := .brif 5 ⟨2,[]⟩ ⟨3,[]⟩ },
    { id := 2, params := [], body := [⟨[6],.binary .iadd .i64 1 1⟩], term := .jump ⟨1,[6]⟩ },
    { id := 3, params := [], body := [], term := .ret [1] }] }

/-- The text of `%uext_cmp_loop`. -/
def uextComparisonSource : String := "function %uext_cmp_loop(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    jump block1(v0)

block1(v2: i32):
    v3 = icmp slt v2, v1
    v4 = uextend.i32 v3
    brif v4, block2, block3

block2:
    v5 = iconst.i32 1
    v6 = iadd v2, v5
    jump block1(v6)

block3:
    return v2
}
"

/-- `%uext_cmp_loop` as a `Clif.Function` literal. -/
def uextComparisonLoop : Clif.Function := {
  name := "uext_cmp_loop"
  sig := { params := [⟨.i32,.none,.normal⟩,⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32),(1,.i32)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(2,.i32)],
      body := [⟨[3],.icmp .slt .i32 2 1⟩,⟨[4],.extend .uextend .i32 3⟩],
      term := .brif 4 ⟨2,[]⟩ ⟨3,[]⟩ },
    { id := 2, params := [], body := [⟨[5],.iconst .i32 1⟩,⟨[6],.binary .iadd .i32 2 5⟩],
      term := .jump ⟨1,[6]⟩ },
    { id := 3, params := [], body := [], term := .ret [2] }] }

/-- The text of `%uext_plain_loop`. -/
def uextPlainSource : String := "function %uext_plain_loop(i8) -> i32 {
block0(v0: i8):
    jump block1(v0)

block1(v1: i8):
    v2 = uextend.i32 v1
    brif v2, block2, block3

block2:
    v3 = iconst.i8 -1
    v4 = iadd v1, v3
    jump block1(v4)

block3:
    return v2
}
"

/-- `%uext_plain_loop` as a `Clif.Function` literal. -/
def uextPlainLoop : Clif.Function := {
  name := "uext_plain_loop"
  sig := { params := [⟨.i8,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i8)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(1,.i8)], body := [⟨[2],.extend .uextend .i32 1⟩],
      term := .brif 2 ⟨2,[]⟩ ⟨3,[]⟩ },
    { id := 2, params := [], body := [⟨[3],.iconst .i8 (-1)⟩,⟨[4],.binary .iadd .i8 1 3⟩],
      term := .jump ⟨1,[4]⟩ },
    { id := 3, params := [], body := [], term := .ret [2] }] }

/-- The CB-12b legacy and split classes reject the four functions; their conditions are a one-bit
test, a zero test of a one-bit mask, a zero extension of a wide comparison and a plain zero
extension of the CB-13 classes. -/
theorem earlier_classes_reject :
    GeneralLoopCfg4.sourceOk bitLoop = false ∧ GeneralArgsLoopCfg4.sourceOk bitLoop = false ∧
    GeneralArgsLoopCfg5.testBitEligible bitLoop 3 = true ∧
    GeneralLoopCfg4.sourceOk zeroBitLoop = false ∧ GeneralArgsLoopCfg4.sourceOk zeroBitLoop = false ∧
    GeneralArgsLoopCfg5.testBitZeroEligible zeroBitLoop 5 = true ∧
    GeneralLoopCfg4.sourceOk uextComparisonLoop = false ∧ GeneralArgsLoopCfg4.sourceOk uextComparisonLoop = false ∧
    GeneralArgsLoopCfg5.uextComparisonEligible uextComparisonLoop 4 = true ∧
    GeneralLoopCfg4.sourceOk uextPlainLoop = false ∧ GeneralArgsLoopCfg4.sourceOk uextPlainLoop = false ∧
    GeneralArgsLoopCfg5.uextPlainEligible uextPlainLoop 2 = true := by
  decide

/-- The source outcome of `f` from the entry with fuel `fuel`, for the arguments `args`. -/
def sourceOutcome (f : Clif.Function) (fuel : Nat) (args : List Clif.Val) : Option Clif.Outcome :=
  match Clif.enterFunc f args Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

/-- The executable facts of one fixture: the literal is the parse of the text, the source run
returns `expected`, and the actual unsplit lowering keeps the legacy per-edge vectors and passes
the checker. -/
def fixtureChecks (source : String) (f : Clif.Function) (fuel : Nat) (args expected : List Clif.Val) : Bool :=
  decide ((Clif.parseFile source).funcs.map (·.func.toOption) = [some f]) &&
  (match sourceOutcome f fuel args with | some (.returned vals _) => decide (vals = expected) | _ => false) &&
  match Stock.lower f with
  | .error _ => false
  | .ok result => edgeLegacyCompatibleB result.code result.edgeArgs && check f result.code

/-- The executable facts of a fixture give its witness: the parse, `Scalar.Domain` (by
`check_sound`), the source return, and the accepted actual lowering. -/
theorem fixture_witness {source : String} {f : Clif.Function} {fuel : Nat} {args expected : List Clif.Val}
    (checked : fixtureChecks source f fuel args expected = true) :
    (Clif.parseFile source).funcs.map (·.func.toOption) = [some f] ∧ Scalar.Domain f ∧
    (∃ mem,sourceOutcome f fuel args = some (.returned expected mem)) ∧
    ∃ result,Stock.lower f = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check f result.code = true := by
  unfold fixtureChecks at checked
  simp only [Bool.and_eq_true] at checked
  obtain ⟨⟨parsed,returns⟩,lowered⟩ := checked
  refine ⟨of_decide_eq_true parsed,?_,?_,?_⟩
  · cases run : Stock.lower f with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      simp only [Bool.and_eq_true] at lowered
      obtain ⟨result',domain,_,_⟩ := check_sound lowered.2
      exact domain
  · cases outcome : sourceOutcome f fuel args with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases run : Stock.lower f with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      simp only [Bool.and_eq_true] at lowered
      exact ⟨result,rfl,lowered.1,lowered.2⟩

private def checks : Bool :=
  fixtureChecks bitSource bitLoop 40 [⟨.i32,3⟩] [⟨.i32,6⟩] &&
  fixtureChecks zeroBitSource zeroBitLoop 40 [⟨.i64,1⟩] [⟨.i64,4⟩] &&
  fixtureChecks uextComparisonSource uextComparisonLoop 40 [⟨.i32,0⟩,⟨.i32,2⟩] [⟨.i32,2⟩] &&
  fixtureChecks uextPlainSource uextPlainLoop 40 [⟨.i8,3⟩] [⟨.i32,0⟩]

-- witness: native_decide (the four fixed functions' parses, source runs, lowerings, compatibility checks and checkers only)
private theorem checks_true : checks = true := by native_decide -- witness: native_decide

private theorem all_checks :
    fixtureChecks bitSource bitLoop 40 [⟨.i32,3⟩] [⟨.i32,6⟩] = true ∧
    fixtureChecks zeroBitSource zeroBitLoop 40 [⟨.i64,1⟩] [⟨.i64,4⟩] = true ∧
    fixtureChecks uextComparisonSource uextComparisonLoop 40 [⟨.i32,0⟩,⟨.i32,2⟩] [⟨.i32,2⟩] = true ∧
    fixtureChecks uextPlainSource uextPlainLoop 40 [⟨.i8,3⟩] [⟨.i32,0⟩] = true := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨bit,zero⟩,comparison⟩,plain⟩ := h
  exact ⟨bit,zero,comparison,plain⟩

private theorem earlier_check {f : Clif.Function} {vc : VCode} (rejected : GeneralLoopCfg4.sourceOk f = false) :
    GeneralLoopCfg4.check f vc = false := by
  simp [GeneralLoopCfg4.check,rejected]

/-- **`%bit_loop` (a `tbnz` condition) is in the checked legacy loop class.** -/
theorem bit_loop_witness :
    (Clif.parseFile bitSource).funcs.map (·.func.toOption) = [some bitLoop] ∧ Scalar.Domain bitLoop ∧
    (∃ mem,sourceOutcome bitLoop 40 [⟨.i32,3⟩] = some (.returned [⟨.i32,6⟩] mem)) ∧
    ∃ result,Stock.lower bitLoop = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check bitLoop result.code = true ∧
      GeneralLoopCfg4.check bitLoop result.code = false := by
  obtain ⟨parsed,domain,returns,result,run,compatible,checked⟩ := fixture_witness all_checks.1
  exact ⟨parsed,domain,returns,result,run,compatible,checked,earlier_check earlier_classes_reject.1⟩

/-- **`%zero_bit_loop` (a `tbz` condition) is in the checked legacy loop class.** -/
theorem zero_bit_loop_witness :
    (Clif.parseFile zeroBitSource).funcs.map (·.func.toOption) = [some zeroBitLoop] ∧ Scalar.Domain zeroBitLoop ∧
    (∃ mem,sourceOutcome zeroBitLoop 40 [⟨.i64,1⟩] = some (.returned [⟨.i64,4⟩] mem)) ∧
    ∃ result,Stock.lower zeroBitLoop = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check zeroBitLoop result.code = true ∧
      GeneralLoopCfg4.check zeroBitLoop result.code = false := by
  obtain ⟨parsed,domain,returns,result,run,compatible,checked⟩ := fixture_witness all_checks.2.1
  exact ⟨parsed,domain,returns,result,run,compatible,checked,earlier_check earlier_classes_reject.2.2.2.1⟩

/-- **`%uext_cmp_loop` (a zero extension of a wide comparison) is in the checked legacy loop
class.** -/
theorem uext_comparison_loop_witness :
    (Clif.parseFile uextComparisonSource).funcs.map (·.func.toOption) = [some uextComparisonLoop] ∧
    Scalar.Domain uextComparisonLoop ∧
    (∃ mem,sourceOutcome uextComparisonLoop 40 [⟨.i32,0⟩,⟨.i32,2⟩] = some (.returned [⟨.i32,2⟩] mem)) ∧
    ∃ result,Stock.lower uextComparisonLoop = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check uextComparisonLoop result.code = true ∧
      GeneralLoopCfg4.check uextComparisonLoop result.code = false := by
  obtain ⟨parsed,domain,returns,result,run,compatible,checked⟩ := fixture_witness all_checks.2.2.1
  exact ⟨parsed,domain,returns,result,run,compatible,checked,
    earlier_check earlier_classes_reject.2.2.2.2.2.2.1⟩

/-- **`%uext_plain_loop` (a plain zero extension) is in the checked legacy loop class.** -/
theorem uext_plain_loop_witness :
    (Clif.parseFile uextPlainSource).funcs.map (·.func.toOption) = [some uextPlainLoop] ∧
    Scalar.Domain uextPlainLoop ∧
    (∃ mem,sourceOutcome uextPlainLoop 40 [⟨.i8,3⟩] = some (.returned [⟨.i32,0⟩] mem)) ∧
    ∃ result,Stock.lower uextPlainLoop = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check uextPlainLoop result.code = true ∧
      GeneralLoopCfg4.check uextPlainLoop result.code = false := by
  obtain ⟨parsed,domain,returns,result,run,compatible,checked⟩ := fixture_witness all_checks.2.2.2
  exact ⟨parsed,domain,returns,result,run,compatible,checked,
    earlier_check earlier_classes_reject.2.2.2.2.2.2.2.2.2.1⟩

end Backend.Stock.GeneralLoopCfg5.Fixture

import FV.Clif.Parse
import FV.Backend.Proof.StockGeneralLoopCheck7
import FV.Backend.Proof.StockGeneralSubsumption7

/-! Non-vacuity of the loop classes with plain `band` conditions (#140, CB-15).

The split class: a loop whose branches test a `band` with a register mask and a `band` with the
mask `300` (three set bits), and pass block arguments, on the back edge too.

```
function %band_loop(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    jump block1(v0)
block1(v2: i32):
    v3 = band v2, v1
    brif v3, block2(v2), block3(v2)
block2(v4: i32):
    v5 = iconst.i32 300
    v6 = band v4, v5
    v7 = iconst.i32 1
    v8 = isub v4, v7
    brif v6, block1(v8), block3(v8)
block3(v9: i32):
    return v9
}
```

From `(7,4)` the loop runs while bit 2 of the counter is set and returns `3`. The legacy class:
`%br_and_immediate` of `x64/branches.clif`, a branch on `band v0, 300` without block arguments; from
`301` it returns `100`. The CB-14c classes `GeneralArgsLoopCfg6` and `GeneralLoopCfg6` reject both
functions (`other_classes_reject`): their only `band` condition is the one-bit test of `tbnz`.
The new selectors accept them, and the actual code passes the new checkers, which derive the code
domain (split) and the production domain (legacy). -/

namespace Backend.Stock.GeneralArgsLoopCfg7.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%band_loop`. -/
def bandLoopSource : String := "function %band_loop(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    jump block1(v0)

block1(v2: i32):
    v3 = band v2, v1
    brif v3, block2(v2), block3(v2)

block2(v4: i32):
    v5 = iconst.i32 300
    v6 = band v4, v5
    v7 = iconst.i32 1
    v8 = isub v4, v7
    brif v6, block1(v8), block3(v8)

block3(v9: i32):
    return v9
}
"

/-- `%band_loop` as a `Clif.Function` literal. -/
def bandLoop : Clif.Function := {
  name := "band_loop"
  sig := { params := [⟨.i32,.none,.normal⟩,⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32),(1,.i32)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(2,.i32)], body := [⟨[3],.binary .band .i32 2 1⟩],
      term := .brif 3 ⟨2,[2]⟩ ⟨3,[2]⟩ },
    { id := 2, params := [(4,.i32)],
      body := [⟨[5],.iconst .i32 300⟩,⟨[6],.binary .band .i32 4 5⟩,⟨[7],.iconst .i32 1⟩,
        ⟨[8],.binary .isub .i32 4 7⟩],
      term := .brif 6 ⟨1,[8]⟩ ⟨3,[8]⟩ },
    { id := 3, params := [(9,.i32)], body := [], term := .ret [9] }] }

/-- The text of `%br_and_immediate` (`x64/branches.clif`). -/
def andImmediateSource : String := "function %br_and_immediate(i32) -> i32 {
block0(v0: i32):
  v1 = iconst.i32 300
  v2 = band v0, v1

  brif v2, block1, block2

block1:
  v3 = iconst.i32 100
  return v3

block2:
  v4 = iconst.i32 200
  return v4
}
"

/-- `%br_and_immediate` as a `Clif.Function` literal. -/
def andImmediate : Clif.Function := {
  name := "br_and_immediate"
  sig := { params := [⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32)], body := [⟨[1],.iconst .i32 300⟩,⟨[2],.binary .band .i32 0 1⟩],
      term := .brif 2 ⟨1,[]⟩ ⟨2,[]⟩ },
    { id := 1, params := [], body := [⟨[3],.iconst .i32 100⟩], term := .ret [3] },
    { id := 2, params := [], body := [⟨[4],.iconst .i32 200⟩], term := .ret [4] }] }

/-- The CB-14c classes reject both functions. -/
theorem other_classes_reject :
    GeneralArgsLoopCfg6.sourceOk bandLoop = false ∧ GeneralLoopCfg6.sourceOk bandLoop = false ∧
    GeneralArgsLoopCfg6.sourceOk andImmediate = false ∧ GeneralLoopCfg6.sourceOk andImmediate = false := by
  decide

/-- The source outcome of `f` from the entry with fuel `fuel`, for the arguments `args`. -/
def sourceOutcome (f : Clif.Function) (fuel : Nat) (args : List Clif.Val) : Option Clif.Outcome :=
  match Clif.enterFunc f args Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  decide ((Clif.parseFile bandLoopSource).funcs.map (·.func.toOption) = [some bandLoop]) &&
  (match sourceOutcome bandLoop 40 [⟨.i32,7⟩,⟨.i32,4⟩] with
    | some (.returned vals _) => decide (vals = [⟨.i32,3⟩]) | _ => false) &&
  sourceOk bandLoop &&
  (match Stock.lower bandLoop with
    | .error _ => false
    | .ok result =>
      match splitEdgesChecked result.code result.edgeArgs with
      | .ok split => check bandLoop split.code
      | .error _ => false) &&
  decide ((Clif.parseFile andImmediateSource).funcs.map (·.func.toOption) = [some andImmediate]) &&
  (match sourceOutcome andImmediate 20 [⟨.i32,301⟩] with
    | some (.returned vals _) => decide (vals = [⟨.i32,100⟩]) | _ => false) &&
  GeneralLoopCfg7.sourceOk andImmediate &&
  (match Stock.lower andImmediate with
    | .error _ => false
    | .ok result => GeneralLoopCfg7.check andImmediate result.code)

-- witness: native_decide (the two fixed functions' parses, source runs, selectors, input checks, lowering, split and checkers only)
private theorem checks_true : checks = true := by native_decide -- witness: native_decide

private theorem returned_of {f : Clif.Function} {fuel : Nat} {args : List Clif.Val} {expected : List Clif.Val}
    (returns : (match sourceOutcome f fuel args with
      | some (.returned vals _) => decide (vals = expected) | _ => false) = true) :
    ∃ mem,sourceOutcome f fuel args = some (.returned expected mem) := by
  cases outcome : sourceOutcome f fuel args with
  | none => rw [outcome] at returns; cases returns
  | some o =>
    rw [outcome] at returns
    cases o with
    | returned vals mem =>
      simp only [decide_eq_true_eq] at returns
      exact ⟨mem,by rw [returns]⟩
    | _ => cases returns

/-- **`%band_loop` (a loop whose branches test a `band` with a register mask and a `band` with a
three-bit constant mask, with block arguments) is in the checked split loop class, and
`%br_and_immediate` (a branch on `band v0, 300`) is in the checked legacy loop class.** The literals
are the parses of the texts; the selectors derive `Scalar.DomainAt` and `Scalar.Domain`; the source
runs return `3` and `100`; the actual split code of `%band_loop` passes the split checker, which
derives the code domain; the actual code of `%br_and_immediate` passes the legacy checker, which
derives the production domain of that code; the CB-14c classes reject both functions. -/
theorem band_loop_witness :
    (Clif.parseFile bandLoopSource).funcs.map (·.func.toOption) = [some bandLoop] ∧
    Scalar.DomainAt bandLoop ∧
    (∃ mem,sourceOutcome bandLoop 40 [⟨.i32,7⟩,⟨.i32,4⟩] = some (.returned [⟨.i32,3⟩] mem)) ∧
    GeneralArgsLoopCfg6.sourceOk bandLoop = false ∧ GeneralLoopCfg6.sourceOk bandLoop = false ∧
    (∃ result split,Stock.lower bandLoop = .ok result ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      check bandLoop split.code = true ∧ Scalar.CodeDomain bandLoop split.code) ∧
    (Clif.parseFile andImmediateSource).funcs.map (·.func.toOption) = [some andImmediate] ∧
    Scalar.Domain andImmediate ∧
    (∃ mem,sourceOutcome andImmediate 20 [⟨.i32,301⟩] = some (.returned [⟨.i32,100⟩] mem)) ∧
    GeneralArgsLoopCfg6.sourceOk andImmediate = false ∧ GeneralLoopCfg6.sourceOk andImmediate = false ∧
    ∃ result,Stock.lower andImmediate = .ok result ∧ GeneralLoopCfg7.check andImmediate result.code = true ∧
      Scalar.Domain andImmediate := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨parsed,returns⟩,source⟩,lowered⟩,parsedLegacy⟩,returnsLegacy⟩,sourceLegacy⟩,loweredLegacy⟩ := h
  refine ⟨of_decide_eq_true parsed,source_ok_sound source,returned_of returns,other_classes_reject.1,
    other_classes_reject.2.1,?_,of_decide_eq_true parsedLegacy,GeneralLoopCfg7.source_ok_sound sourceLegacy,
    returned_of returnsLegacy,other_classes_reject.2.2.1,other_classes_reject.2.2.2,?_⟩
  · cases run : Stock.lower bandLoop with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      dsimp only at lowered
      cases splitRun : splitEdgesChecked result.code result.edgeArgs with
      | error message => rw [splitRun] at lowered; cases lowered
      | ok split =>
        rw [splitRun] at lowered
        exact ⟨result,split,rfl,splitRun,lowered,check_sound lowered⟩
  · cases run : Stock.lower andImmediate with
    | error message => rw [run] at loweredLegacy; cases loweredLegacy
    | ok result =>
      rw [run] at loweredLegacy
      obtain ⟨result',domain,run',code⟩ := GeneralLoopCfg7.check_sound loweredLegacy
      exact ⟨result,rfl,loweredLegacy,domain⟩

end Backend.Stock.GeneralArgsLoopCfg7.Fixture

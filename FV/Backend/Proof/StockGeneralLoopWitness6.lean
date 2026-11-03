import FV.Clif.Parse
import FV.Backend.Proof.StockGeneralLoopCheck6
import FV.Backend.Proof.StockGeneralSubsumption6

/-! Non-vacuity of the legacy loop class with `br_table` terminators (#140, CB-14c): the function
`%f` of the Cranelift filetest `isa/aarch64/jumptable.clif`.

```
function %f(i32) -> i32 {
block0(v0: i32):
  br_table v0, block4, [block1, block2, block3]
block1:
  v1 = iconst.i32 1
  jump block5(v1)
...
block4:
  v4 = iconst.i32 4
  jump block5(v4)
block5(v5: i32):
  v6 = iadd.i32 v0, v5
  return v6
}
```

The entry block ends in a `br_table` on the `i32` parameter `v0`, with three table entries and no
block arguments; the jumps pass one argument each. The CB-13 classes `GeneralLoopCfg5` and
`GeneralArgsLoopCfg5` reject the function (`earlier_classes_reject`): they have no `br_table`.
The new legacy selector accepts it, and its checker accepts the actual unsplit code, whose
per-edge vectors agree with the legacy branch arguments. The source runs return `3` from `1`
(table entry `block2`) and `11` from `7` (the default `block4`). -/

namespace Backend.Stock.GeneralLoopCfg6.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%f` in `isa/aarch64/jumptable.clif`. -/
def jumptableSource : String := "function %f(i32) -> i32 {
block0(v0: i32):
  br_table v0, block4, [block1, block2, block3]

block1:
  v1 = iconst.i32 1
  jump block5(v1)

block2:
  v2 = iconst.i32 2
  jump block5(v2)

block3:
  v3 = iconst.i32 3
  jump block5(v3)

block4:
  v4 = iconst.i32 4
  jump block5(v4)

block5(v5: i32):
  v6 = iadd.i32 v0, v5
  return v6
}
"

/-- `%f` as a `Clif.Function` literal. -/
def jumptable : Clif.Function := {
  name := "f"
  sig := { params := [⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32)], body := [], term := .brTable 0 ⟨4,[]⟩ [⟨1,[]⟩,⟨2,[]⟩,⟨3,[]⟩] },
    { id := 1, params := [], body := [⟨[1],.iconst .i32 1⟩], term := .jump ⟨5,[1]⟩ },
    { id := 2, params := [], body := [⟨[2],.iconst .i32 2⟩], term := .jump ⟨5,[2]⟩ },
    { id := 3, params := [], body := [⟨[3],.iconst .i32 3⟩], term := .jump ⟨5,[3]⟩ },
    { id := 4, params := [], body := [⟨[4],.iconst .i32 4⟩], term := .jump ⟨5,[4]⟩ },
    { id := 5, params := [(5,.i32)], body := [⟨[6],.binary .iadd .i32 0 5⟩], term := .ret [6] }] }

/-- The CB-13 legacy and split classes reject `%f`: they have no `br_table` terminator. -/
theorem earlier_classes_reject :
    GeneralLoopCfg5.sourceOk jumptable = false ∧ GeneralArgsLoopCfg5.sourceOk jumptable = false := by
  decide

/-- The source outcome of `%f` from the entry with fuel `fuel`, for the index `index`. -/
def sourceOutcome (fuel : Nat) (index : BitVec 32) : Option Clif.Outcome :=
  match Clif.enterFunc jumptable [⟨.i32,index⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def returnsWith (fuel : Nat) (index result : BitVec 32) : Bool :=
  match sourceOutcome fuel index with
  | some (.returned vals _) => decide (vals = [⟨.i32,result⟩])
  | _ => false

private def checks : Bool :=
  decide ((Clif.parseFile jumptableSource).funcs.map (·.func.toOption) = [some jumptable]) &&
  returnsWith 10 1 3 && returnsWith 10 7 11 &&
  match Stock.lower jumptable with
  | .error _ => false
  | .ok result => edgeLegacyCompatibleB result.code result.edgeArgs && check jumptable result.code

-- witness: native_decide (the fixed function's parse, source runs, lowering, compatibility check and checker only)
private theorem checks_true : checks = true := by native_decide -- witness: native_decide

private theorem returns_of {fuel : Nat} {index result : BitVec 32} (checked : returnsWith fuel index result = true) :
    ∃ mem,sourceOutcome fuel index = some (.returned [⟨.i32,result⟩] mem) := by
  unfold returnsWith at checked
  cases outcome : sourceOutcome fuel index with
  | none => rw [outcome] at checked; cases checked
  | some o =>
    rw [outcome] at checked
    cases o with
    | returned vals mem =>
      simp only [decide_eq_true_eq] at checked
      exact ⟨mem,by rw [checked]⟩
    | _ => cases checked

private theorem earlier_check {vc : VCode} : GeneralLoopCfg5.check jumptable vc = false := by
  simp [GeneralLoopCfg5.check,earlier_classes_reject.1]

/-- **`%f` of `jumptable.clif` (a `br_table` on an `i32` parameter) is in the checked legacy loop
class.** The literal is the parse of the text; the checker derives `Scalar.Domain`; the source
returns `3` from `1` and `11` from `7`; the actual unsplit lowering keeps the legacy per-edge
vectors and passes the new checker, and the CB-13 checker rejects it. -/
theorem jumptable_witness :
    (Clif.parseFile jumptableSource).funcs.map (·.func.toOption) = [some jumptable] ∧
    Scalar.Domain jumptable ∧
    (∃ mem,sourceOutcome 10 1 = some (.returned [⟨.i32,3⟩] mem)) ∧
    (∃ mem,sourceOutcome 10 7 = some (.returned [⟨.i32,11⟩] mem)) ∧
    ∃ result,Stock.lower jumptable = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check jumptable result.code = true ∧
      GeneralLoopCfg5.check jumptable result.code = false := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨parsed,first⟩,second⟩,lowered⟩ := h
  cases run : Stock.lower jumptable with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    simp only [Bool.and_eq_true] at lowered
    obtain ⟨_,domain,_,_⟩ := check_sound lowered.2
    exact ⟨of_decide_eq_true parsed,domain,returns_of first,returns_of second,result,rfl,lowered.1,lowered.2,
      earlier_check⟩

end Backend.Stock.GeneralLoopCfg6.Fixture

import FV.E2E.ActualCompilerModes

/-! Preserve sliced function and binary checks over the actual callback table. -/
set_option autoImplicit false
namespace E2E.LinkCheck
open Backend

def globalBWithLowering (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) : Bool :=
  let R := I.resultsWithLowering lower stage
  (globalChks I (progOf R) (tabOf R)).all (·.2)

def fnsBWithLowering (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) (fs : List FnInput) : Bool :=
  let R := I.resultsWithLowering lower stage
  fs.all fun fi => (chksWith stage I (progOf R) (tabOf R) fi.func
    (I.pipeOfWithLowering lower stage fi)).all (·.2)

theorem fnsBWithLowering_append (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) (a b : List FnInput) :
    fnsBWithLowering I lower stage (a ++ b) =
      (fnsBWithLowering I lower stage a && fnsBWithLowering I lower stage b) := by
  simp only [fnsBWithLowering, List.all_append]

theorem okRWith_ofLowering {I : LinkInput} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode}
    (hg : globalBWithLowering I lower stage = true)
    (hf : fnsBWithLowering I lower stage I.funcs = true) :
    okRWith stage I (I.resultsWithLowering lower stage) = true := by
  unfold okRWith
  rw [Bool.and_eq_true]
  constructor
  · exact hg
  · simpa only [fnsBWithLowering, LinkInput.resultsWithLowering, List.all_map,
      Function.comp_def] using hf

end E2E.LinkCheck

namespace E2E.BinCheck
open Backend E2E.LinkCheck

theorem artsOkWithCompilerModes_append {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : VCode → VCode}
    {file : ByteArray} {a b : List FnInput}
    (ha : ArtsOkWithCompilerModes I lower stage file a)
    (hb : ArtsOkWithCompilerModes I lower stage file b) :
    ArtsOkWithCompilerModes I lower stage file (a ++ b) := by
  intro fi hfi
  rcases List.mem_append.mp hfi with h | h
  · exact ha fi h
  · exact hb fi h
end E2E.BinCheck

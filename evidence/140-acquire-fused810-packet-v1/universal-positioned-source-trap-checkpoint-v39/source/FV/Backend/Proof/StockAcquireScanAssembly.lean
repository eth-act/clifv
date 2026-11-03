import FV.Backend.Proof.StockAcquirePendingRecordMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual backward scans place whole emitted chunks in reverse record order.
The original instruction order inside each chunk remains exact. -/
theorem scans_forward_chunks {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output) :
    output.code.toList = output.records.reverse.flatMap (fun record => record.output.emitted.toList) := by
  induction spec with
  | nil => rfl
  | @cons inst indices before scan tail head rest ih =>
    simp only [Array.toList_append,List.reverse_cons,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil]
    exact congrArg (fun code => code++scan.emitted.toList) ih

/-- Successful real scanning supplies its actual forward chunk assembly without a supplied schedule. -/
theorem scanBlock_forward_chunks {ctx : Ctx} {block termInst : Nat} {branch : Bool}
    {indices : List Nat} {before : State} {output : BlockScan}
    (run : scanBlock ctx block termInst branch indices before = .ok output) :
    output.code.toList = output.records.reverse.flatMap (fun record => record.output.emitted.toList) :=
  scans_forward_chunks (runScans_spec run)

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockAcquireActualSourcePrefixIndices

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual source captures append in source execution order without dropping uncaptured effects. -/
theorem SourceReadCaptures.append {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {first second : List ScanRecord} {before middle after : Clif.Frame × Clif.Mem}
    {left right : List (SunkReadSnapshot ctx env program)}
    (front : SourceReadCaptures ctx env program first before middle left)
    (back : SourceReadCaptures ctx env program second middle after right) :
    SourceReadCaptures ctx env program (first++second) before after (left++right) := by
  induction front with
  | nil state => exact back
  | skipped unmarked source tail ih => exact .skipped unmarked source (ih back)
  | captured marked source read tail ih => exact .captured marked source read (ih back)

/-- Each exact captured read carries its singleton source trace. -/
theorem SunkReadSnapshot.source_capture {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (captured : SunkReadSnapshot ctx env program) :
    SourceReadCaptures ctx env program [captured.record] captured.before captured.after [captured] := by
  exact .captured captured.marked captured.source captured.read (.nil captured.after)

end Backend.Stock.Proof.Acquire810

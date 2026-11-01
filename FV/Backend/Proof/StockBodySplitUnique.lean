import FV.Backend.Proof.StockBodyScanOrigin

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- Two descriptions of the same actual source body have identical records and code. -/
theorem SourceBodySplit.unique {f : Clif.Function} {event : BlockScanEvent} {b : Clif.Block}
    {term otherTerm : ScanRecord} {body otherBody : BlockScan}
    (first : SourceBodySplit f event b term body)
    (second : SourceBodySplit f event b otherTerm otherBody) : term = otherTerm ∧ body = otherBody := by
  obtain ⟨terms,records⟩ := List.cons.inj (first.records.symm.trans second.records)
  have states : body.state = otherBody.state := first.state.trans second.state.symm
  have buffers := congrArg Array.toList (first.code.symm.trans second.code)
  rw [terms] at buffers
  simp only [Array.toList_append] at buffers
  have codes : body.code = otherBody.code := Array.toList_inj.mp (List.append_cancel_right buffers)
  refine ⟨terms,?_⟩
  cases body
  cases otherBody
  cases states
  cases records
  cases codes
  rfl

end Backend.Stock.Proof

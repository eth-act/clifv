import FV.Backend.Proof.StockEmissionCoverage

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program

/-- The existing statement summaries also check integer virtual result shapes
when opportunistic definitions are forbidden. Fixed-program kernel evidence,
not a new compiler or accepted-input check. -/
theorem stock_statement_result_table_checked :
    (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id || r.id == 587 ||
      aRule program covTab aext actor noOpportunityPre aOracle [.xv .inst] (.flat 1 true) r) = true := by
  decide +kernel


end Backend.Stock.Proof.Coverage.Result

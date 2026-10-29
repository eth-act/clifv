module

public import FV.Isle.Generated.Program

@[expose] public section

namespace Backend.Stock.Proof.SinkRules
open Isle Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
/-- Actual term lookup indices agree with stored term identifiers. -/
theorem stock_term_ids_checked :
    program.terms.toList.map Term.id = List.range program.terms.size := by decide +kernel
end Backend.Stock.Proof.SinkRules

import FV.Backend.Proof.IselCovFns

/-! The abstract precondition of the Stock coverage proofs: `apre`, and the opportunistic-def
constructor forbidden. (Its own module, so that its users need not wait for the kernel table
check of `StockNoOpportunityTable`.) -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64

def noOpportunityPre (t : TermId) (args : List AW) : Bool :=
  t != TId.opportunistic_def && apre t args

end Backend.Stock.Proof

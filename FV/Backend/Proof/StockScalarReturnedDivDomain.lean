import FV.Backend.Proof.StockScalarContract
import FV.Backend.Proof.StockLocalSourceExecution
import FV.Backend.Proof.StockPureNotrap
import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.StockHighMulBodyRefines
import FV.Backend.Proof.StockGuardedOmission
import FV.Backend.Proof.StockPureBodyFamilies
import FV.Backend.Proof.StockPureSourceColors
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockBlockScan
import FV.Backend.Proof.StockReturnedDivBodyRefines

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The existing full return-and-trap contract for proved scalar computations before and after
a returned division. Original arguments, memory and slots remain
arbitrary; compiler records and binding facts are derived internally. -/
theorem domain_of_returned_div {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front back : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ stm :: back)
    (before : ∀ item ∈ front,HighMulBody.Family item.inst)
    (after : ∀ item ∈ back,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact DivBody.actual_returned_div_entry_return_refines_frame run scope dominated abi blocks
      shape before after division results ret entered returned refines driver memorySem stable memory arguments
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact DivBody.actual_returned_div_entry_trap_refines_frame run scope dominated blocks
      shape before after division results ret entered trapped refines driver memorySem stable memory arguments

end Backend.Stock.Scalar


import FV.Backend.Proof.StockScalarContract
import FV.Backend.Proof.StockDivReturnRefines
namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- All four division/remainder operations retain arbitrary original input
values, real zero/overflow traps, successful returns and original ABI slots. -/
theorem domain_of_single_div {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {stm : Clif.Stmt} (singleton : b.body = [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact DivBody.actual_single_div_entry_return_refines_frame run scope dominated abi blocks
      singleton division results ret entered returned refines driver memorySem stable memory arguments
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact DivBody.actual_single_div_entry_trap_refines_frame run scope dominated blocks
      singleton division results ret entered trapped refines driver memorySem stable memory arguments

end Backend.Stock.Scalar

import FV.Backend.Proof.StockScalarDivDomain
import FV.Link.ReachCheckEq
set_option autoImplicit false
namespace StockDivPacketReview
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Scalar
/-- The actual arbitrary-input return/trap source domain and the equivalent
executable linker reach predicate are both independent of fixed native witnesses. -/
theorem checked :
    (∀ {f : Clif.Function} (_ : LowerScope f) (_ : Dominated f) (_ : sigAbiOk f.sig = true)
      {b : Clif.Block} (_ : f.blocks = [b]) {stm : Clif.Stmt} (_ : b.body = [stm])
      {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
      (_ : stm.inst = .div op ty x y) (_ : stm.results = [z]) (_ : b.term = .ret [z])
      (_ : (sigRets f.sig).any (·.purpose == .sret) = false), Domain f) ∧
    (∀ P : Link.LinkSpec, P.reachOkMap = P.reachOkB) :=
  ⟨@domain_of_single_div,Link.LinkSpec.reachOkMap_eq⟩
end StockDivPacketReview

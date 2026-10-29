module

public import FV.Backend.Proof.StockScalarContract
public import FV.Backend.Proof.StockMaskBodyRefines

@[expose] public section

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Bmask and general nop compose with every previously supported scalar and
division position under the original return/trap and ABI contracts. -/
theorem domain_of_mask {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact MaskBody.actual_entry_return_refines_frame run scope dominated abi blocks family ret
      entered returned refines driver memorySem stable memory arguments
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact MaskBody.actual_entry_trap_refines_frame run scope dominated blocks family ret
      entered trapped refines driver memorySem stable memory arguments

end Backend.Stock.Scalar

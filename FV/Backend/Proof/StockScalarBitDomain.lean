module

public import FV.Backend.Proof.StockScalarContract
public import FV.Backend.Proof.StockBitReturnRefines
public import FV.Backend.Proof.StockBitFamily

@[expose] public section

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Fixed unary-bit/rotation and earlier scalar source proofs construct the reusable production
contract universally, without checking emitted-code equality against legacy. -/
theorem domain_of_bit {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, BitBody.Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact BitBody.actual_bit_entry_return_refines_frame run scope dominated abi blocks family ret
      entered returned refines driver memorySem stable memory arguments
  · intro result run args cm fr entered env cp fuel code trapped
    obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entered
    have same : b' = b := by
      have equal : some b = some b' := by
        simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
      exact Option.some.inj equal.symm
    subst b'
    have body : fr.body = b.body := by rw [frame]
    have terminal : fr.term = .ret xs := by rw [frame]; exact ret
    have impossible := BitBody.bit_source_notrap fuel ⟨fr,[],cm⟩ rfl
      (fun stm member => family stm (by rwa [body] at member)) terminal code trapped
    cases impossible

end Backend.Stock.Scalar

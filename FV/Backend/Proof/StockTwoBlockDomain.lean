import FV.Backend.Proof.StockTwoBlockReturn
import FV.Backend.Proof.StockTwoBlockTrap
import FV.Backend.Proof.StockTwoBlockCompatibility
import FV.Backend.Proof.StockScalarContract

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The first CFG class satisfies the existing universal production-consumer
contract. Nonempty successor copies are retained and proved equal to the
actual single-successor block field; no legacy lowering verdict is assumed. -/
theorem domain_of_two_block {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    {entry target : Clif.Block} {bc : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,target]) (jump : entry.term = .jump bc) (ret : target.term = .ret xs)
    (destination : bc.block = target.id) (different : entry.id ≠ target.id)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    (quiet : ∀ stm ∈ entry.body,(∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop)
    (forwarded : ∀ stm ∈ entry.body,∀ x ∈ stm.results,x ∈ bc.args) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,source⟩ := TwoBlock.entry_return_frame run scope dominated abi blocks jump ret destination
      different family quiet forwarded entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,source.legacyCompatible (TwoBlock.legacy_compatible run scope blocks jump ret destination different)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,source⟩ := TwoBlock.entry_trap_frame run scope dominated abi blocks jump ret destination
      different family quiet forwarded entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,source.legacyCompatible (TwoBlock.legacy_compatible run scope blocks jump ret destination different)⟩

end Backend.Stock.Scalar

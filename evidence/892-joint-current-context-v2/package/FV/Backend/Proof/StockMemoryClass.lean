import FV.Backend.Proof.StockMemorySingleDomain

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The first production memory class is described entirely by original source
syntax and the original scope/dominance/ABI conditions. No run or output artifact
is part of this predicate. Other previously accepted classes retain fallback. -/
structure SingleClass (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (b : Clif.Block) (x z : Nat) (flags : Clif.MemFlags),
    f.blocks = [b] ∧ b.body = [⟨[z],.load .load .i32 flags x 0⟩] ∧
      b.term = .ret [z] ∧ x ∈ b.params.map (·.1) ∧ flags.trapCode = none

/-- The source class derives the full original-source memory contract. -/
theorem SingleClass.domain {f : Clif.Function} (family : SingleClass f) : Domain f := by
  obtain ⟨b,x,z,flags,blocks,body,ret,parameter,notrap⟩ := family.shape
  exact domain_of_single_load_return family.scope family.dominated family.abi family.ordinary
    blocks body ret parameter notrap

end Backend.Stock.Memory

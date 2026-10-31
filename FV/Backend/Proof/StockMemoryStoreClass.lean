import FV.Backend.Proof.StockMemoryStoreSingleDomain

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The first production memory class is described entirely by original source
syntax and the original scope/dominance/ABI conditions. No run or output artifact
is part of this predicate. Other previously accepted classes retain fallback. -/
structure SingleClass (kind : Kind) (ty : Clif.Ty) (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (b : Clif.Block) (value pointer : Nat) (flags : Clif.MemFlags) (valueTy : Clif.Ty),
    f.blocks = [b] ∧ b.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩] ∧
      b.term = .ret [] ∧ pointer ∈ b.params.map (·.1) ∧ (value,valueTy) ∈ b.params ∧
      (kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) ∧ flags.trapCode = none

/-- The source class derives the full original-source memory contract. -/
theorem SingleClass.domain (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} (family : SingleClass kind ty f) : Domain f := by
  obtain ⟨b,value,pointer,flags,valueTy,blocks,body,ret,parameter,valueParameter,width,notrap⟩ := family.shape
  exact domain_of_single_store_return kind ty family.scope family.dominated family.abi family.ordinary
    blocks body ret parameter valueParameter width notrap

end Backend.Stock.Memory.StoreRoots

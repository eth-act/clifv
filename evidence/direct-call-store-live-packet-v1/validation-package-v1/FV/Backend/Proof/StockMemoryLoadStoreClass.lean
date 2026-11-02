import FV.Backend.Proof.StockMemoryLoadStoreDomain

namespace Backend.Stock.Memory.LoadStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The complete mixed class reads original source and existing admission conditions only. -/
structure SingleClass (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (ty : Clif.Ty)
    (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (b : Clif.Block) (loadPointer storePointer value z : Nat)
    (loadFlags storeFlags : Clif.MemFlags) (valueTy : Clif.Ty),
    f.blocks = [b] ∧
      b.body = [⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩,
        ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩] ∧ b.term = .ret [z] ∧
      loadPointer ∈ b.params.map (·.1) ∧ storePointer ∈ b.params.map (·.1) ∧
      (value,valueTy) ∈ b.params ∧
      (kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) ∧
      loadFlags.trapCode = none ∧ storeFlags.trapCode = none

/-- The original source class supplies the complete memory-capable domain. -/
theorem SingleClass.domain (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (ty : Clif.Ty)
    {f : Clif.Function} (family : SingleClass width kind ty f) : Domain f := by
  obtain ⟨b,loadPointer,storePointer,value,z,loadFlags,storeFlags,valueTy,blocks,body,ret,
    loadParameter,storeParameter,valueParameter,storeWidth,loadNotrap,storeNotrap⟩ := family.shape
  exact domain_of_load_store_return width kind ty family.scope family.dominated family.abi family.ordinary
    blocks body ret loadParameter storeParameter valueParameter storeWidth loadNotrap storeNotrap

end Backend.Stock.Memory.LoadStore

import FV.Backend.Proof.StockMemoryStoreNopTwoBlockDomain

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The CFG class uses original source syntax and the existing ABI conditions. -/
structure CfgClass (kind : Kind) (ty : Clif.Ty) (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (entry target : Clif.Block) (storeIndex value pointer : Nat)
      (flags : Clif.MemFlags) (valueTy : Clif.Ty),
    f.blocks = [entry,target] ∧
      (∀ stm ∈ entry.body,stm.inst = .nop) ∧ entry.term = .jump ⟨target.id,[]⟩ ∧
      target.body[storeIndex]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ ∧
      (∀ j stm,target.body[j]? = some stm → j = storeIndex ∨ stm.inst = .nop) ∧
      target.term = .ret [] ∧ pointer ∈ entry.params.map (·.1) ∧ (value,valueTy) ∈ entry.params ∧
      (kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) ∧ flags.trapCode = none

/-- The original CFG class derives both return and trap obligations. -/
theorem CfgClass.domain (kind : Kind) (ty : Clif.Ty) {f : Clif.Function}
    (family : CfgClass kind ty f) : Domain f := by
  obtain ⟨entry,target,storeIndex,value,pointer,flags,valueTy,blocks,nops,jump,statement,shape,
    ret,parameter,valueParameter,width,notrap⟩ := family.shape
  exact domain_of_two_block_nop_store_return kind ty family.scope family.dominated family.abi
    family.ordinary blocks nops jump statement shape ret parameter valueParameter width notrap

end Backend.Stock.Memory.StoreRoots

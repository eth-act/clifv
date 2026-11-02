import FV.Backend.Proof.StockMemoryCapturedCopyDomain

namespace Backend.Stock.Memory.CapturedCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The complete captured class uses only original source and existing admission conditions. -/
structure CfgClass (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (entry target : Clif.Block) (iv ip is base value pointer : Nat)
      (vf pf sf : Clif.MemFlags),
    f.blocks = [entry,target] ∧
      (∀ stm ∈ entry.body,stm.inst = .nop) ∧ entry.term = .jump ⟨target.id,[]⟩ ∧
      target.body[iv]? = some ⟨[value],.load .load .i64 vf base 8⟩ ∧
      target.body[ip]? = some ⟨[pointer],.load .load .i64 pf base 0⟩ ∧
      target.body[is]? = some ⟨[],.store .store .i64 sf value pointer 0⟩ ∧
      iv < is ∧ ip < is ∧
      (∀ j stm,target.body[j]? = some stm → j = iv ∨ j = ip ∨ j = is ∨ stm.inst = .nop) ∧
      target.term = .ret [] ∧ base ∈ entry.params.map (·.1) ∧
      vf.trapCode = none ∧ pf.trapCode = none ∧ sf.trapCode = none

/-- The original source class derives both complete return and trap obligations. -/
theorem CfgClass.domain {f : Clif.Function} (family : CfgClass f) : Domain f := by
  obtain ⟨entry,target,iv,ip,is,base,value,pointer,vf,pf,sf,blocks,nops,jump,valueStatement,
    pointerStatement,storeStatement,valueEarlier,pointerEarlier,shape,ret,parameter,vn,pn,sn⟩ := family.shape
  exact domain_of_two_block_captured_copy family.scope family.dominated family.abi family.ordinary
    blocks nops jump valueStatement pointerStatement storeStatement valueEarlier pointerEarlier shape ret
    parameter vn pn sn

end Backend.Stock.Memory.CapturedCopy

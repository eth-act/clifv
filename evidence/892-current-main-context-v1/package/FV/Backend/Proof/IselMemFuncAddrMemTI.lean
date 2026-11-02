import FV.Backend.Proof.IselMemFuncAddr
import FV.Backend.Proof.LowerContractT

/-!
# `IselMemFuncAddr` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselMemFuncAddr`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Builders
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}
end Builders
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
set_option maxHeartbeats 2000000 in
/-- **`func_addr`** (`lower.isle:2486`, rule id 1026). -/
theorem func_addr_okTI {p : Program} (hp : Data p) (hpF : FAData p) (hR : Refines F isem) (hMR : MRStable F MR)
    (hM : MemRefinesR Rd F sb syms isem) : MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2486 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_func_ref_data_iff, hpF.t2296, hpF.t2459] at hmatch heval
  have hdat0 := CtxInvT.data hctx _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨fn, rfl, rfl⟩ := inv_funcAddr_root hdat
  simp only [ext_func_ref_data_iff] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, and_true] at *
  isel_destruct; subst_vars
  have hL := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨ms, d, rfl, hsym⟩ := load_ext_name_ok hp ctx hco hR hM (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  subst hs'
  exact ⟨ms, hsym.frag.emitted, _, rfl, (funcAddr_lower_ok hMR hMRo hsym ‹_›).toR⟩

end Backend.Proof

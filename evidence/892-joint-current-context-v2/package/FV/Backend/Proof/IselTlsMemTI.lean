import FV.Backend.Proof.IselTls
import FV.Backend.Proof.LowerContractT

/-!
# `IselTls` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselTls`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Extern
variable (ctx : Ctx) (st : LState)
end Extern
section
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
end
section Builders
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {ctx : Ctx}
end Builders
variable {p : Program} (hp : Data p) {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
set_option maxHeartbeats 2000000 in
include hp in
/-- **`tls_value`** (`lower.isle:3217`, rule id 1129, `tls_model` `elf_gd`). -/
theorem tls_value_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_3217 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_tls_model_iff, ext_symbol_value_data_tls_iff] at hmatch heval
  have hdat0 := CtxInvT.data hctx _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  have := inv_tlsValue_root hdat
  isel_destruct; subst_vars
  repeat (mem_inv_simp [ext_tls_model_iff, ext_symbol_value_data_tls_iff] at * <;> isel_destruct <;>
    subst_vars)
  have hE := ‹ApplyInternal _ _ _ _ 27 647 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hs⟩ := elf_tls_get_addr_ok hp ctx hco (by omega) hE
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  simp only at hs'
  rw [hs] at hs'
  subst hs'
  have hg1 := ‹List.lookup _ ctx.func.globals = some (Clif.GlobalValue.tlsSymbol _ _ _)›
  have hg2 := ‹List.lookup _ f.globals = some (Clif.GlobalValue.tlsSymbol _ 0 _)›
  rw [hctx.func, hg2] at hg1
  cases hg1
  refine ⟨[_], ?_, _, rfl, (tls_lower_ok hMR hM hMRo _ (hctx.func ▸ hg2)).toR⟩
  exact Array.push_eq_append

include hp in
/-- **`tls_value`** with `tls_model` `macho` (rule id 1130): never matches (`tls_model` is
`elf_gd`). -/
theorem tls_value_macho_okTI : MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_3220 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ext_tls_model_iff] at hmatch
  exact absurd ‹2 = VIdx.TlsModel.ElfGd› (by decide)

end Backend.Proof

import FV.Backend.Proof.IselAtomic
import FV.Backend.Proof.IselBaseTI

/-!
# `IselAtomic` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselAtomic`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Helpers
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end Helpers
section Builders
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}
end Builders
section BmaskRun
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {isem : Sem}
end BmaskRun
section BmaskLower
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx}
end BmaskLower
section Bmask
variable {p : Program} (hp : Data p)
end Bmask
section Fence
variable {p : Program} (hp : Data p)
end Fence
section Roots
variable {p : Program} (hp : Data p) {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
set_option maxHeartbeats 2000000 in
include hp in
/-- **`atomic_load`** (`lower.isle:2316`, rule id 983): `ldar`. -/
theorem atomic_load_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2316 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_valid_atomic_transaction_iff] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
  have hRT := hctx.resTys _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨ty, fl, a, rfl, rfl, rfl, hety, hfl⟩ := inv_atomicLoad_root hdat
  repeat (mem_inv_simp [] at * <;> isel_destruct <;> subst_vars)
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hL := ‹ApplyInternal _ _ _ _ 27 422 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨mi, hmi, rfl, hs3⟩ := load_acquire_ok hp hco (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  have := hctx.valueRegI a _ ‹ctx.valueReg? a = some _›; subst this
  simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
    Option.getD_some] at hmi
  rw [ofV_loadAcquire, Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs3 ⊢
  rw [hs3] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, atomicLoad_lower_ok hMR hM hMRo hety hfl (hA64 _ rfl)⟩
  rw [fresh_fst]
  exact (frag_one _ (.loadAcquire _ (.vreg _ .int) (.vreg _ .int) _)
    (by simp [vdefs, operands_loadAcquire, Operand.isDef])).emitted

set_option maxHeartbeats 2000000 in
include hp in
/-- **`atomic_store`** (`lower.isle:2321`, rule id 984): `stlr`. -/
theorem atomic_store_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2321 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_valid_atomic_transaction_iff] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨ty, fl, x, a, rfl, hvs, rfl, hety, hfl⟩ := inv_atomicStore_root hdat
  repeat (mem_inv_simp [ext_valid_atomic_transaction_iff] at * <;> isel_destruct <;> subst_vars)
  have hSR := ‹ApplyInternal _ _ _ _ 46 423 _ _ _ _›
  have hSE := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  obtain ⟨rfl, hs4⟩ := store_release_ok hp hco (by omega) hSR
  obtain ⟨mi, hmi, hs', rfl⟩ := side_effect_inst_ok hp hco (ctx := ctx) (by omega) hSE
  have := hctx.valueRegI x _ ‹ctx.valueReg? x = some _›; subst this
  have := hctx.valueRegI a _ ‹ctx.valueReg? a = some _›; subst this
  rw [ofV_storeRelease, Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs4 ⊢
  rw [hs4] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, (atomicStore_lower_ok hMR hM hMRo hety hfl (hA64 _ rfl) ‹_›).toR⟩
  exact (frag_emit0 _ (.storeRelease _ (.vreg _ .int) (.vreg _ .int) _)
    (by simp [vdefs, operands_storeRelease, Operand.isDef])).emitted

include hp in
/-- **`uextend` of an `atomic_load`** (rule id 810): never matches (`is_sinkable_inst` fails). -/
theorem uextend_atomic_load_okTI : MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_1272 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ctor_is_sinkable_inst] at hmatch

end Roots
syntax "rmw_rootTI" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rmw_rootTI) => `(tactic| (
    intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
    have hctx : CtxInvT f ctx := hctxT.inv
    have hops := hctx.intOps ii info inst hi hic
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
    mem_inv hp [ext_valid_atomic_transaction_iff] at hmatch heval
    have hdat0 := hctx.data _ _ _ hi hic
    have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
    have hRT := hctx.resTys _ _ _ hi hic
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := data_trans hdat0 ‹_›
    obtain ⟨cop, ty, fl, a, x, nm, rfl, hvs, rfl, hnm, hk, hety, hfl⟩ := inv_atomicRmw_root hdat
    cases cop <;> simp only [rmwOpName, Option.some.injEq] at hnm <;> subst hnm <;>
      (try (exact absurd hk (by decide)))
    repeat (mem_inv_simp [ext_value_array_2_iff] at * <;> isel_destruct <;> subst_vars)
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hL := ‹ApplyInternal _ _ _ _ 27 612 _ _ _ _›
    have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    obtain ⟨mi, hmi, rfl, hs3⟩ := atomic_rmw_loop_ok hp hco (by omega) hL
    obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
    have := hctx.valueRegI a _ ‹ctx.valueReg? a = some _›; subst this
    have := hctx.valueRegI x _ ‹ctx.valueReg? x = some _›; subst this
    simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
      Option.getD_some] at hmi
    obtain rfl := Option.some.inj (hmi.symm.trans rfl)
    simp only at hs' hs3 ⊢
    rw [hs3] at hs'
    subst hs'
    refine ⟨_, ?_, _, rfl, atomicRmw_lower_ok hMR hM hMRo (by rfl) hety hfl (hA64 _ rfl)⟩
    simp only [LState.fresh]
    exact (frag_fresh3 _ (.atomicRmwLoop _ _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int)
      (.vreg _ .int) (.vreg _ .int)) (by simp [vdefs, operands_rmwLoop, Operand.isDef])).emitted))

section LoopRoots
variable {p : Program} (hp : Data p) {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `add`** (`lower.isle:2357`). -/
theorem atomic_rmw_add_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2357 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `sub`** (`lower.isle:2359`). -/
theorem atomic_rmw_sub_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2359 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `and`** (`lower.isle:2361`). -/
theorem atomic_rmw_and_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2361 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `nand`** (`lower.isle:2363`). -/
theorem atomic_rmw_nand_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2363 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `or`** (`lower.isle:2365`). -/
theorem atomic_rmw_or_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2365 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `xor`** (`lower.isle:2367`). -/
theorem atomic_rmw_xor_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2367 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `smin`** (`lower.isle:2369`). -/
theorem atomic_rmw_smin_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2369 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `smax`** (`lower.isle:2371`). -/
theorem atomic_rmw_smax_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2371 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `umin`** (`lower.isle:2373`). -/
theorem atomic_rmw_umin_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2373 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `umax`** (`lower.isle:2375`). -/
theorem atomic_rmw_umax_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2375 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `xchg`** (`lower.isle:2377`). -/
theorem atomic_rmw_xchg_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2377 := by
  rmw_rootTI

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_cas`** (`lower.isle:2390`, rule id 1007): `AtomicCASLoop`. -/
theorem atomic_cas_okTI (hMR : MRStable F MR) (hM : MemRefinesR Rd F sb syms isem) :
    MemRuleOkRTX Rd F sb syms isem MR env cp p rule_lower_2390 := by
  intro f ctx hctxT hMRo ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_valid_atomic_transaction_iff, matchPat_and_single] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
  have hRT := hctx.resTys _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨ty, fl, a, e, x, rfl, hvs, rfl, hety, hfl⟩ := inv_atomicCas_root hdat
  repeat (mem_inv_simp [ext_value_array_3_iff] at * <;> isel_destruct <;> subst_vars)
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hL := ‹ApplyInternal _ _ _ _ 27 613 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨mi, hmi, rfl, hs3⟩ := atomic_cas_loop_ok hp hco (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  have := hctx.valueRegI a _ ‹ctx.valueReg? a = some _›; subst this
  have := hctx.valueRegI e _ ‹ctx.valueReg? e = some _›; subst this
  have := hctx.valueRegI x _ ‹ctx.valueReg? x = some _›; subst this
  simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
    Option.getD_some] at hmi
  rw [ofV_casLoop, Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs3 ⊢
  rw [hs3] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, atomicCas_lower_ok hMR hM hMRo hety hfl (hA64 _ rfl)⟩
  simp only [LState.fresh]
  exact (frag_fresh2 _ (.atomicCasLoop _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int)
    (.vreg _ .int) (.vreg _ .int)) (by simp [vdefs, operands_casLoop, Operand.isDef])).emitted

end LoopRoots
end Backend.Proof

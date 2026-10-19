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
set_option maxHeartbeats 4000000 in
include hp in
/-- **`bmask`** (`lower.isle:2052`): `cmp #0` (an 8/16-bit value masked first), `csetm ne`. -/
theorem bmask_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2052 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  mem_inv hp [ctor_put_in_regs_iff] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hRT := hctx.resTys _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [atom_vn_Unary] at hf
  rw [atom_vn_Bmask] at ho
  obtain ⟨ty, x, rfl⟩ :=
    instNames_bmask (Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm)
  obtain ⟨hety, hfs⟩ := instData_bmask hdat
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (mem_inv_simp [ctor_put_in_regs_iff] at * <;> isel_destruct <;> subst_vars)
  simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
    Option.getD_some, ofClif_int_width (isInt_of_eTy hety)] at *
  have := hctx.valueRegI x _ ‹ctx.valueReg? x = some _›; subst this
  have hvt := ‹ctx.valueType? x = some _›
  have hE := hctx.valTyEI x _ hvt
  simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at hE
  have hw := eTy_width hety
  have hcall := ‹ApplyInternal _ _ _ _ 22 658 _ _ _ _›
  have hout := ‹externCtor ctx T.output _ _ = _›
  rcases hE with rfl | rfl | rfl | rfl
  · obtain ⟨rfl, hs⟩ := lower_bmask_816_ok hp hco (by omega) hw (.inl rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push3], _, rfl,
      bmask_lower_816 hR hMR hety (.inl rfl) hvt⟩
  · obtain ⟨rfl, hs⟩ := lower_bmask_816_ok hp hco (by omega) hw (.inr rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push3], _, rfl,
      bmask_lower_816 hR hMR hety (.inr rfl) hvt⟩
  · obtain ⟨rfl, hs⟩ := lower_bmask_3264_ok hp hco (by omega) hw (.inl rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push2], _, rfl,
      bmask_lower_3264 hR hMR hety (.inl rfl) hvt⟩
  · obtain ⟨rfl, hs⟩ := lower_bmask_3264_ok hp hco (by omega) hw (.inr rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push2], _, rfl,
      bmask_lower_3264 hR hMR hety (.inr rfl) hvt⟩

end Bmask
section Fence
variable {p : Program} (hp : Data p)
set_option maxHeartbeats 2000000 in
include hp in
/-- **`fence`** (`lower.isle:2476`): `dmb ish`, no effect in the single-threaded model. -/
theorem fence_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2476 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  obtain ⟨tys, htys, -, hlen⟩ := hctx.resTys _ _ _ hi hic
  mem_inv hp [] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [atom_vn_NullAry] at hf
  rw [atom_vn_Fence] at ho
  have := instNames_fence (Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm)
  subst this
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hF := ‹ApplyInternal _ _ _ _ 46 466 _ _ _ _›
  have hSE := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  obtain ⟨rfl, hs4⟩ := fence_helper_ok hp hco (by omega) hF
  obtain ⟨mi, hmi, hs', rfl⟩ := side_effect_inst_ok hp hco (ctx := ctx) (by omega) hSE
  have hmi' : MInst.ofV (.data 58 44 []) = some .fence := rfl
  rw [hmi', Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs4
  rw [hs4] at hs'
  subst hs'
  have hres := List.eq_nil_of_length_eq_zero hlen
  have hfr := frag_emit0 st .fence rfl
  refine ⟨[.fence], hfr.emitted, [], rfl, ⟨hfr.mono, hfr.defs, ?_⟩⟩
  intro fr cm ρ w _ _ _ hmr
  have ho : instOutcome env cp fr cm .fence = .ok ([], cm) := rfl
  rw [ho]
  obtain ⟨w'', hs, hsw⟩ := hR .fence [] w [] w (ctl := .next) rfl
  refine ⟨fun m hm u hu => ?_, _, w'', seqRun_isem_one (ops := #[]) rfl hs rfl, .inl hres,
    hMR _ _ _ _ hsw.toNF hmr⟩
  simp only [List.mem_singleton] at hm
  subst hm
  simp [show vuseNums MInst.fence = [] from rfl] at hu

end Fence
section Roots
variable {p : Program} (hp : Data p) {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
end Roots
section LoopRoots
variable {p : Program} (hp : Data p) {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
end LoopRoots
end Backend.Proof

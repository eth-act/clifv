import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselCmpEmitTI

/-!
# `IselCmpDiv` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpDiv`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`put_nonzero_in_reg`** (`lower.isle:1097–1110`): a nonzero `iconst` divisor as an
immediate (`imm`, no check), or the divisor in a register (64-bit: as is; narrower: extended to
32 bits) followed by `trapIf (zero r) int_divz`. `e`: `ImmExtend` (0 sign, 1 zero). -/
theorem put_nonzero_in_reg_okTI {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem)
    {f : Clif.Function} (hctx : CtxInvT f ctx) {n : Nat} (hn : 100 ≤ n) {y e w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (he : e = 0 ∨ e = 1) {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 698 [.value y, .data 125 e [], .ty (.int w)] s v s') :
    (∃ j info ity imm, ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
        info.clif = some (.iconst ity imm) ∧ eTy ity = true ∧ imm64OfIconst ity imm ≠ 0 ∧
        ImmOut F isem w e (u64 (imm64OfIconst ity imm)) s.1 s'.1 v) ∨
    (w = 64 ∧ ∃ ry, ctx.valueReg? y = some ry ∧ v = .reg ry ∧
        s'.1 = s.1.emit (.trapIf (.zero ry .size64) .intDivz)) ∨
    (w ≤ 32 ∧ ∃ r s2, ExtOut ctx y (e == 0) 32 [.int 32, .int 64] s.1 s2 (.reg r) ∧ v = .reg r ∧
        s'.1 = s2.emit (.trapIf (.zero r .size32) .intDivz)) := by
  rcases hw with rfl | rfl | rfl | rfl <;> rcases he with rfl | rfl <;>
  isel_split' hp hc h 698 <;>
  (try (isel_refute hp at hm; done))
  all_goals isel_inv' hp [] at hm he
  all_goals try (obtain ⟨hx⟩ : Nonempty (CTy.int _ = CTy.int 64) := ⟨‹_›⟩; cases hx; done)
  all_goals try (have hx : (CTy.int 64).bits ≤ 32 := by assumption
                 exact absurd hx (by decide))
  -- `iconst` divisor: `imm`
  all_goals try (
    obtain ⟨hnz⟩ : Nonempty (externExtract ctx T.nonzero_u64_from_imm64 _ _ = _) := ⟨‹_›⟩
    obtain ⟨hj⟩ : Nonempty (ctx.defInst? y = some _) := ⟨‹_›⟩
    obtain ⟨hi⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
    obtain ⟨hd⟩ : Nonempty (V.data 152 35 _ = _) := ⟨‹_›⟩
    obtain ⟨h553⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 553 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨ity, imm, rfl, hety, hcl⟩ := iconst_data_invTI hctx hj hi hd
    rw [ext_nonzero_u64_iff] at hnz
    obtain ⟨hne, hfs⟩ := hnz
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    have hI := imm_ok_ai hp hc hR (by decide) (by decide) (by omega) h553
    rw [u64_ofNat (u64_lt' _)] at hI
    exact .inl ⟨_, hj, _, hi, _, _, hcl, hety, hne, hI⟩)
  all_goals
    obtain ⟨h559⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 559 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨h305⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 93 305 _ _ _ _) := ⟨‹_›⟩
    obtain ⟨hs5, hsz⟩ := operand_size_ok hp hc (by omega) h305
    rcases hsz with ⟨hb, rfl⟩ | ⟨hb, -, rfl⟩ <;> (try (exact absurd hb (by decide)))
  -- 64-bit divisor register
  all_goals try (
    obtain ⟨hr, hs'⟩ := trap_if_zero_divisor_ok hp hc (h := h559) (hn := by omega) (hi := rfl)
    subst hr
    simp only at hs' hs5
    rw [hs5] at hs'
    exact .inr (.inl ⟨_, by assumption, rfl, hs'⟩))
  -- 64-bit divisor register
  -- narrower divisor: extended to 32 bits
  all_goals
    first
      | obtain ⟨h55⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 555 _ _ _ _) := ⟨‹_›⟩
        have hE := sext32_ok hp hc (hn := by omega) h55
      | obtain ⟨h55⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 556 _ _ _ _) := ⟨‹_›⟩
        have hE := zext32_ok hp hc (hn := by omega) h55
    obtain ⟨r, rfl⟩ := hE.isReg
    obtain ⟨hr, hs'⟩ := trap_if_zero_divisor_ok hp hc (h := h559) (hn := by omega) (hi := rfl)
    subst hr
    simp only at hs'
    rw [hs5] at hs'
    exact .inr (.inr ⟨r, _, hE, rfl, hs'⟩)

end
/-- **Semantic contract of `put_nonzero_in_reg`**: the returned vreg `k` holds the divisor as a
division operand, after a check that halts with `int_divz` on a zero divisor. -/
theorem divisor_semTI {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInvT f ctx) {y e w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (he : e = 0 ∨ e = 1) {s s' : LState} {v : V} (hvb : ValsBelow ctx s)
    (hD : (∃ j info ity imm, ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
        info.clif = some (.iconst ity imm) ∧ eTy ity = true ∧ imm64OfIconst ity imm ≠ 0 ∧
        ImmOut F isem w e (u64 (imm64OfIconst ity imm)) s s' v) ∨
      (w = 64 ∧ ∃ ry, ctx.valueReg? y = some ry ∧ v = .reg ry ∧
        s' = s.emit (.trapIf (.zero ry .size64) .intDivz)) ∨
      (w ≤ 32 ∧ ∃ r s2, ExtOut ctx y (e == 0) 32 [.int 32, .int 64] s s2 (.reg r) ∧ v = .reg r ∧
        s' = s2.emit (.trapIf (.zero r .size32) .intDivz)))
    (hyI : IntPos ctx y := by int_posA) :
    ∃ k ms, v = .reg (.vreg k .int) ∧ Frag s s' ms ∧ (s.nextVreg ≤ k ∨ k = y) ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (ty : Clif.Ty) (b : BitVec ty.width), ty.width = w →
        ((∃ r, ctx.valueReg? y = some r) → VHolds ⟨ty, b⟩ (ρ y)) → DFGCons ctx fr →
        fr.regs y = some ⟨ty, b⟩ →
        UsesLo s.nextVreg fr ms ∧ ∀ wd, k < s'.nextVreg ∧
          (b = 0#ty.width → TrapRun isem ms ρ wd .intDivz) ∧
          (b ≠ 0#ty.width → Runs F isem ms ρ wd (fun ρ' _ => DivOpnd (e == 0) b (ρ' k))) := by
  rcases hD with ⟨j, info, ity, imm, hj, hi, hcl, hety, hne, hI⟩ | ⟨rfl, ry, hry, rfl, rfl⟩ |
    ⟨hw32, r, s2, hE, rfl, rfl⟩
  · -- `iconst`: `imm`, no check
    obtain ⟨ms, d, rfl, hsh, hrun⟩ := hI
    refine ⟨d, ms, rfl, ⟨hsh.emitted, hsh.mono, hsh.defs⟩, .inl hsh.res,
      fun fr ρ ty b htw hh hdf hyv => ⟨?_, fun wd => ?_⟩⟩
    · intro m hm u hu
      rcases hsh.uses m hm u hu with h | h
      · exact .inl h
      · exact .inl (by omega)
    have hv := iconst_val hdf hj hi hcl hyv
    simp only [Clif.Val.mk.injEq] at hv
    obtain ⟨rfl, hb⟩ := hv
    have hb' : b = imm := eq_of_heq hb
    subst hb'
    have hw64 := eTy_width hety
    obtain ⟨d', ms', he', hsh', hlt, hrun'⟩ := immOut_lt (by omega) (by omega) wd ⟨ms, d, rfl, hsh, hrun⟩
    cases he'
    refine ⟨hlt, fun h0 => absurd h0 (imm64OfIconst_ne_zero hne), fun _ => ?_⟩
    obtain ⟨ρ', X, hp, hX, hXc, hXv⟩ := hrun ρ
    refine prun_runs hp wd fun _ => ?_
    rw [u64_imm64OfIconst hw64] at hXc hXv
    subst htw
    exact imm_divOpnd hw he b hXc hXv hX
  · -- 64-bit register, `trapIf (zero y)`
    have hry' := hctx.valueRegI y ry hry
    subst hry'
    have hylt := hvb y _ hry
    refine ⟨y, _, rfl, Frag.emit_nodef s (vdefs_trapIf_zero _ _ _), .inr rfl,
      fun fr ρ ty b htw hh hdf hyv => ⟨?_, fun wd => ⟨by simpa [LState.emit] using hylt, ?_⟩⟩⟩
    · intro m hm u hu
      simp only [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_trapIf_zero, List.mem_singleton] at hu
      subst hu
      exact .inr (by simp [hyv])
    have hd : DivOpnd (e == 0) b (ρ y) := by
      have hv := hh ⟨_, hry⟩
      cases ty <;> simp [Clif.Ty.width] at htw <;>
      · simp only [VHolds, Clif.Ty.width] at hv
        unfold DivOpnd
        simp only [Clif.Ty.width, show ¬ (64 : Nat) ≤ 32 by decide, ↓reduceIte, lo64,
          BitVec.setWidth_eq]
        exact hv
    have hz := hd.zero_iff (by omega) wd (.vreg y .int)
    rw [show szOf ty.width = .size64 by rw [htw]; rfl] at hz
    refine ⟨fun h0 => trapRun_trapIf_zero hR _ _ _ ρ wd (by rw [hz, h0]; simp), fun h0 => ?_⟩
    refine (runs_trapIf_zero_fall hR _ _ _ ρ wd (by rw [hz]; simpa using h0)).imp fun ρ' _ _ e => ?_
    rw [e]; exact hd
  · -- extended to 32 bits, `trapIf (zero r)`
    obtain ⟨k, ms, hkr, hf, hklt, hk, hsem⟩ := ExtOut.semT hR hctx (hxi := by int_posA) hvb (.inl rfl)
      (by intro t ht; simp at ht; rcases ht with rfl | rfl <;> simp) (fun _ => by simp) hE
    cases hkr
    refine ⟨k, ms ++ [.trapIf (.zero (.vreg k .int) .size32) .intDivz], rfl,
      hf.append (Frag.emit_nodef s2 (vdefs_trapIf_zero _ _ _)), hk,
      fun fr ρ ty b htw hh hdf hyv => ?_⟩
    obtain ⟨hu, hrun⟩ := hsem fr ρ _ (hh (by obtain ⟨t, -, rx, hx, -⟩ := hE; exact ⟨rx, hx⟩)) hdf hyv
    refine ⟨UsesLo.append hu ?_, fun wd => ⟨by simpa [LState.emit] using hklt, ?_⟩⟩
    · intro m hm u hu'
      simp only [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_trapIf_zero, List.mem_singleton] at hu'
      subst hu'
      rcases hk with h | rfl
      · exact .inl h
      · exact .inr (by simp [hyv])
    have hd : ∀ a, ExtHolds (e == 0) 32 ⟨ty, b⟩ a → DivOpnd (e == 0) b a := by
      intro a ha
      unfold DivOpnd
      simp only [show ty.width ≤ 32 by omega, ↓reduceIte]
      exact ha.2 (by simp; omega)
    have hsz : szOf ty.width = .size32 := by simp [szOf, show ty.width ≤ 32 by omega]
    refine ⟨fun h0 => TrapRun.prefix (hrun wd) fun ρ1 w1 h1 => ?_, fun h0 => ?_⟩
    · have hz := (hd _ h1).zero_iff (by omega) w1 (.vreg k .int)
      rw [hsz] at hz
      exact trapRun_trapIf_zero hR _ _ _ ρ1 w1 (by rw [hz, h0]; simp)
    · refine Runs.append (hrun wd) fun ρ1 w1 h1 => ?_
      have hz := (hd _ h1).zero_iff (by omega) w1 (.vreg k .int)
      rw [hsz] at hz
      refine (runs_trapIf_zero_fall hR _ _ _ ρ1 w1 (by rw [hz]; simpa using h0)).imp fun ρ' _ _ e => ?_
      rw [e]; exact hd _ h1

end Backend.Proof

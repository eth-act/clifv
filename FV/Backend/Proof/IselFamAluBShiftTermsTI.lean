import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselTermsShiftTI

/-!
# `IselFamAluBShiftTerms` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBShiftTerms`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
section Ctor
variable (ctx : Ctx) (st : LState)
end Ctor
section Sem
variable {F : BitVec 64 → Prop} {isem : Sem}
set_option maxHeartbeats 1000000 in
include hp hc in
/-- **Contract of `do_shift`** (all four rules). -/
theorem do_shift_okTI (hR : Refines F isem) {f : Clif.Function} (hctx : CtxInvT f ctx) {n : Nat}
    (hn : 80 ≤ n) {k w : Nat} {op : ALUOp} (hk : ShiftOp k op) (hw : IW w) {xa y : Nat}
    {s s' : LState × Array RuleId} {v : V} (hxa : xa < s.1.nextVreg)
    (h : ApplyInternal p (sem ctx) cfg n 27 703
      [.data 59 k [], .ty (.int w), .reg (.vreg xa .int), .value y] s v s')
    (hyI : IntPos ctx y := by int_posA) :
    ShiftRes F isem ctx op w xa y s.1 s'.1 v := by
  have hp' := hp
  isel_split hp hc h 703
  · fb_inv [*, rule_lower_1631] at hm he
    have hdata := ‹V.data 152 35 _ = _›
    have hdj := ‹ctx.defInst? y = some _›
    have hij := ‹ctx.insts[_]? = some _›
    obtain ⟨ty, imm, hcl, hfs⟩ := defInst_iconst_clifTI ctx hctx hdj hij hdata.symm
    have hety : eTy ty = true := by
      have hdat := hctx.data _ _ _ hij hcl
      rw [← hdata] at hdat
      exact (fb_instData_iconst hdat).1
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
      ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
    have hA := ‹ApplyInternal _ _ _ _ 27 361 _ _ _ _›
    obtain ⟨ks, hks, rfl, m, hm', hs'⟩ := alu_rr_imm_shift_ok hp' hc (by omega) hA
    dsimp only at hm' hs'
    rw [ofV_aluRRImmShift_fb _ _ hk.ofIdx (hks.ofIdx hw)] at hm'
    cases hm'
    rw [hs']
    exact shiftRes_imm hR hk.isShift hw hdj hij hcl hety _
  · fb_inv [*, rule_lower_1622] at hm he
    have hwe := ‹CTy.int w = CTy.int 32›
    simp only [CTy.int.injEq] at hwe
    subst hwe
    have hry := ‹ctx.valueReg? y = some _›
    have hg := ‹[_][Int.toNat 0]? = some _›
    simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    obtain rfl := hctx.valueRegI y _ hry
    have hA := ‹ApplyInternal _ _ _ _ 27 362 _ _ _ _›
    obtain ⟨ks, hks, rfl, m, hm', hs'⟩ := alu_rrr_ok hp' hc (by omega) hA
    dsimp only at hm' hs'
    rw [ofV_aluRRR hk.ofIdx (hks.ofIdx hw)] at hm'
    cases hm'
    rw [hs']
    exact shiftRes_rrr hR hk.isShift (by simp) hry _
  · fb_inv [*, rule_lower_1623] at hm he
    have hwe := ‹CTy.int w = CTy.int 64›
    simp only [CTy.int.injEq] at hwe
    subst hwe
    have hry := ‹ctx.valueReg? y = some _›
    have hg := ‹[_][Int.toNat 0]? = some _›
    simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    obtain rfl := hctx.valueRegI y _ hry
    have hA := ‹ApplyInternal _ _ _ _ 27 362 _ _ _ _›
    obtain ⟨ks, hks, rfl, m, hm', hs'⟩ := alu_rrr_ok hp' hc (by omega) hA
    dsimp only at hm' hs'
    rw [ofV_aluRRR hk.ofIdx (hks.ofIdx hw)] at hm'
    cases hm'
    rw [hs']
    exact shiftRes_rrr hR hk.isShift (by simp) hry _
  · fb_inv [*, rule_lower_1612] at hm he
    have h16 := ‹(CTy.int w).bits ≤ 16›
    have hry := ‹ctx.valueReg? y = some _›
    have hg := ‹[_][Int.toNat 0]? = some _›
    simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    obtain rfl := hctx.valueRegI y _ hry
    have hmask := ‹externCtor ctx T.shift_mask _ _ = _›
    have hA := ‹ApplyInternal _ _ _ _ 27 502 _ _ _ _›
    have hB := ‹ApplyInternal _ _ _ _ 27 362 _ _ _ _›
    have h32 : IW 32 := by simp [IW]
    rcases hw with rfl | rfl | rfl | rfl
    rotate_left 2
    · simp [CTy.bits] at h16
    · simp [CTy.bits] at h16
    all_goals first
      | (rw [ctor_shift_mask_i8_iff] at hmask) | (rw [ctor_shift_mask_i16_iff] at hmask)
    all_goals
      obtain ⟨rfl, rfl⟩ := hmask
      obtain ⟨ks1, hks1, rfl, m1, hm1, hs1⟩ := and_imm_ok hp' hc (by omega) hA
      dsimp only at hm1 hs1
      rw [ofV_aluRRImmLogic_fb _ _ (rfl : ALUOp.ofIdx? 4 = some .and) (hks1.ofIdx h32)] at hm1
      cases hm1
      obtain ⟨ks2, hks2, rfl, m2, hm2, hs2⟩ := alu_rrr_ok hp' hc (by omega) hB
      dsimp only at hm2 hs2
      rw [ofV_aluRRR hk.ofIdx (hks2.ofIdx h32)] at hm2
      cases hm2
      rw [hs2, hs1]
      exact shiftRes_mask hR hk.isShift (by simp) hry _ hxa rfl

end Sem
end Backend.Proof

import FV.Backend.Proof.IselTermsImm

/-!
# Family B: `iconst` (`lower.isle:53`): `(imm ty (ImmExtend.Zero) n)`

The instruction is `iconst.ty imm` (`UnaryImm`/`Iconst` data, `imm64OfIconst`); the right-hand
side is `output_reg` of `imm`, whose contract (`imm_ok`) gives the emitted code and a 64-bit
value whose low `ty.width` bits are the constant's.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxRecDepth 20000 in
theorem fb_variantNames_UnaryImm : (variantNames 152)[35]? = some "UnaryImm" := rfl
set_option maxRecDepth 20000 in
theorem fb_variantNames_Iconst : (variantNames 151)[57]? = some "Iconst" := rfl

theorem fb_instNames_iconst {c : Clif.Inst} (h : instNames c = ("UnaryImm", "Iconst")) :
    ∃ ty imm, c = .iconst ty imm := by
  cases c <;> simp [instNames] at h ⊢

theorem fb_instData_iconst {f : Clif.Function} {ty : Clif.Ty} {imm : BitVec ty.width}
    {k k' : Nat} {fs : List V}
    (h : instData f (.iconst ty imm) = .ok (.data 152 k (.data 151 k' [] :: fs))) :
    eTy ty = true ∧ fs = [.int (imm64OfIconst ty imm)] := by
  simp only [instData] at h
  split at h
  · rename_i he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    injection h3 with _ h4
    exact ⟨he, h4⟩
  · cases h

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_53 {i : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info) {w : Nat}
    (hty : info.resTys.head? = some (.int w)) {k : Int}
    (hd : info.data = .data 152 35 [.data 151 57 [], .int k]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_53 [.inst i]).run (st, tr) =
      .ok (some (env2 (.ty (.int w)) (.int (u64 k))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_u64_from_imm64 ctx st k
  cases hp
  isel_eval [*, rule_lower_53]

include hp hc in
theorem rhs_53_inv {w : Nat} {c : Int} {out : V} {s' : LState × Array RuleId}
    (h : (evalExpr p (sem ctx) cfg (n+50) rule_lower_53.rhs (env2 (.ty (.int w)) (.int c))).run
      (st, tr) = .ok (some out, s')) :
    ∃ v s2, (applyTerm p (sem ctx) cfg (n+47) 27 553 (immArgs w 1 c)).run (st, tr) =
        .ok (some v, s2) ∧ ∀ r, v = .reg r → out = .regsVec [[r]] ∧ s'.1 = s2.1 := by
  revert h
  have ho := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hA : (applyTerm p (sem ctx) cfg (n+47) 27 553 (immArgs w 1 c)).run (st, tr) with
  | error e =>
    cases hp
    isel_eval [*, rule_lower_53]
    exact fun h => by cases h
  | ok q =>
    obtain ⟨ov, s2⟩ := q
    cases ov with
    | none =>
      cases hp
      isel_eval [*, rule_lower_53]
      exact fun h => by cases h
    | some v =>
      intro h
      refine ⟨v, s2, rfl, fun r hr => ?_⟩
      subst hr
      obtain ⟨st2, tr2⟩ := s2
      revert h
      cases hp
      isel_eval [*, rule_lower_53]
      intro h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl⟩

end

theorem fb_u64_imm64 {ty : Clif.Ty} (hw : ty.width ≤ 64) (imm : BitVec ty.width) :
    u64 (imm64OfIconst ty imm) = imm.toNat := by
  have hlt := imm.isLt
  have hp64 : 2 ^ ty.width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  unfold imm64OfIconst u64
  split
  · omega
  · have h64 : ty.width = 64 := by omega
    have hp : 2 ^ ty.width = 2 ^ 64 := by rw [h64]
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega

theorem fb_u64_nat {k : Nat} (h : k < 2 ^ 64) : u64 (k : Int) = k := by unfold u64; omega

theorem eTy_widths {ty : Clif.Ty} (h : eTy ty = true) :
    ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
  cases ty <;> simp [eTy, Clif.Ty.width] at h ⊢

/-- The low `w` bits of a register whose low 64 bits are `X`. -/
theorem vholds_of_lo64 {ty : Clif.Ty} (hw : ty.width ≤ 64) {x : CV} {X : Nat}
    {imm : BitVec ty.width} (hx : lo64 x = BitVec.ofNat 64 X) (hX : X % 2 ^ ty.width = imm.toNat) :
    VHolds ⟨ty, imm⟩ x := by
  simp only [VHolds]
  have : x.setWidth ty.width = (lo64 x).setWidth ty.width := by
    simp only [lo64, BitVec.setWidth_setWidth_of_le _ hw]
  rw [this, hx]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hw), hX]

include hp in
/-- **`iconst`** (`lower.isle:53`), i8..i64: the `imm` sequence. -/
theorem iconst_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_53 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 50 := ⟨n - 50, by omega⟩
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx (r := rule_lower_53) rfl hp.t2482
    term_2482_kind hp.t2341 term_2341_kind (m := m' + 1) hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [fb_variantNames_UnaryImm] at hf
  rw [fb_variantNames_Iconst] at ho
  have hnm : instNames inst = ("UnaryImm", "Iconst") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, imm, rfl⟩ := fb_instNames_iconst hnm
  obtain ⟨hety, rfl⟩ := fb_instData_iconst hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by rw [hres]; simp [ofClif_int_width]
  have hw := eTy_width hety
  rw [match_53 hp ctx st tr m' hi hhead hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨v, s2, hA, hout⟩ := rhs_53_inv hp ctx hco st tr n' heval
  obtain ⟨ms, d, rfl, hsh, hrun⟩ :=
    imm_ok hp ctx hco hR (eTy_widths hety) (.inr rfl) (n := n' + 7) hA
  obtain ⟨rfl, hs'⟩ := hout _ rfl
  simp only at hs'
  subst hs'
  refine ⟨ms, _, hsh.emitted, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ _ _ ho
  simp only [instOutcome, Clif.evalInst, pure, Except.pure] at ho
  cases ho
  obtain ⟨ρ', X, hp', hx, hX, -⟩ := hrun ρ
  refine ⟨rfl, usesOk_of [] ?_ (by simp), .inl hsh.res, _, ρ', rfl, hp', ?_⟩
  · intro mi hmi u hu
    rcases hsh.uses mi hmi u hu with h | h
    · exact .inl h
    · exact .inl (by omega)
  · refine vholds_of_lo64 hw hx ?_
    have hp64 : 2 ^ ty.width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
    rw [hX, fb_u64_imm64 hw, fb_u64_nat (by have := imm.isLt; omega), Nat.mod_eq_of_lt imm.isLt]

end Backend.Proof

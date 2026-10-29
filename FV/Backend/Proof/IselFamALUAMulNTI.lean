module

public import FV.Backend.Proof.IselFamALUAMulN
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselTermsALUAMulNTI
public import FV.Backend.Proof.IselFamALUATI

@[expose] public section

/-!
# `IselFamALUAMulN` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamALUAMulN`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
section LetInv
variable {p : Program} {σ : Type} {sem' : Isle.Sem V σ} {cfg : Config}
end LetInv
set_option maxRecDepth 20000 in
/-- **`smulhi_fits_in_32`** (`lower.isle:1059`, `smulhi` at i8/i16/i32 → `sxt`, `sxt`, `madd`, `asr`). -/
theorem smulhi_fits_in_32_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1059 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, -, -, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .smulhi) rfl hp.t2363 term_2363_kind
      variantNames_Smulhi rfl hmatch
  cases Classical.em (ty.width ≤ 32) with
  | inr hnw => rw [match_1059_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  rw [match_1059 hp ctx st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨envB, sB, hbinds, -⟩ := evalExpr_let_inv (n := N + 99) heval
  obtain ⟨v1, sx, hv1, -, hbinds'⟩ := evalBinds_cons_inv hbinds
  obtain ⟨v2, sy, hv2, -, -⟩ := evalBinds_cons_inv hbinds'
  obtain ⟨vs1, sa, ha1, happ1⟩ := evalExpr_term_inv hv1
  rw [evalArgs_var1 (n := N + 95) (v := .value x) (by simp)] at ha1
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha1
  obtain ⟨rfl, rfl⟩ := ha1
  obtain ⟨sxs, sxt⟩ := sx
  obtain ⟨t1, hvt1, hrx, hc1⟩ := sext64_invTI hp ctx hco hctx st tr (N + 37) happ1
  have hxb : x < st.nextVreg := hvb x _ hrx
  obtain ⟨r1, ms1, rfl, P1⟩ := partOk_of (F := F) (isem := isem) hR hxb hvt1 hc1
  obtain ⟨vs2, sb, ha2, happ2⟩ := evalExpr_term_inv hv2
  rw [evalArgs_var1 (n := N + 94) (v := .value y) (by simp)] at ha2
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha2
  obtain ⟨rfl, rfl⟩ := ha2
  obtain ⟨sys, syt⟩ := sy
  obtain ⟨t2, hvt2, hry, hc2⟩ := sext64_invTI hp ctx hco hctx sxs sxt (N + 36) happ2
  have hyb : y < st.nextVreg := hvb y _ hry
  obtain ⟨r2, ms2, rfl, P2⟩ := partOk_of (F := F) (isem := isem) hR
    (Nat.lt_of_lt_of_le hyb P1.1) hvt2 hc2
  obtain ⟨tr'', he⟩ := rhs_1059 hp ctx hco st tr N hw happ1 happ2
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  simp only [fresh_fst]
  refine ⟨ms1 ++ ms2 ++ [_, _], _, ?_, rfl,
    mulhiN_lowerInstOk hR hMR (cop := .smulhi) rfl (sg := true) (sop := .asr)
      (fun hw u v => ⟨_, rfl, mulhi_narrow_s hw u v⟩) P1 P2 hyb hw⟩
  simp only [LState.emit, LState.fresh]
  rw [P2.2.1, P1.2.1]
  simp [Array.append_assoc]

set_option maxRecDepth 20000 in
/-- **`umulhi_fits_in_32`** (`lower.isle:1071`, `umulhi` at i8/i16/i32 → `uxt`, `uxt`, `madd`, `lsr`). -/
theorem umulhi_fits_in_32_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_1071 := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, -, -, -⟩ :=
    binary_root_invTI hp hctx hi hc (m := m' + 1) (cop := .umulhi) rfl hp.t2362 term_2362_kind
      variantNames_Umulhi rfl hmatch
  cases Classical.em (ty.width ≤ 32) with
  | inr hnw => rw [match_1071_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  rw [match_1071 hp ctx st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨envB, sB, hbinds, -⟩ := evalExpr_let_inv (n := N + 99) heval
  obtain ⟨v1, sx, hv1, -, hbinds'⟩ := evalBinds_cons_inv hbinds
  obtain ⟨v2, sy, hv2, -, -⟩ := evalBinds_cons_inv hbinds'
  obtain ⟨vs1, sa, ha1, happ1⟩ := evalExpr_term_inv hv1
  rw [evalArgs_var1 (n := N + 95) (v := .value x) (by simp)] at ha1
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha1
  obtain ⟨rfl, rfl⟩ := ha1
  obtain ⟨sxs, sxt⟩ := sx
  obtain ⟨t1, hvt1, hrx, hc1⟩ := zext64_invTI hp ctx hco hctx st tr (N + 37) happ1
  have hxb : x < st.nextVreg := hvb x _ hrx
  obtain ⟨r1, ms1, rfl, P1⟩ := partOk_of (F := F) (isem := isem) hR hxb hvt1 hc1
  obtain ⟨vs2, sb, ha2, happ2⟩ := evalExpr_term_inv hv2
  rw [evalArgs_var1 (n := N + 94) (v := .value y) (by simp)] at ha2
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha2
  obtain ⟨rfl, rfl⟩ := ha2
  obtain ⟨sys, syt⟩ := sy
  obtain ⟨t2, hvt2, hry, hc2⟩ := zext64_invTI hp ctx hco hctx sxs sxt (N + 36) happ2
  have hyb : y < st.nextVreg := hvb y _ hry
  obtain ⟨r2, ms2, rfl, P2⟩ := partOk_of (F := F) (isem := isem) hR
    (Nat.lt_of_lt_of_le hyb P1.1) hvt2 hc2
  obtain ⟨tr'', he⟩ := rhs_1071 hp ctx hco st tr N hw happ1 happ2
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  simp only [fresh_fst]
  refine ⟨ms1 ++ ms2 ++ [_, _], _, ?_, rfl,
    mulhiN_lowerInstOk hR hMR (cop := .umulhi) rfl (sg := false) (sop := .lsr)
      (fun hw u v => ⟨_, rfl, mulhi_narrow_u hw u v⟩) P1 P2 hyb hw⟩
  simp only [LState.emit, LState.fresh]
  rw [P2.2.1, P1.2.1]
  simp [Array.append_assoc]

end Backend.Proof

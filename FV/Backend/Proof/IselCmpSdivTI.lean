import FV.Backend.Proof.IselCmpSdiv
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselCmpDivTI
import FV.Backend.Proof.IselCmpDivRootTI

/-!
# `IselCmpSdiv` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpSdiv`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end
section OvfFlags
end OvfFlags
section Run
variable {F : BitVec 64 → Prop} {isem : Sem}
end Run
section Intmin
variable {F : BitVec 64 → Prop} {isem : Sem}
end Intmin
section Finish
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx} {ty : Clif.Ty} {x y : Nat} {st s1 s2 : LState} {kx ky : Nat} {msX msY : List MInst}
end Finish
section Root
variable {p : Program} (hp : Data p)
set_option maxHeartbeats 8000000 in
include hp in
theorem sdiv64_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1145 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h493⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 493 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h561⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 561 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h562⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 562 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h557⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 557 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  obtain ⟨hty⟩ : Nonempty (CTy.int 64 = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .sdiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hty
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety),
    CTy.int.injEq] at hty
  have hE := sext64_ok hp hco (hn := by omega) h557
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpndTI hR hctx hvb (w := ty.width) (.inr ⟨rfl, rfl, hty.symm⟩) (.inr hty.symm) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_okTI hp hco hR hctx (hn := by omega) (w := 64) (e := 0) (by decide)
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_semTI hR hctx (w := 64) (e := 0) (by decide) (by decide) hvb2 hD
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b hty.symm hv hdf hyb }
  have hw4 : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := .inr (.inr (.inr hty.symm))
  have hI := intmin_check_ok hp hco (hn := by omega) (w := 64) (by decide) h562
  rw [show (64 : Nat) = ty.width from hty] at hI
  obtain ⟨kc, msC, rfl, hfC, hkc, -, huC, hsC⟩ := intmin_code_sem (F := F) (isem := isem) hR
    (w := ty.width) hw4 hI
  obtain ⟨hv5, hs5⟩ := trap_if_div_overflow_ok hp hco (hn := by omega) (by decide) h561
  subst hv5
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by decide) h493
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  obtain ⟨hok, hem⟩ := sdiv_base_finish (env := env) (cp := cp) hR hMR hw4 (results := info.results) hdo
    hfC hkc huC hsC
  simp only at hs3
  rw [hs3, hs2, hs5]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem sdiv32_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1153 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h493⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 493 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h561⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 561 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h562⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 562 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h555⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 555 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  have hb32 : (info.resTys.head?.getD CTy.invalid).bits ≤ 32 := by
    rw [hi, Option.some.injEq] at hins; subst hins; assumption
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .sdiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hb32 h698 h562 h561 h493
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety)]
    at hb32 h698 h562 h561 h493
  have hw32 : ty.width ≤ 32 := hb32
  have hwid := cmp_eTy_widths hety
  have hE := sext32_ok hp hco (hn := by omega) h555
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpndTI hR hctx hvb (w := ty.width) (.inl ⟨rfl, rfl⟩) (.inl hw32) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_okTI hp hco hR hctx (hn := by omega) (w := ty.width) (e := 0) hwid
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_semTI hR hctx (w := ty.width) (e := 0) hwid (by decide) hvb2 hD
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  have hw4 : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := hwid
  have hI := intmin_check_ok hp hco (hn := by omega) (w := ty.width) hwid h562
  obtain ⟨kc, msC, rfl, hfC, hkc, -, huC, hsC⟩ := intmin_code_sem (F := F) (isem := isem) hR
    (w := ty.width) hw4 hI
  obtain ⟨hv5, hs5⟩ := trap_if_div_overflow_ok hp hco (hn := by omega) hwid h561
  subst hv5
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by omega) h493
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  obtain ⟨hok, hem⟩ := sdiv_base_finish (env := env) (cp := cp) hR hMR hw4 (results := info.results) hdo
    hfC hkc huC hsC
  simp only at hs3
  rw [hs3, hs2, hs5]
  exact ⟨_, hem, _, rfl, hok⟩

end Root
end Backend.Proof

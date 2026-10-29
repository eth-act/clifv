module

public import FV.Backend.Proof.IselCmpDivRem
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselCmpDivTI
public import FV.Backend.Proof.IselCmpDivRootTI
public import FV.Backend.Proof.IselCmpEmitTI

@[expose] public section

/-!
# `IselCmpDivRem` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpDivRem`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Finish
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx} {ty : Clif.Ty} {x y : Nat} {st s1 s2 : LState} {kx ky : Nat} {msX msY : List MInst}
end Finish
section Finish
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx} {ty : Clif.Ty} {x y : Nat} {st s1 s2 : LState} {kx ky : Nat} {msX msY : List MInst}
end Finish
section Root
variable {p : Program} (hp : Data p)
set_option maxHeartbeats 8000000 in
include hp in
theorem urem32_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1197 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨h172⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 25 172 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h492⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 492 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h444⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 444 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h556⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 556 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  have hb32 : (info.resTys.head?.getD CTy.invalid).bits ≤ 32 := by
    rw [hi, Option.some.injEq] at hins; subst hins; assumption
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .urem) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hb32 h698 h492 h444
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety)]
    at hb32 h698 h492 h444
  have hw32 : ty.width ≤ 32 := hb32
  have hwid := cmp_eTy_widths hety
  have hE := zext32_ok hp hco (hn := by omega) h556
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpndTI hR hctx hvb (w := ty.width) (.inl ⟨rfl, rfl⟩) (.inl hw32) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_okTI hp hco hR hctx (hn := by omega) (w := ty.width) (e := 1) hwid
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_semTI hR hctx (w := ty.width) (e := 1) hwid (by decide) hvb2 hD
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by omega) h492
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by omega) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y false _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  obtain ⟨hok, hem⟩ := urem_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs4, hs2]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem srem64_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1204 := by
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
  obtain ⟨h444⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 444 _ _ _ _) := ⟨‹_›⟩
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
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .srem) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hty
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety),
    CTy.int.injEq] at hty
  have hwid := cmp_eTy_widths hety
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
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by decide) h493
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by decide) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b hty.symm hv hdf hyb }
  obtain ⟨hok, hem⟩ := srem_finish (env := env) (cp := cp) hR hMR (.inr hty.symm) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs4, hs2]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem srem32_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1211 := by
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
  obtain ⟨h444⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 444 _ _ _ _) := ⟨‹_›⟩
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
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .srem) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hb32 h698 h493 h444
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety)]
    at hb32 h698 h493 h444
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
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by omega) h493
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by omega) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  obtain ⟨hok, hem⟩ := srem_finish (env := env) (cp := cp) hR hMR (.inl hw32) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs4, hs2]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem sdiv_safe64_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1163 := by
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
  obtain ⟨h553⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 553 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h557⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 557 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hdi⟩ : Nonempty (externExtract ctx T.def_inst _ st = _) := ⟨‹_›⟩
  obtain ⟨hidv⟩ : Nonempty (externExtract ctx T.inst_data_value _ st = _) := ⟨‹_›⟩
  obtain ⟨hsd⟩ : Nonempty (externCtor ctx T.safe_divisor_from_imm64 _ st = _) := ⟨‹_›⟩
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
  rw [ext_def_inst_iff] at hdi
  obtain ⟨j, hj, hdi⟩ := hdi
  simp only [List.cons.injEq, and_true] at hdi
  subst hdi
  rw [ext_inst_data_value_iff] at hidv
  obtain ⟨info', hi', hidv⟩ := hidv
  simp only [List.cons.injEq, and_true] at hidv
  obtain ⟨-, hd⟩ := hidv
  obtain ⟨ity, imm, rfl, hity, hcl⟩ := iconst_data_invTI hctx hj hi' hd
  rw [ctor_safe_divisor_iff] at hsd
  obtain ⟨hne, rfl, rfl⟩ := hsd
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
  have hI := imm_ok_ai hp hco hR (w := 64) (e := 0) (by decide) (by decide) (by omega) h553
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ := safe_divisor_sem (y := y) (w := 64) (by decide) hj hi' hcl hity hne hI
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by decide) h493
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := .inl hky,
      sY := fun fr ρ b _ hdf hyb => by
        obtain ⟨hb0, -, hu, hr⟩ := hsemY fr ρ ty b hty.symm hdf hyb
        exact ⟨hu, fun wd => ⟨(hr wd).1, fun h0 => absurd h0 hb0, fun _ => (hr wd).2⟩⟩ }
  obtain ⟨hok, hem⟩ := sdiv_safe_finish (env := env) (cp := cp) hR hMR (.inr hty.symm)
    (results := info.results) hdo (fun fr b hdf hyb => (hsemY fr (fun _ => 0) ty b hty.symm hdf hyb).2.1)
  simp only at hs3
  rw [hs3, hs2]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem sdiv_safe32_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1167 := by
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
  obtain ⟨h553⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 553 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h555⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 555 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hdi⟩ : Nonempty (externExtract ctx T.def_inst _ st = _) := ⟨‹_›⟩
  obtain ⟨hidv⟩ : Nonempty (externExtract ctx T.inst_data_value _ st = _) := ⟨‹_›⟩
  obtain ⟨hsd⟩ : Nonempty (externCtor ctx T.safe_divisor_from_imm64 _ st = _) := ⟨‹_›⟩
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
  rw [ext_def_inst_iff] at hdi
  obtain ⟨j, hj, hdi⟩ := hdi
  simp only [List.cons.injEq, and_true] at hdi
  subst hdi
  rw [ext_inst_data_value_iff] at hidv
  obtain ⟨info', hi', hidv⟩ := hidv
  simp only [List.cons.injEq, and_true] at hidv
  obtain ⟨-, hd⟩ := hidv
  obtain ⟨ity, imm, rfl, hity, hcl⟩ := iconst_data_invTI hctx hj hi' hd
  rw [ctor_safe_divisor_iff] at hsd
  obtain ⟨hne, rfl, rfl⟩ := hsd
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hb32 h553 h493 hne
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety)]
    at hb32 h553 h493 hne
  have hw32 : ty.width ≤ 32 := hb32
  have hwid := cmp_eTy_widths hety
  have hE := sext32_ok hp hco (hn := by omega) h555
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpndTI hR hctx hvb (w := ty.width) (.inl ⟨rfl, rfl⟩) (.inl hw32) hE
  have hI := imm_ok_ai hp hco hR (w := ty.width) (e := 0) hwid (by decide) (by omega) h553
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ := safe_divisor_sem (y := y) (w := ty.width) hwid hj hi' hcl hity hne hI
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by omega) h493
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := .inl hky,
      sY := fun fr ρ b _ hdf hyb => by
        obtain ⟨hb0, -, hu, hr⟩ := hsemY fr ρ ty b rfl hdf hyb
        exact ⟨hu, fun wd => ⟨(hr wd).1, fun h0 => absurd h0 hb0, fun _ => (hr wd).2⟩⟩ }
  obtain ⟨hok, hem⟩ := sdiv_safe_finish (env := env) (cp := cp) hR hMR (.inl hw32)
    (results := info.results) hdo (fun fr b hdf hyb => (hsemY fr (fun _ => 0) ty b rfl hdf hyb).2.1)
  simp only at hs3
  rw [hs3, hs2]
  exact ⟨_, hem, _, rfl, hok⟩

end Root
end Backend.Proof

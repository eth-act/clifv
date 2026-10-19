import FV.Backend.Proof.IselCmpDivRoot
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselCmpDivTI

/-!
# `IselCmpDivRoot` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpDivRoot`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
/-- **The dividend**: a `put_in_reg_*ext*` result (or the value's own register) holding the value
as a division operand. -/
theorem ext_divOpndTI {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInvT f ctx) {x : Nat} {sg : Bool} {toB w : Nat} {pass : List CTy}
    {s s' : LState} {v : V} (hvb : ValsBelow ctx s)
    (hcase : (toB = 32 ∧ pass = [.int 32, .int 64]) ∨ (toB = 64 ∧ pass = [.int 64] ∧ w = 64))
    (hw : w ≤ 32 ∨ w = 64) (h : ExtOut ctx x sg toB pass s s' v)
    (hxI : IntPos ctx x := by int_posA) :
    ∃ k ms, v = .reg (.vreg k .int) ∧ Frag s s' ms ∧ k < s'.nextVreg ∧ (s.nextVreg ≤ k ∨ k = x) ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (ty : Clif.Ty) (a : BitVec ty.width), ty.width = w →
        ValsHeld fr ρ → DFGCons ctx fr → fr.regs x = some ⟨ty, a⟩ →
        UsesLo s.nextVreg fr ms ∧ ∀ wd, Runs F isem ms ρ wd (fun ρ' _ => DivOpnd sg a (ρ' k)) := by
  have hto : toB = 32 ∨ toB = 64 := by rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨k, ms, rfl, hf, hk, hkx, hsem⟩ := ExtOut.semT hR hctx (hxi := by int_posA) hvb hto
    (by rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ <;> intro t ht <;> simp at ht <;>
      rcases ht with rfl | rfl <;> simp)
    (by rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ <;> simp) h
  refine ⟨k, ms, rfl, hf, hk, hkx, fun fr ρ ty a htw hh hdf hxv => ?_⟩
  obtain ⟨hu, hrun⟩ := hsem fr ρ _ (hh x _ hxv) hdf hxv
  refine ⟨hu, fun wd => (hrun wd).imp fun ρ' _ _ he => ?_⟩
  rcases hw with hw | hw
  · rcases hcase with ⟨rfl, -⟩ | ⟨-, -, rfl⟩
    · unfold DivOpnd
      simp only [show ty.width ≤ 32 by omega, ↓reduceIte]
      exact he.2 (by simp; omega)
    · omega
  · exact divOpnd_of_vholds64 (by omega) he.1

section Finish
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx} {ty : Clif.Ty} {x y : Nat} {st s1 s2 : LState} {kx ky : Nat} {msX msY : List MInst}
  {sg : Bool}
end Finish
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end
section Root
variable {p : Program} (hp : Data p)
set_option maxHeartbeats 8000000 in
include hp in
theorem udiv64_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1116 := by
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
  obtain ⟨h698⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 698 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hpr⟩ : Nonempty (externCtor ctx T.put_in_reg _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  obtain ⟨hty⟩ : Nonempty (CTy.int 64 = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .udiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  rw [ctor_put_in_reg_iff] at hpr
  obtain ⟨rx, hrx, rfl, rfl⟩ := hpr
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hty
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety),
    CTy.int.injEq] at hty
  have hD := put_nonzero_in_reg_okTI hp hco hR hctx (hn := by omega) (w := 64) (e := 1) (by decide)
    (by decide) h698
  dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ := divisor_semTI hR hctx (w := 64) (e := 1) (by decide) (by decide) hvb hD
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by decide) h492
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hrx' := hctx.valueRegI x rx hrx
  subst hrx'
  have hxlt := hvb x _ hrx
  have hdo : DivOperands F isem ctx ty x y false _ _ _ x ky [] msY :=
    { xlt := hxlt, vb := hvb, fX := Frag.nil _, kxlt := hxlt, kxl := .inr rfl,
      sX := fun fr ρ a hh hdf hxa =>
        ⟨UsesLo.nil _ _, fun wd => Runs.nil (divOpnd_of_vholds64 hty.symm (hh x _ hxa))⟩,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b hty.symm hv hdf hyb }
  obtain ⟨hok, hem⟩ := udiv_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs2]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem udiv32_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1119 := by
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
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_div_inv (op := .udiv) rfl hdat
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at hb32 h698
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety)] at hb32 h698
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
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by decide) h492
  subst hv2
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y false _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  obtain ⟨hok, hem⟩ := udiv_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs2]
  rw [show szOf 32 = szOf ty.width by simp [szOf, hw32]]
  exact ⟨_, hem, _, rfl, hok⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem urem64_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1190 := by
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
  obtain ⟨h558⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 558 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  obtain ⟨hty⟩ : Nonempty (CTy.int 64 = _) := ⟨‹_›⟩
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
  rw [hres] at hty
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety),
    CTy.int.injEq] at hty
  have hwid := cmp_eTy_widths hety
  have hE := zext64_ok hp hco (hn := by omega) h558
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpndTI hR hctx hvb (w := ty.width) (.inr ⟨rfl, rfl, hty.symm⟩) (.inr hty.symm) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_okTI hp hco hR hctx (hn := by omega) (w := 64) (e := 1) (by decide)
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_semTI hR hctx (w := 64) (e := 1) (by decide) (by decide) hvb2 hD
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by decide) h492
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by decide) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := cmp_output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y false _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b hty.symm hv hdf hyb }
  obtain ⟨hok, hem⟩ := urem_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs4, hs2]
  rw [show szOf 64 = szOf ty.width by rw [hty]]
  exact ⟨_, hem, _, rfl, hok⟩

end Root
end Backend.Proof

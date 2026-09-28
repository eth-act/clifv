import FV.Backend.Proof.IselCmpDivRoot

/-!
# Family C: remaining division root rules (urem 32, srem, sdiv)
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem urem32_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1197 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
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
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width]
    at hb32 h698 h492 h444
  have hw32 : ty.width ≤ 32 := hb32
  have hwid := eTy_widths hety
  have hE := zext32_ok hp hco (hn := by omega) h556
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpnd hR hctx hvb (w := ty.width) (.inl ⟨rfl, rfl⟩) (.inl hw32) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := ty.width) (e := 1) hwid
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_sem hR hctx (w := ty.width) (e := 1) hwid (by decide) hvb2 hD
  obtain ⟨hv2, hs2⟩ := a64_udiv_ok hp hco (by omega) (by omega) h492
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by omega) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y false _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  obtain ⟨hok, hem⟩ := urem_finish (env := env) (cp := cp) hR hMR (by omega) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs4, hs2]
  exact ⟨_, hem, _, rfl, hok⟩

end Root

end Backend.Proof

import FV.Backend.Proof.IselCmpDivRoot

/-!
# Family C: remaining division root rules (urem 32, srem, sdiv)
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Signed arithmetic -/

open BitVec in
theorem sub_sdiv_mul_eq_srem {m : Nat} (X Y : BitVec m) : X - X.sdiv Y * Y = X.srem Y := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_sub, toInt_mul, toInt_sdiv]
  simp only [Int.bmod_mul_bmod, Int.sub_bmod_bmod]
  rw [Int.mul_comm, ← Int.tmod_def, ← toInt_srem, toInt_bmod_cancel]

open BitVec in
theorem srem_signExtend {n m : Nat} (h : n ≤ m) (a b : BitVec n) :
    (a.signExtend m).srem (b.signExtend m) = (a.srem b).signExtend m := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_srem, toInt_signExtend_of_le h, toInt_signExtend_of_le h, toInt_signExtend_of_le h, toInt_srem]

open BitVec in
theorem sdiv_signExtend {n m : Nat} (h : n ≤ m) (a b : BitVec n) (hov : a ≠ intMin n ∨ b ≠ -1#n) :
    (a.signExtend m).sdiv (b.signExtend m) = (a.sdiv b).signExtend m := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_sdiv, toInt_signExtend_of_le h, toInt_signExtend_of_le h, ← toInt_sdiv_of_ne_or_ne a b hov,
    ← toInt_signExtend_of_le (v := m) h, toInt_bmod_cancel]

open BitVec in
theorem se_trunc {n : Nat} (hn : n ≤ 32) (x : BitVec n) :
    (((x.signExtend 32).setWidth 64).setWidth 128).setWidth n = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 32 by omega, show i < 64 by omega, show i < 128 by omega]

open BitVec in
theorem resX32_of_eq {n : Nat} (hn : n ≤ 32) (r : BitVec OperandSize.size32.bits) (x : BitVec n)
    (h : r = x.signExtend 32) : (resX .size32 r).setWidth n = x := by
  subst h
  exact se_trunc hn x

open BitVec in
theorem srem_core {n : Nat} (hw : n ≤ 32 ∨ n = 64) {a b : BitVec n} {A B : CV}
    (hA : DivOpnd true a A) (hB : DivOpnd true b B) :
    (resX (szOf n) (opnd (szOf n) A - opnd (szOf n) (resX (szOf n) ((opnd (szOf n) A).sdiv (opnd (szOf n) B))) *
      opnd (szOf n) B)).setWidth n = a.srem b := by
  rw [opnd_resX, sub_sdiv_mul_eq_srem]
  unfold DivOpnd at hA hB
  rcases hw with h32 | rfl
  · have e : szOf n = .size32 := ite_eq_left_iff.mpr (fun h => absurd h32 h)
    rw [e]
    simp only [h32, ↓reduceIte] at hA hB
    exact resX32_of_eq h32 _ _ (by have := srem_signExtend h32 a b; rw [← hA, ← hB] at this; exact this)
  · simp only [show ¬ (64:Nat) ≤ 32 by decide, ↓reduceIte, BitVec.setWidth_eq] at hA hB
    have hA' : opnd .size64 A = a := by rw [← hA]; exact BitVec.setWidth_eq _
    have hB' : opnd .size64 B = b := by rw [← hB]; exact BitVec.setWidth_eq _
    show (resX .size64 ((opnd .size64 A).srem (opnd .size64 B))).setWidth 64 = _
    rw [hA', hB']
    simp [resX, ofX]
    exact BitVec.setWidth_eq _

open BitVec in
theorem sdiv_core {n : Nat} (hw : n ≤ 32 ∨ n = 64) {a b : BitVec n} {A B : CV}
    (hA : DivOpnd true a A) (hB : DivOpnd true b B) (hov : a ≠ intMin n ∨ b ≠ -1#n) :
    (resX (szOf n) ((opnd (szOf n) A).sdiv (opnd (szOf n) B))).setWidth n = a.sdiv b := by
  unfold DivOpnd at hA hB
  rcases hw with h32 | rfl
  · have e : szOf n = .size32 := ite_eq_left_iff.mpr (fun h => absurd h32 h)
    rw [e]
    simp only [h32, ↓reduceIte] at hA hB
    exact resX32_of_eq h32 _ _ (by have := sdiv_signExtend h32 a b hov; rw [← hA, ← hB] at this; exact this)
  · simp only [show ¬ (64:Nat) ≤ 32 by decide, ↓reduceIte, BitVec.setWidth_eq] at hA hB
    have hA' : opnd .size64 A = a := by rw [← hA]; exact BitVec.setWidth_eq _
    have hB' : opnd .size64 B = b := by rw [← hB]; exact BitVec.setWidth_eq _
    show (resX .size64 ((opnd .size64 A).sdiv (opnd .size64 B))).setWidth 64 = _
    rw [hA', hB']
    simp [resX, ofX]
    exact BitVec.setWidth_eq _

theorem srem_trap {n : Nat} {a b : BitVec n} {c : Clif.TrapCode} (h : Clif.Sem.div .srem a b = .error c) :
    b = 0#n ∧ c = .intDivz := by
  simp only [Clif.Sem.div, Clif.Sem.srem] at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · cases h

theorem srem_ok {n : Nat} {a b q : BitVec n} (h : Clif.Sem.div .srem a b = .ok q) :
    b ≠ 0#n ∧ q = a.srem b := by
  simp only [Clif.Sem.div, Clif.Sem.srem] at h
  split at h
  · cases h
  · cases h; exact ⟨‹_›, rfl⟩

section Finish
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx} {ty : Clif.Ty} {x y : Nat} {st s1 s2 : LState} {kx ky : Nat} {msX msY : List MInst}

theorem srem_finish (hR : Refines F isem) (hMR : MRStable F MR) (hw : ty.width ≤ 32 ∨ ty.width = 64)
    {results : List Nat} (h : DivOperands F isem ctx ty x y true st s1 s2 kx ky msX msY) :
    let m1 := MInst.aluRRR .sDiv (szOf ty.width) (.vreg s2.nextVreg .int) (.vreg kx .int) (.vreg ky .int)
    let s3 := (s2.fresh .int).2.emit m1
    let m2 := MInst.aluRRRR .mSub (szOf ty.width) (.vreg s3.nextVreg .int) (.vreg s2.nextVreg .int)
      (.vreg ky .int) (.vreg kx .int)
    LowerInstOk isem MR env cp ctx (.div .srem ty x y) results st [[.vreg s3.nextVreg .int]]
      ((s3.fresh .int).2.emit m2) (msX ++ msY ++ ([m1] ++ [m2])) ∧
    ((s3.fresh .int).2.emit m2).emitted = st.emitted ++ (msX ++ msY ++ ([m1] ++ [m2])).toArray := by
  intro m1 s3 m2
  have hf1 : Frag s2 s3 [m1] := Frag.fresh_emit s2 (by simp [m1, vdefs_aluRRR'])
  have hf2 : Frag s3 ((s3.fresh .int).2.emit m2) [m2] :=
    Frag.fresh_emit s3 (by simp [m2, vdefs_aluRRRR'])
  have hf := (h.fX.append h.fY).append (hf1.append hf2)
  have hs3 : s3.nextVreg = s2.nextVreg + 1 := by simp [s3, LState.emit, LState.fresh]
  refine ⟨lowerInstOk_div hMR hf.mono hf.defs (by have := (h.fX.append h.fY).mono; omega) ?_,
    hf.emitted⟩
  intro fr ρ w a b _ hh hdf hxa hyb
  obtain ⟨hu, hukx, huky⟩ := h.uses hh hdf hxa hyb
  obtain ⟨hky, htr, hrun⟩ := h.run hh hdf hxa hyb w
  have hkx := h.kxlt
  have hs12 := h.fY.mono
  refine ⟨hu.append ?_, fun c hc => ?_, fun q hq => ?_⟩
  · intro m hm u hu'
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with rfl | rfl
    · simp only [m1, vuseNums_aluRRR', List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl
      · exact hukx
      · exact huky
    · simp only [m2, vuseNums_aluRRRR', List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl | rfl
      · exact .inl (by have := (h.fX.append h.fY).mono; omega)
      · exact huky
      · exact hukx
  · obtain ⟨h0, rfl⟩ := srem_trap hc
    exact (htr h0).append
  · obtain ⟨h0, rfl⟩ := srem_ok hq
    refine Runs.append (hrun h0) fun ρ1 w1 ⟨h1, h2⟩ => ?_
    refine Runs.append (runs_sdiv hR _ _ _ _ ρ1 w1) fun ρ2 w2 e2 => ?_
    refine (runs_msub hR _ _ _ _ _ ρ2 w2).imp fun ρ' _ _ e => ?_
    rw [e, upd_same, e2, upd_same, div_upd_ne (by omega : kx ≠ s2.nextVreg),
      div_upd_ne (by omega : ky ≠ s2.nextVreg)]
    exact srem_core hw h1 h2

end Finish

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

set_option maxHeartbeats 8000000 in
include hp in
theorem srem64_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1204 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
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
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width,
    CTy.int.injEq] at hty
  have hwid := eTy_widths hety
  have hE := sext64_ok hp hco (hn := by omega) h557
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpnd hR hctx hvb (w := ty.width) (.inr ⟨rfl, rfl, hty.symm⟩) (.inr hty.symm) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := 64) (e := 0) (by decide)
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_sem hR hctx (w := 64) (e := 0) (by decide) (by decide) hvb2 hD
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by decide) h493
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by decide) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := output_reg_ok hp hco (by omega) h172
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
theorem srem32_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1211 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
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
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width]
    at hb32 h698 h493 h444
  have hw32 : ty.width ≤ 32 := hb32
  have hwid := eTy_widths hety
  have hE := sext32_ok hp hco (hn := by omega) h555
  obtain ⟨_, -, rx, hrx, -⟩ := id hE
  have hxlt := hvb x _ hrx
  obtain ⟨kx, msX, rfl, hfX, hkx, hkxl, hsX⟩ :=
    ext_divOpnd hR hctx hvb (w := ty.width) (.inl ⟨rfl, rfl⟩) (.inl hw32) hE
  have hvb2 : ValsBelow ctx _ := fun z r hz => Nat.lt_of_lt_of_le (hvb z r hz) hfX.mono
  have hD := put_nonzero_in_reg_ok hp hco hR hctx (hn := by omega) (w := ty.width) (e := 0) hwid
    (by decide) h698
  try dsimp only at hD
  obtain ⟨ky, msY, rfl, hfY, hky, hsemY⟩ :=
    divisor_sem hR hctx (w := ty.width) (e := 0) hwid (by decide) hvb2 hD
  obtain ⟨hv2, hs2⟩ := a64_sdiv_ok hp hco (by omega) (by omega) h493
  subst hv2
  obtain ⟨hv4, hs4⟩ := msub_ok hp hco (by omega) (by omega) h444
  subst hv4
  obtain ⟨hs3, rfl⟩ := output_reg_ok hp hco (by omega) h172
  have hdo : DivOperands F isem ctx ty x y true _ _ _ kx ky msX msY :=
    { xlt := hxlt, vb := hvb, fX := hfX, kxlt := hkx, kxl := hkxl,
      sX := fun fr ρ a hh hdf hxa => hsX fr ρ ty a rfl hh hdf hxa,
      fY := hfY, kyl := hky,
      sY := fun fr ρ b hv hdf hyb => hsemY fr ρ ty b rfl hv hdf hyb }
  obtain ⟨hok, hem⟩ := srem_finish (env := env) (cp := cp) hR hMR (.inl hw32) (results := info.results) hdo
  simp only at hs3
  rw [hs3, hs4, hs2]
  exact ⟨_, hem, _, rfl, hok⟩

end Root

end Backend.Proof

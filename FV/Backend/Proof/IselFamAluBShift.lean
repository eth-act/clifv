import FV.Backend.Proof.IselFamAluBShiftTerms

/-!
# Family B: the scalar shift root rules (`ishl`/`ushr`/`sshr`, `lower.isle:1545–1699`)

`(lower (op ty x y))` → `(do_shift (ALUOp.Lsl/Lsr/Asr) ty (put_in_reg[_zext/_sext] x) y)` at
`fits_in_32` types and at `$I64`. Through `shift_ruleOk`: the value operand is prepared
(`put_in_reg`, or `put_in_reg_{z,s}ext{32,64}`: pass-through or one `extend`, `extOut_prun`),
then `do_shift_ok` gives the shift at the operand size; the width lemmas (`shl_setWidth`,
`lsr_zext`, `asr_sext`) bring it to the CLIF result.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Width lemmas -/

theorem shl_setWidth {n m : Nat} (h : m ≤ n) (A : BitVec n) (s : Nat) :
    (A <<< s).setWidth m = (A.setWidth m) <<< s := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have hin : i < n := by omega
  simp [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, hin]
  rw [BitVec.getLsbD_eq_getElem (by omega)]

theorem lsr_zext {m n : Nat} (h : m ≤ n) (u : BitVec m) (s : Nat) :
    ((u.setWidth n) >>> s).setWidth m = u >>> s := by
  apply BitVec.eq_of_toNat_eq
  have hu := u.isLt
  have h2 : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  rw [Nat.mod_eq_of_lt (by omega : u.toNat < 2 ^ n)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hu)

theorem asr_sext {m n : Nat} (h : m ≤ n) (u : BitVec m) (s : Nat) :
    ((u.signExtend n).sshiftRight s).setWidth m = u.sshiftRight s := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have hin : ¬ n ≤ i := by omega
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend,
    BitVec.getElem_sshiftRight, BitVec.msb_signExtend, hin, decide_false, Bool.not_false,
    Bool.true_and]
  by_cases h1 : s + i < m
  · have h2 : s + i < n := by omega
    simp [h1, h2, BitVec.getLsbD_eq_getElem]
  · by_cases h2 : s + i < n
    · simp [h1, h2]
    · have h3 : 0 < n := by omega
      by_cases h4 : n ≤ m
      · have : n = m := by omega
        subst this
        simp [h1, h3, BitVec.msb_eq_getMsbD_zero]
      · simp [h1, h2, h3, h4]

theorem setWidth_opnd {sz : OperandSize} {w : Nat} (hw : w ≤ sz.bits) (X : CV) :
    (opnd sz X).setWidth w = X.setWidth w := by
  simp only [opnd, lo64, BitVec.setWidth_setWidth_of_le _ hw,
    BitVec.setWidth_setWidth_of_le _ (Nat.le_trans hw (opSize_bits_le sz))]

theorem fin_lsl (sz : OperandSize) {m : Nat} (hm : m ≤ sz.bits) {u : BitVec m} {X D : CV}
    {s : Nat} (hX : X.setWidth m = u) (hD : opnd sz D = shiftF .lsl (opnd sz X) s) :
    D.setWidth m = u <<< s := by
  rw [← setWidth_opnd hm D, hD]
  simp only [shiftF]
  rw [shl_setWidth hm, setWidth_opnd hm, hX]

theorem fin_lsr (sz : OperandSize) {m : Nat} (hm : m ≤ sz.bits) {u : BitVec m} {X D : CV}
    {s : Nat} (hA : opnd sz X = u.setWidth sz.bits) (hD : opnd sz D = shiftF .lsr (opnd sz X) s) :
    D.setWidth m = u >>> s := by
  rw [← setWidth_opnd hm D, hD]
  simp only [shiftF]
  rw [hA, lsr_zext hm]

theorem fin_asr (sz : OperandSize) {m : Nat} (hm : m ≤ sz.bits) {u : BitVec m} {X D : CV}
    {s : Nat} (hA : opnd sz X = u.signExtend sz.bits)
    (hD : opnd sz D = shiftF .asr (opnd sz X) s) :
    D.setWidth m = u.sshiftRight s := by
  rw [← setWidth_opnd hm D, hD]
  simp only [shiftF]
  rw [hA, asr_sext hm]

theorem hA64 {X : CV} {u : BitVec 64} (h : X.setWidth 64 = u) :
    opnd .size64 X = u.setWidth OperandSize.size64.bits := by
  subst h; rfl

theorem hA64s {X : CV} {u : BitVec 64} (h : X.setWidth 64 = u) :
    opnd .size64 X = u.signExtend OperandSize.size64.bits := by
  subst h
  simp only [opnd, lo64, OperandSize.bits, BitVec.setWidth_eq, BitVec.signExtend_eq]

/-! ## Composition: operand preparation, then `do_shift` -/

section Sem
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- **Meaning of a `put_in_reg_*ext*` call as a pure run**: the returned vreg `k` (the value's
own, or a fresh one defined by one `extend`) holds the value, extended to `toB` bits when it
has at most 32; vregs below the start counter are unchanged. -/
theorem extOut_prun (hR : Refines F isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    {x : Nat} {sg : Bool} {toB : Nat} {pass : List CTy} {s s' : LState} {v : V}
    (hvb : ValsBelow ctx s) (hto : toB = 32 ∨ toB = 64)
    (hpass : ∀ t ∈ pass, t = .int 64 ∨ (t = .int 32 ∧ toB = 32)) (h32 : toB = 32 → .int 32 ∈ pass)
    (h : ExtOut ctx x sg toB pass s s' v) :
    ∃ k ms, v = .reg (.vreg k .int) ∧ s'.emitted = s.emitted ++ ms.toArray ∧
      s.nextVreg ≤ s'.nextVreg ∧
      (∀ mi ∈ ms, ∀ e ∈ vdefs mi, s.nextVreg ≤ e ∧ e < s'.nextVreg) ∧
      (∀ mi ∈ ms, ∀ u ∈ vuseNums mi, s.nextVreg ≤ u ∨ u = x) ∧
      (k = x ∨ s.nextVreg ≤ k) ∧ k < s'.nextVreg ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (vx : Clif.Val), VHolds vx (ρ x) → DFGCons ctx fr →
        fr.regs x = some vx →
        ∃ ρ1, PRun F isem ms ρ ρ1 ∧ (∀ z, z < s.nextVreg → ρ1 z = ρ z) ∧
          ExtHolds sg toB vx (ρ1 k) := by
  obtain ⟨t, hT, rx, hx, hcase⟩ := h
  have hrx := hctx.valueReg x rx hx
  subst hrx
  have hxlt := vreg_lt hvb hx
  rcases hcase with ⟨ht, rfl, hs⟩ | ⟨ht, hb, rfl, rfl⟩
  · subst s'
    refine ⟨x, [], rfl, by simp, Nat.le_refl _, by simp, by simp, .inl rfl, hxlt,
      fun fr ρ vx hheld hdfg hvx => ⟨ρ, prun_nil _, fun _ _ => rfl, hheld, fun hw => ?_⟩⟩
    have hty := hdfg.2 x t vx hT hvx
    obtain ⟨vty, vb⟩ := vx
    have hv := hheld
    simp only [VHolds] at hv
    subst hty
    rcases hpass _ ht with h64 | ⟨h32', rfl⟩
    · cases vty <;> simp [CTy.ofClif] at h64; simp [Clif.Ty.width] at hw
    · cases vty <;> simp [CTy.ofClif] at h32'
      subst hv
      simp only [lo64, Clif.Ty.width, Bool.false_eq_true, ↓reduceIte]
      cases sg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_decide
  · have hf : (s.fresh .int).1 = .vreg s.nextVreg .int := rfl
    rw [hf]
    refine ⟨s.nextVreg, [.extend (.vreg s.nextVreg .int) (.vreg x .int) sg t.bits toB], rfl, by simp only [LState.emit, LState.fresh]; apply Array.ext'; simp,
      by simp [LState.emit, LState.fresh], ?_, ?_, .inr (Nat.le_refl _),
      by simp [LState.emit, LState.fresh], fun fr ρ vx hheld hdfg hvx => ?_⟩
    · intro mi hmi e he
      simp only [List.mem_singleton] at hmi
      subst hmi
      rw [vdefs_extend', List.mem_singleton] at he
      subst he
      simp [LState.emit, LState.fresh]
    · intro mi hmi u hu
      simp only [List.mem_singleton] at hmi
      subst hmi
      rw [vuseNums_extend', List.mem_singleton] at hu
      exact .inr hu
    · have hty := hdfg.2 x t vx hT hvx
      obtain ⟨vty, vb⟩ := vx
      subst hty
      rw [ofClif_bits] at hb
      dsimp only at hb
      have hne : vty.width < toB := by
        rcases hto with rfl | rfl
        · have := h32 rfl
          cases vty <;> simp [Clif.Ty.width, CTy.ofClif] at hb ⊢
          exact ht this
        · omega
      have hfrom : vty.width = 8 ∨ vty.width = 16 ∨ vty.width = 32 := by
        cases vty <;> simp [Clif.Ty.width] at hb ⊢
      rw [ofClif_bits]
      refine ⟨_, prun_rr hR (operands_extend' _ _ _ _ _)
        (fun w => ispec_extend hfrom hto hne) (prun_nil _), fun z hz => ?_, ?_⟩
      · simp [upd, show z ≠ s.nextVreg by omega]
      · rw [upd_same]
        exact extHolds_extend sg vb (by omega) toB hto hne _ (hheld)

/-- **Operand preparation `ms1` (from `st` to `st1`, reading `x`), then `do_shift`**: the code's
shape, and its meaning from any run of the preparation that keeps the vregs below `st`. -/
theorem shift_compose {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {op : ALUOp}
    {w xa x y : Nat} {st st1 st2 : LState} {ms1 : List MInst} {v1 : V} (hvb : ValsBelow ctx st)
    (hem : st1.emitted = st.emitted ++ ms1.toArray) (hmono : st.nextVreg ≤ st1.nextVreg)
    (hdefs : ∀ mi ∈ ms1, ∀ e ∈ vdefs mi, st.nextVreg ≤ e ∧ e < st1.nextVreg)
    (huses : ∀ mi ∈ ms1, ∀ u ∈ vuseNums mi, st.nextVreg ≤ u ∨ u = x)
    (hxa : xa = x ∨ st.nextVreg ≤ xa)
    (hs : ShiftRes F isem ctx op w xa y st1 st2 v1) :
    ∃ ms2 d, v1 = .reg (.vreg d .int) ∧ CodeShapeU st st2 (ms1 ++ ms2) d [x, y] ∧
      ∀ (fr : Clif.Frame) (ρ ρ1 : Nat → CV) (yv : Clif.Val), PRun F isem ms1 ρ ρ1 →
        (∀ z, z < st.nextVreg → ρ1 z = ρ z) → ValsHeld fr ρ → DFGCons ctx fr →
        fr.regs y = some yv →
        ∃ ρ', PRun F isem (ms1 ++ ms2) ρ ρ' ∧
          opnd (szOf w) (ρ' d) = shiftF op (opnd (szOf w) (ρ1 xa)) (yv.bits.toNat % w) := by
  obtain ⟨ms2, d, rfl, hsh, hsem⟩ := hs
  refine ⟨ms2, d, rfl, ⟨?_, by have := hsh.mono; omega, by have := hsh.res; omega, ?_, ?_⟩, ?_⟩
  · rw [hsh.emitted, hem]; simp
  · intro mi hmi e he
    rcases List.mem_append.mp hmi with h | h
    · have := hdefs mi h e he; have := hsh.mono; omega
    · have := hsh.defs mi h e he; omega
  · intro mi hmi u hu
    rcases List.mem_append.mp hmi with h | h
    · rcases huses mi h u hu with h' | h'
      · exact .inl h'
      · exact .inr (by simp [h'])
    · rcases hsh.uses mi h u hu with h' | h'
      · exact .inl (by omega)
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
        rcases h' with rfl | rfl
        · rcases hxa with rfl | h''
          · exact .inr (by simp)
          · exact .inl h''
        · exact .inr (by simp)
  · intro fr ρ ρ1 yv h1 hfr hvals hdfg hy
    obtain ⟨ρ', h2, hr⟩ := hsem fr ρ1 yv hdfg hy (fun r hr => by
      have := hctx.valueReg y r hr
      subst this
      rw [hfr y (hvb y _ hr)]
      exact hvals y yv hy)
    exact ⟨ρ', prun_append h1 h2, hr⟩

end Sem

/-! ## Root rule matches -/

section Match
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (st : LState) (tr : Array RuleId)
  (n : Nat)

include hp in
theorem match_1545 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 103 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1545 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_array_2 ctx st x y
  cases hp
  isel_eval [*, rule_lower_1545]

include hp in
theorem match_1545_none {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : ¬ w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 103 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1545 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_array_2 ctx st x y
  cases hp
  isel_eval [*, rule_lower_1545]

include hp in
theorem match_1549 {i x y : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 64))
    (hd : info.data = .data 152 2 [.data 151 103 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1549 [.inst i]).run (st, tr) =
      .ok (some (env2 (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h3 := ext_value_array_2 ctx st x y
  have he := sem_eq_beq' ctx
  cases hp
  isel_eval [*, rule_lower_1549]

include hp in
theorem match_1549_none {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 64)
    (hd : info.data = .data 152 2 [.data 151 103 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1549 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h3 := ext_value_array_2 ctx st x y
  have he := sem_eq_beq' ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [hw]
  have hne' : (V.ty (.int 64) == V.ty (.int w)) = false := by simp [Ne.symm hw]
  cases hp
  isel_eval [*, rule_lower_1549]

include hp in
theorem match_1638 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 104 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1638 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_array_2 ctx st x y
  cases hp
  isel_eval [*, rule_lower_1638]

include hp in
theorem match_1638_none {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : ¬ w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 104 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1638 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_array_2 ctx st x y
  cases hp
  isel_eval [*, rule_lower_1638]

include hp in
theorem match_1642 {i x y : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 64))
    (hd : info.data = .data 152 2 [.data 151 104 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1642 [.inst i]).run (st, tr) =
      .ok (some (env2 (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h3 := ext_value_array_2 ctx st x y
  have he := sem_eq_beq' ctx
  cases hp
  isel_eval [*, rule_lower_1642]

include hp in
theorem match_1642_none {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 64)
    (hd : info.data = .data 152 2 [.data 151 104 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1642 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h3 := ext_value_array_2 ctx st x y
  have he := sem_eq_beq' ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [hw]
  have hne' : (V.ty (.int 64) == V.ty (.int w)) = false := by simp [Ne.symm hw]
  cases hp
  isel_eval [*, rule_lower_1642]

include hp in
theorem match_1695 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 105 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1695 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_array_2 ctx st x y
  cases hp
  isel_eval [*, rule_lower_1695]

include hp in
theorem match_1695_none {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : ¬ w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 105 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1695 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_value_array_2 ctx st x y
  cases hp
  isel_eval [*, rule_lower_1695]

include hp in
theorem match_1699 {i x y : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 64))
    (hd : info.data = .data 152 2 [.data 151 105 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1699 [.inst i]).run (st, tr) =
      .ok (some (env2 (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h3 := ext_value_array_2 ctx st x y
  have he := sem_eq_beq' ctx
  cases hp
  isel_eval [*, rule_lower_1699]

include hp in
theorem match_1699_none {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 64)
    (hd : info.data = .data 152 2 [.data 151 105 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1699 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h3 := ext_value_array_2 ctx st x y
  have he := sem_eq_beq' ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [hw]
  have hne' : (V.ty (.int 64) == V.ty (.int w)) = false := by simp [Ne.symm hw]
  cases hp
  isel_eval [*, rule_lower_1699]

end Match

section Rules
variable {F : BitVec 64 → Prop} {isem : Sem}

set_option maxHeartbeats 1000000 in
/-- **`ishl_fits_in_32`** (`lower.isle:1545`), i8..i32. -/
theorem ishl_fits_in_32_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1545 := by
  refine shift_ruleOk hp (cop := .ishl) rfl rfl hp.t2387 term_2387_kind rfl rfl
    (fun w x y => env3 (.ty (.int w)) (.value x) (.value y)) (fun w => w ≤ 32) F isem MR env cp hMR
    ?_ ?_
  · intro ctx cfg ii info w x y st tr m env' s1 hi hhead _ hd _ hm
    by_cases h32 : w ≤ 32
    · rw [match_1545 hp ctx st tr m hi hhead h32 hd] at hm
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hm
      exact ⟨hm.1.symm, hm.2.symm, h32⟩
    · rw [match_1545_none hp ctx st tr m hi hhead h32 hd] at hm
      cases hm
  · intro f ctx hctx cfg x y w st tr n v s' hco hvb hw hW h32 heval
    have hp' := hp
    cases hp
    isel_inv [*, rule_lower_1545] at heval
    have hrx := ‹ctx.valueReg? x = some _›
    have hDo := ‹ApplyInternal _ _ _ _ 27 703 _ _ _ _›
    have hOut := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    obtain rfl := hctx.valueReg x _ hrx
    have hs := do_shift_ok hp' hco hR hctx (by omega) (k := 18) (op := .lsl) (.inl ⟨rfl, rfl⟩) hW
      (hvb x _ hrx) hDo
    obtain ⟨ms2, d, rfl, hsh, hsem⟩ := shift_compose (ms1 := []) hctx hvb (by simp)
      (Nat.le_refl _) (by simp) (by simp) (.inl rfl) hs
    obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hOut
    refine ⟨[] ++ ms2, d, rfl, by rw [hst]; exact hsh, ?_⟩
    intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
    subst hty
    obtain ⟨ρ', hrun, hD⟩ := hsem fr ρ ρ yv (prun_nil _) (fun _ _ => rfl) hvals hdfg hy
    refine ⟨ρ', hrun, ?_⟩
    simp only [Clif.Sem.shift, Clif.Sem.ishl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
    subst hres
    exact fin_lsl (szOf ty.width) (szOf_bits hw) (hvals x _ hx) hD

set_option maxHeartbeats 1000000 in
/-- **`ishl_64`** (`lower.isle:1549`), i64. -/
theorem ishl_64_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1549 := by
  refine shift_ruleOk hp (cop := .ishl) rfl rfl hp.t2387 term_2387_kind rfl rfl
    (fun _ x y => env2 (.value x) (.value y)) (fun w => w = 64) F isem MR env cp hMR ?_ ?_
  · intro ctx cfg ii info w x y st tr m env' s1 hi hhead _ hd _ hm
    by_cases h64 : w = 64
    · subst h64
      rw [match_1549 hp ctx st tr m hi hhead hd] at hm
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hm
      exact ⟨hm.1.symm, hm.2.symm, rfl⟩
    · rw [match_1549_none hp ctx st tr m hi hhead h64 hd] at hm
      cases hm
  · intro f ctx hctx cfg x y w st tr n v s' hco hvb hw hW hP heval
    have hp' := hp
    cases hp
    isel_inv [*, rule_lower_1549] at heval
    have hrx := ‹ctx.valueReg? x = some _›
    have hDo := ‹ApplyInternal _ _ _ _ 27 703 _ _ _ _›
    have hOut := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    obtain rfl := hctx.valueReg x _ hrx
    have hs := do_shift_ok hp' hco hR hctx (by omega) (k := 18) (op := .lsl) (.inl ⟨rfl, rfl⟩) (by simp [IW])
      (hvb x _ hrx) hDo
    obtain ⟨ms2, d, rfl, hsh, hsem⟩ := shift_compose (ms1 := []) hctx hvb (by simp)
      (Nat.le_refl _) (by simp) (by simp) (.inl rfl) hs
    obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hOut
    refine ⟨[] ++ ms2, d, rfl, by rw [hst]; exact hsh, ?_⟩
    intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
    cases ty <;> simp [Clif.Ty.width] at hty
    obtain ⟨ρ', hrun, hD⟩ := hsem fr ρ ρ yv (prun_nil _) (fun _ _ => rfl) hvals hdfg hy
    refine ⟨ρ', hrun, ?_⟩
    simp only [Clif.Sem.shift, Clif.Sem.ishl, Clif.Sem.shiftAmt, Option.some.injEq] at hres
    subst hres
    exact fin_lsl (szOf 64) (Nat.le_refl _) (hvals x _ hx) hD

set_option maxHeartbeats 1000000 in
/-- **`ushr_fits_in_32`** (`lower.isle:1638`), i8..i32. -/
theorem ushr_fits_in_32_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1638 := by
  refine shift_ruleOk hp (cop := .ushr) rfl rfl hp.t2388 term_2388_kind rfl rfl
    (fun w x y => env3 (.ty (.int w)) (.value x) (.value y)) (fun w => w ≤ 32) F isem MR env cp hMR ?_ ?_
  · intro ctx cfg ii info w x y st tr m env' s1 hi hhead _ hd _ hm
    by_cases h32 : w ≤ 32
    · rw [match_1638 hp ctx st tr m hi hhead h32 hd] at hm
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hm
      exact ⟨hm.1.symm, hm.2.symm, h32⟩
    · rw [match_1638_none hp ctx st tr m hi hhead h32 hd] at hm
      cases hm
  · intro f ctx hctx cfg x y w st tr n v s' hco hvb hw hW hP heval
    have hp' := hp
    cases hp
    isel_inv [*, rule_lower_1638] at heval
    have hZ := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
    have hDo := ‹ApplyInternal _ _ _ _ 27 703 _ _ _ _›
    have hOut := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have hE := zext32_ok hp' hco (by omega) hZ
    obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
      extOut_prun hR hctx hvb (.inl rfl) (by simp) (by simp) hE
    have hs := do_shift_ok hp' hco hR hctx (by omega) (k := 16) (op := .lsr) (.inr (.inl ⟨rfl, rfl⟩)) hW hklt hDo
    obtain ⟨ms2, d, rfl, hsh, hsem⟩ := shift_compose hctx hvb hem hmono hdefs huses hkx hs
    obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hOut
    refine ⟨ms1 ++ ms2, d, rfl, by rw [hst]; exact hsh, ?_⟩
    intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
    subst hty
    obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr ρ ⟨_, u⟩ (hvals x _ hx) hdfg hx
    obtain ⟨ρ', hrun, hD⟩ := hsem fr ρ ρ1 yv hr1 hfr hvals hdfg hy
    refine ⟨ρ', hrun, ?_⟩
    simp only [Clif.Sem.shift, Clif.Sem.ushr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
    subst hres
    have hsz : szOf ty.width = .size32 := by simp [szOf, hP]
    rw [hsz] at hD
    have hA := hext.2 hP
    simp only [Bool.false_eq_true, ↓reduceIte] at hA
    exact fin_lsr .size32 (by simp [OperandSize.bits]; omega) hA hD

set_option maxHeartbeats 1000000 in
/-- **`ushr_64`** (`lower.isle:1642`), i64. -/
theorem ushr_64_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1642 := by
  refine shift_ruleOk hp (cop := .ushr) rfl rfl hp.t2388 term_2388_kind rfl rfl
    (fun _ x y => env2 (.value x) (.value y)) (fun w => w = 64) F isem MR env cp hMR ?_ ?_
  · intro ctx cfg ii info w x y st tr m env' s1 hi hhead _ hd _ hm
    by_cases h64 : w = 64
    · subst h64
      rw [match_1642 hp ctx st tr m hi hhead hd] at hm
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hm
      exact ⟨hm.1.symm, hm.2.symm, rfl⟩
    · rw [match_1642_none hp ctx st tr m hi hhead h64 hd] at hm
      cases hm
  · intro f ctx hctx cfg x y w st tr n v s' hco hvb hw hW hP heval
    have hp' := hp
    cases hp
    isel_inv [*, rule_lower_1642] at heval
    have hZ := ‹ApplyInternal _ _ _ _ 27 558 _ _ _ _›
    have hDo := ‹ApplyInternal _ _ _ _ 27 703 _ _ _ _›
    have hOut := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have hE := zext64_ok hp' hco (by omega) hZ
    obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
      extOut_prun hR hctx hvb (.inr rfl) (by simp) (by simp) hE
    have hs := do_shift_ok hp' hco hR hctx (by omega) (k := 16) (op := .lsr) (.inr (.inl ⟨rfl, rfl⟩)) (by simp [IW]) hklt hDo
    obtain ⟨ms2, d, rfl, hsh, hsem⟩ := shift_compose hctx hvb hem hmono hdefs huses hkx hs
    obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hOut
    refine ⟨ms1 ++ ms2, d, rfl, by rw [hst]; exact hsh, ?_⟩
    intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
    cases ty <;> simp [Clif.Ty.width] at hty
    obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr ρ ⟨_, u⟩ (hvals x _ hx) hdfg hx
    obtain ⟨ρ', hrun, hD⟩ := hsem fr ρ ρ1 yv hr1 hfr hvals hdfg hy
    refine ⟨ρ', hrun, ?_⟩
    simp only [Clif.Sem.shift, Clif.Sem.ushr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
    subst hres
    have hX := hext.1
    simp only [VHolds] at hX
    exact fin_lsr .size64 (Nat.le_refl _) (hA64 hX) hD

set_option maxHeartbeats 1000000 in
/-- **`sshr_fits_in_32`** (`lower.isle:1695`), i8..i32. -/
theorem sshr_fits_in_32_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1695 := by
  refine shift_ruleOk hp (cop := .sshr) rfl rfl hp.t2389 term_2389_kind rfl rfl
    (fun w x y => env3 (.ty (.int w)) (.value x) (.value y)) (fun w => w ≤ 32) F isem MR env cp hMR ?_ ?_
  · intro ctx cfg ii info w x y st tr m env' s1 hi hhead _ hd _ hm
    by_cases h32 : w ≤ 32
    · rw [match_1695 hp ctx st tr m hi hhead h32 hd] at hm
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hm
      exact ⟨hm.1.symm, hm.2.symm, h32⟩
    · rw [match_1695_none hp ctx st tr m hi hhead h32 hd] at hm
      cases hm
  · intro f ctx hctx cfg x y w st tr n v s' hco hvb hw hW hP heval
    have hp' := hp
    cases hp
    isel_inv [*, rule_lower_1695] at heval
    have hZ := ‹ApplyInternal _ _ _ _ 27 555 _ _ _ _›
    have hDo := ‹ApplyInternal _ _ _ _ 27 703 _ _ _ _›
    have hOut := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have hE := sext32_ok hp' hco (by omega) hZ
    obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
      extOut_prun hR hctx hvb (.inl rfl) (by simp) (by simp) hE
    have hs := do_shift_ok hp' hco hR hctx (by omega) (k := 17) (op := .asr) (.inr (.inr ⟨rfl, rfl⟩)) hW hklt hDo
    obtain ⟨ms2, d, rfl, hsh, hsem⟩ := shift_compose hctx hvb hem hmono hdefs huses hkx hs
    obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hOut
    refine ⟨ms1 ++ ms2, d, rfl, by rw [hst]; exact hsh, ?_⟩
    intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
    subst hty
    obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr ρ ⟨_, u⟩ (hvals x _ hx) hdfg hx
    obtain ⟨ρ', hrun, hD⟩ := hsem fr ρ ρ1 yv hr1 hfr hvals hdfg hy
    refine ⟨ρ', hrun, ?_⟩
    simp only [Clif.Sem.shift, Clif.Sem.sshr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
    subst hres
    have hsz : szOf ty.width = .size32 := by simp [szOf, hP]
    rw [hsz] at hD
    have hA := hext.2 hP
    simp only [Bool.false_eq_true, ↓reduceIte] at hA
    exact fin_asr .size32 (by simp [OperandSize.bits]; omega) hA hD

set_option maxHeartbeats 1000000 in
/-- **`sshr_64`** (`lower.isle:1699`), i64. -/
theorem sshr_64_ok {p : Program} (hp : Data p) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1699 := by
  refine shift_ruleOk hp (cop := .sshr) rfl rfl hp.t2389 term_2389_kind rfl rfl
    (fun _ x y => env2 (.value x) (.value y)) (fun w => w = 64) F isem MR env cp hMR ?_ ?_
  · intro ctx cfg ii info w x y st tr m env' s1 hi hhead _ hd _ hm
    by_cases h64 : w = 64
    · subst h64
      rw [match_1699 hp ctx st tr m hi hhead hd] at hm
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hm
      exact ⟨hm.1.symm, hm.2.symm, rfl⟩
    · rw [match_1699_none hp ctx st tr m hi hhead h64 hd] at hm
      cases hm
  · intro f ctx hctx cfg x y w st tr n v s' hco hvb hw hW hP heval
    have hp' := hp
    cases hp
    isel_inv [*, rule_lower_1699] at heval
    have hZ := ‹ApplyInternal _ _ _ _ 27 557 _ _ _ _›
    have hDo := ‹ApplyInternal _ _ _ _ 27 703 _ _ _ _›
    have hOut := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have hE := sext64_ok hp' hco (by omega) hZ
    obtain ⟨k, ms1, rfl, hem, hmono, hdefs, huses, hkx, hklt, hsem1⟩ :=
      extOut_prun hR hctx hvb (.inr rfl) (by simp) (by simp) hE
    have hs := do_shift_ok hp' hco hR hctx (by omega) (k := 17) (op := .asr) (.inr (.inr ⟨rfl, rfl⟩)) (by simp [IW]) hklt hDo
    obtain ⟨ms2, d, rfl, hsh, hsem⟩ := shift_compose hctx hvb hem hmono hdefs huses hkx hs
    obtain ⟨rfl, hst⟩ := output_reg_ok hp' hco (by omega) hOut
    refine ⟨ms1 ++ ms2, d, rfl, by rw [hst]; exact hsh, ?_⟩
    intro ty hty hety fr ρ u yv res _ hvals hdfg hx hy hres
    cases ty <;> simp [Clif.Ty.width] at hty
    obtain ⟨ρ1, hr1, hfr, hext⟩ := hsem1 fr ρ ⟨_, u⟩ (hvals x _ hx) hdfg hx
    obtain ⟨ρ', hrun, hD⟩ := hsem fr ρ ρ1 yv hr1 hfr hvals hdfg hy
    refine ⟨ρ', hrun, ?_⟩
    simp only [Clif.Sem.shift, Clif.Sem.sshr, Clif.Sem.shiftAmt, Option.some.injEq] at hres
    subst hres
    have hX := hext.1
    simp only [VHolds] at hX
    exact fin_asr .size64 (Nat.le_refl _) (hA64s hX) hD

end Rules

end Backend.Proof

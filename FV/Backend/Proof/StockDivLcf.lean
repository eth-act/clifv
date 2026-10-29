module

public import FV.Backend.Proof.StockDivMovK

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
theorem stock_div_movK_val {sz : OperandSize} {a : CV} {run b j : Nat} (ha : lo64 a = BitVec.ofNat 64 run)
    (hr : run < 2 ^ sz.bits) (hb : b < 2 ^ 16) (hj : j < sz.bits / 16) :
    lo64 (resX sz (movKVal (opnd sz a) ⟨b, j⟩)) = BitVec.ofNat 64 (replace16 run b j) := by
  have hn : Wid sz.bits := by cases sz <;> first | exact .inl rfl | exact .inr rfl
  rw [opnd_of_lo64 ha]
  have hy : (BitVec.ofNat 16 b).toNat = b := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  conv => lhs; rw [← hy]
  rw [stock_div_movK_ident hn hj]
  apply BitVec.eq_of_toNat_eq
  rw [lo64_resX_toNat]
  have hrl : replace16 run b j < 2 ^ sz.bits := replace16_lt hn hr hb hj
  generalize sz.bits = n at *
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    replace16, slice16] at hrl ⊢
  rcases hn with rfl | rfl
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one, Nat.mul_one] at *; omega
  · obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    all_goals simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one, Nat.mul_one] at *; omega

section Loop
variable {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
theorem stock_div_lcf_step (hR : Refines F isem) {st0 : LState} {value first j : Nat} {size : OperandSize}
    (hn : Wid size.bits) (hj : j < size.bits / 16) {acc : Reg × LState × Nat}
    (h : LcfInv F isem st0 value first size.bits j acc) :
    LcfInv F isem st0 value first size.bits (j + 1) (lcfStep value first size acc j) := by
  obtain ⟨rd, st, run⟩ := acc
  obtain ⟨ms, d, hd, hsh, hdlt, hlt, hsl, hrun⟩ := h
  dsimp only at hd hsh hdlt hlt hsl hrun
  subst hd
  unfold lcfStep
  split
  · exact ⟨ms, d, rfl, hsh, hdlt, hlt, fun i hi h' => hsl i hi (by omega), hrun⟩
  · rename_i hjf
    dsimp only
    have hb := slice16_lt value j
    split
    · refine ⟨ms ++ [.movK (.vreg st.nextVreg .int) (.vreg d .int) ⟨slice16 value j, j⟩ size],
        st.nextVreg, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, by simp [LState.emit, LState.fresh],
        replace16_lt hn hlt hb hj, ?_, ?_⟩
      · simp [LState.emit, LState.fresh, hsh.emitted]
      · have := hsh.mono; simp only [LState.emit, LState.fresh]; omega
      · exact hsh.mono
      · intro mi hmi e he
        simp only [List.mem_append, List.mem_singleton] at hmi
        rcases hmi with hmi | rfl
        · have := hsh.defs mi hmi e he; simp only [LState.emit, LState.fresh]; omega
        · have : vdefs (.movK (.vreg st.nextVreg .int) (.vreg d .int) ⟨slice16 value j, j⟩ size) =
              [st.nextVreg] := rfl
          rw [this, List.mem_singleton] at he; subst he
          have := hsh.mono; simp only [LState.emit, LState.fresh]; omega
      · intro mi hmi u hu
        simp only [List.mem_append, List.mem_singleton] at hmi
        rcases hmi with hmi | rfl
        · exact hsh.uses mi hmi u hu
        · have : vuseNums (.movK (.vreg st.nextVreg .int) (.vreg d .int) ⟨slice16 value j, j⟩
              size) = [d] := rfl
          rw [this, List.mem_singleton] at hu; subst hu
          exact .inl hsh.res
      · intro i hi h'
        rw [slice16_replace16 hn hlt hb hj hi]
        split
        · subst_vars; rfl
        · exact hsl i hi (by omega)
      · intro ρ
        obtain ⟨ρ', hp, hv⟩ := hrun ρ
        have h16 : (⟨slice16 value j, j⟩ : MoveWideConst).bits < 2 ^ 16 ∧
            16 * (⟨slice16 value j, j⟩ : MoveWideConst).shift < size.bits :=
          ⟨hb, by simp only; omega⟩
        refine ⟨_, prun_append hp (prun_movk hR rfl (fun w => ispec_movK h16 w) (prun_nil _)), ?_⟩
        rw [upd_same]
        exact stock_div_movK_val hv hlt hb hj
    · rename_i heq
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
      refine ⟨ms, d, rfl, hsh, hdlt, hlt, fun i hi h' => ?_, hrun⟩
      by_cases hij : i = j
      · subst hij; exact heq.symm
      · exact hsl i hi (by omega)

theorem stock_div_lcf_fold (hR : Refines F isem) {st0 : LState} {value first : Nat} {size : OperandSize}
    (hn : Wid size.bits) {init : Reg × LState × Nat}
    (h0 : LcfInv F isem st0 value first size.bits 0 init) :
    ∀ j, j ≤ size.bits / 16 →
      LcfInv F isem st0 value first size.bits j ((List.range j).foldl (lcfStep value first size) init)
  | 0, _ => h0
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append]
    exact stock_div_lcf_step hR hn (by omega) (stock_div_lcf_fold hR hn h0 j (by omega))

/-- **`load_constant_full`**: the emitted code has `CodeShape` (fresh defs, no outside uses) and
every run leaves `lcfValue …` in the result vreg. -/
theorem stock_div_lcf_run (hR : Refines F isem) (bits : Nat) (sg : Bool) (sz : OperandSize) (v : Nat)
    (st : LState) :
    ∃ ms d, (loadConstantFull bits sg sz v st).1 = .vreg d .int ∧
      CodeShape st (loadConstantFull bits sg sz v st).2 ms d st.nextVreg ∧
      ∀ ρ, ∃ ρ', PRun F isem ms ρ ρ' ∧ lo64 (ρ' d) = BitVec.ofNat 64 (lcfValue bits sg sz v) := by
  rw [lcf_eq]
  dsimp only
  have hv64 := lcfValue_lt bits sg sz v
  generalize lcfValue bits sg sz v = value at *
  obtain ⟨hn, hv⟩ := lcfSize_spec value hv64
  generalize lcfSize value = size at *
  obtain ⟨hf, hc1, hcs, base, hbase, hceq⟩ := lcfFirst_spec size hn hv
  generalize lcfFirst value size = c at *
  obtain ⟨hi1, hi2, hival⟩ := movWide_first hn c.2.1 hbase (slice16_lt value c.2.2) hf
  have hn64 : 2 ^ size.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (opSize_bits_le size)
  have h0 : LcfInv F isem st value c.2.2 size.bits 0
      ((st.fresh .int).1, (st.fresh .int).2.emit (.movWide c.2.1 (st.fresh .int).1
        ⟨match c.2.1 with
          | .movZ => slice16 value c.2.2
          | .movN => 2 ^ 16 - 1 - slice16 value c.2.2, c.2.2⟩ size), c.1) := by
    refine ⟨[.movWide c.2.1 (.vreg st.nextVreg .int) ⟨match c.2.1 with
          | .movZ => slice16 value c.2.2
          | .movN => 2 ^ 16 - 1 - slice16 value c.2.2, c.2.2⟩ size], st.nextVreg, rfl,
      ⟨by simp [LState.emit, LState.fresh], by simp [LState.emit, LState.fresh], Nat.le_refl _, ?_, ?_⟩,
      by simp [LState.emit, LState.fresh], hc1, fun i hi h' => hcs i hi (by omega), ?_⟩
    · intro mi hmi e he
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [vdd_movWide, List.mem_singleton] at he; subst he
      simp [LState.emit, LState.fresh]
    · intro mi hmi u hu
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [vdu_movWide] at hu; cases hu
    · intro ρ
      refine ⟨_, prun_r0 hR rfl (fun w => ispec_movWide ⟨hi1, hi2⟩ w) (prun_nil _), ?_⟩
      rw [upd_same]
      apply BitVec.eq_of_toNat_eq
      rw [lo64_resX_toNat, hival, ← hceq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hc1 hn64)]
  have hK := stock_div_lcf_fold hR hn h0 (size.bits / 16) (Nat.le_refl _)
  obtain ⟨ms, d, hd, hsh, -, hlt, hsl, hrun⟩ := hK
  refine ⟨ms, d, hd, hsh, fun ρ => ?_⟩
  obtain ⟨ρ', hp, hval⟩ := hrun ρ
  refine ⟨ρ', hp, ?_⟩
  rw [hval, eq_of_slice16 hn hlt hv (fun i hi => hsl i hi (.inr hi))]
end Loop
end Backend.Stock.Proof.ScalarDiv

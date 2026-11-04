import FV.Backend.Asm

/-!
# `loadConst64` (Cranelift's `Inst::load_constant`): its cases and its shape

The facts about `loadConst64` (`FV/Backend/Asm.lean`) that do not need the Arm model, in a low
module so that the files with per-line lemmas about it can import it:

* `loadConst64_cases`: the four cases of `Inst::load_constant` (`movz`, `movn`,
  `orr _, xzr, #_`, the general `movz`/`movn` + `movk` sequence);
* `loadConst64_form`, **the shape**: every line is an instruction without a trap code, a
  `movz`/`movn`, `movk` or `orr _, xzr, #_` (`LcForm`) to the destination register. The
  per-line lemmas (`loadConst64_form`, `loadConst64_free`, `loadConst64_noCall`, ...) follow from
  it alone;
* `loadConst64_ne_nil`, `movSeqLines_length` (for `loadConst64_length`), `lines_orr_xzr` (case 3
  is what `MInst.lines` emits for Cranelift's `AluRRImmLogic` `orr` with `rn = zero_reg()`);
* the halfword facts (`mwc_spec`, `halfword_compl`, `mem_kept`, `general_ne`) that the semantic
  proof `steps_loadConst64` (`FV/Backend/Proof/RegallocMem.lean`) uses.
-/

namespace Backend.Proof
open Backend

namespace LoadConstant

theorem halfword_lt (v j : Nat) : halfword v j < 2 ^ 16 := Nat.mod_lt _ (by decide)

/-- `MoveWideConst::maybe_from_u64(u) = Some(imm)`: `u` is `imm.bits` in halfword
`imm.shift`. -/
theorem mwc_spec {u : Nat} {imm : MoveWideConst} (hu : u < 2 ^ 64)
    (h : MoveWideConst.ofNat? u = some imm) :
    imm.bits < 2 ^ 16 ∧ imm.shift < 4 ∧
      ∀ j < 4, halfword u j = if j = imm.shift then imm.bits else 0 := by
  have hm : mask64 u = u := Nat.mod_eq_of_lt hu
  unfold MoveWideConst.ofNat? at h
  rw [hm] at h
  dsimp only at h
  simp only [Nat.reducePow] at hu
  split at h
  · cases h; simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  split at h
  · cases h; rename_i h1 h2; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  split at h
  · cases h; rename_i h1 h2 h3; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  split at h
  · cases h; rename_i h1 h2 h3 h4; simp only [beq_iff_eq] at h4
    simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  · cases h

theorem halfword_compl {u j : Nat} (hu : u < 2 ^ 64) (hj : j < 4) :
    halfword (2 ^ 64 - 1 - u) j = 2 ^ 16 - 1 - halfword u j := by
  simp only [Nat.reducePow] at hu
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [halfword] <;> omega

theorem mem_kept {v n ig : Nat} {p : Nat × Nat} :
    p ∈ keptHalfwords v n ig ↔ p.1 < n ∧ halfword v p.1 ≠ ig ∧ p.2 = halfword v p.1 := by
  obtain ⟨i, c⟩ := p
  simp only [keptHalfwords, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨a, ha, h⟩
    split at h
    · cases h
    · rename_i hne; cases h; simp only [beq_iff_eq] at hne; exact ⟨ha, hne, rfl⟩
  · rintro ⟨ha, hne, rfl⟩
    exact ⟨i, ha, by simp [hne]⟩

theorem kept_nil {v n ig : Nat} (h : keptHalfwords v n ig = []) : ∀ j < n, halfword v j = ig := by
  intro j hj
  refine Classical.byContradiction fun hne => ?_
  have : (j, halfword v j) ∈ keptHalfwords v n ig := mem_kept.2 ⟨hj, hne, rfl⟩
  rw [h] at this; cases this

/-- The general case is reached only with a kept halfword: all halfwords ignored would make
`value` `0`, `2^64 - 1` (cases 1, 2) or `2^32 - 1` (a bitmask immediate, case 3). -/
theorem general_ne {v n ig : Nat} (hv : v < 2 ^ 64) (h1 : MoveWideConst.ofNat? v = none)
    (h2 : MoveWideConst.ofNat? (2 ^ 64 - 1 - v) = none) (h3 : ImmLogic.ofNat? v .size64 = none)
    (is64 inv : Bool) (hn : n = if is64 then 4 else 2) (hig : ig = if inv then 2 ^ 16 - 1 else 0)
    (hv32 : is64 = false → v < 2 ^ 32) : keptHalfwords v n ig ≠ [] := by
  intro hk
  have h := kept_nil hk
  subst hn hig
  simp only [Nat.reducePow] at hv hv32
  cases is64 <;> cases inv <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide); have := hv32 rfl
    simp [halfword] at e0 e1
    have : v = 0 := by omega
    subst this; simp [MoveWideConst.ofNat?, mask64] at h1
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide); have := hv32 rfl
    simp [halfword] at e0 e1
    have : v = 2 ^ 32 - 1 := by omega
    subst this; revert h3; decide
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide)
    have e2 := h 2 (by decide); have e3 := h 3 (by decide)
    simp [halfword] at e0 e1 e2 e3
    have : v = 0 := by omega
    subst this; simp [MoveWideConst.ofNat?, mask64] at h1
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide)
    have e2 := h 2 (by decide); have e3 := h 3 (by decide)
    simp [halfword] at e0 e1 e2 e3
    have : 2 ^ 64 - 1 - v = 0 := by omega
    rw [this] at h2; simp [MoveWideConst.ofNat?, mask64] at h2

theorem mask64_lt' (v : Nat) : mask64 v < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem mask64_mask64 (v : Nat) : mask64 (mask64 v) = mask64 v := Nat.mod_eq_of_lt (mask64_lt' v)

/-- `ImmLogic::maybe_from_u64(u, I64) = Some(imml)`: `imml` holds `u` itself. -/
theorem immLogic_eq {u : Nat} {i : ImmLogic} (h : ImmLogic.ofNat? u .size64 = some i) :
    i = ⟨u, .size64⟩ := by
  unfold ImmLogic.ofNat? at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

theorem movSeqLines_length (rd : Reg) (is64 inv : Bool) :
    ∀ ks : List (Nat × Nat), (movSeqLines rd is64 inv ks).length = ks.length
  | [] => rfl
  | _ :: _ => by simp [movSeqLines]

theorem ite_movWide (b : Prop) [Decidable b] (w : Bool) (rd : Reg) (x y : MoveWideConst) :
    ∃ op w' imm, (if b then Insn.movWide .movN w rd x else .movWide .movZ w rd y) =
      .movWide op w' rd imm := by
  by_cases h : b <;> simp [h]

/-- Case 3 emits what `MInst.lines` emits for Cranelift's
`AluRRImmLogic { alu_op: Orr, size: Size64, rd, rn: zero_reg(), imml }`. -/
theorem lines_orr_xzr (c : FnCtx) (ps : PState) (rd : Reg) {v : Nat} {i : ImmLogic}
    (h : ImmLogic.ofNat? v .size64 = some i) :
    MInst.lines c (.aluRRImmLogic .orr .size64 rd .xzr i) ps =
      .ok ([.ins (.logicImm .orr true rd .xzr (mask64 v))], ps) := by
  rw [immLogic_eq h]
  rfl

end LoadConstant

open LoadConstant

/-- `loadConst64` by cases. -/
theorem loadConst64_cases (rd : Reg) (v : Nat) :
    (∃ imm, MoveWideConst.ofNat? (mask64 v) = some imm ∧
      loadConst64 rd v = [.ins (.movWide .movZ true rd imm)]) ∨
    (MoveWideConst.ofNat? (mask64 v) = none ∧ ∃ imm,
      MoveWideConst.ofNat? (2 ^ 64 - 1 - mask64 v) = some imm ∧
      loadConst64 rd v = [.ins (.movWide .movN true rd imm)]) ∨
    (∃ i, ImmLogic.ofNat? (mask64 v) .size64 = some i ∧
      loadConst64 rd v = [.ins (.logicImm .orr true rd .xzr (mask64 v))]) ∨
    (MoveWideConst.ofNat? (mask64 v) = none ∧
      MoveWideConst.ofNat? (2 ^ 64 - 1 - mask64 v) = none ∧
      ImmLogic.ofNat? (mask64 v) .size64 = none ∧
      loadConst64 rd v = generalLines rd (mask64 v)) := by
  unfold loadConst64
  dsimp only
  rcases h1 : MoveWideConst.ofNat? (mask64 v) with _ | imm
  · rcases h2 : MoveWideConst.ofNat? (2 ^ 64 - 1 - mask64 v) with _ | imm
    · rcases h3 : ImmLogic.ofNat? (mask64 v) .size64 with _ | i
      · exact .inr (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩))
      · exact .inr (.inr (.inl ⟨i, rfl, rfl⟩))
    · exact .inr (.inl ⟨rfl, imm, rfl, rfl⟩)
  · exact .inl ⟨imm, rfl, rfl⟩

/-- The instruction forms of `loadConst64 rd v`: `movz`/`movn`, `movk` or `orr _, xzr, #_`,
all with destination `rd`. -/
def LcForm (rd : Reg) (i : Insn) : Prop :=
  (∃ op w imm, i = .movWide op w rd imm) ∨ (∃ w imm, i = .movk w rd imm) ∨
    ∃ val, i = .logicImm .orr true rd .xzr val

/-- **The shape of `loadConst64`**: every line is an instruction without a trap code, of one
of the `LcForm` forms. The per-line lemmas about `loadConst64` follow from this alone. -/
theorem loadConst64_form {rd : Reg} {v : Nat} {ln : Line} (h : ln ∈ loadConst64 rd v) :
    ∃ i, ln = .ins i none ∧ LcForm rd i := by
  rcases loadConst64_cases rd v with ⟨_, -, e⟩ | ⟨-, _, -, e⟩ | ⟨_, -, e⟩ | ⟨-, -, -, e⟩ <;>
    rw [e] at h
  · simp only [List.mem_singleton] at h; exact ⟨_, h, .inl ⟨_, _, _, rfl⟩⟩
  · simp only [List.mem_singleton] at h; exact ⟨_, h, .inl ⟨_, _, _, rfl⟩⟩
  · simp only [List.mem_singleton] at h; exact ⟨_, h, .inr (.inr ⟨_, rfl⟩)⟩
  · unfold generalLines at h
    dsimp only at h
    generalize keptHalfwords _ _ _ = ks at h
    cases ks with
    | nil => cases h
    | cons p R =>
      simp only [movSeqLines, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨q, -, rfl⟩
      · exact ⟨_, rfl, .inl (ite_movWide _ _ _ _ _)⟩
      · exact ⟨_, rfl, .inr (.inl ⟨_, _, rfl⟩)⟩

/-- `loadConst64` is never empty. -/
theorem loadConst64_ne_nil (rd : Reg) (v : Nat) : loadConst64 rd v ≠ [] := by
  rcases loadConst64_cases rd v with ⟨_, -, e⟩ | ⟨-, _, -, e⟩ | ⟨_, -, e⟩ |
    ⟨h1, h2, h3, e⟩ <;> rw [e] <;> try simp
  unfold generalLines
  dsimp only
  have := general_ne (mask64_lt' v) h1 h2 h3 (decide (2 ^ 32 ≤ mask64 v))
    (decide (countZeroHalfWords (mask64 v) (if decide (2 ^ 32 ≤ mask64 v) = true then 4 else 2) <
      countZeroHalfWords (if decide (2 ^ 32 ≤ mask64 v) = true then 2 ^ 64 - 1 - mask64 v
        else 2 ^ 32 - 1 - mask64 v) (if decide (2 ^ 32 ≤ mask64 v) = true then 4 else 2)))
    rfl rfl (fun h => by simpa using h)
  revert this
  generalize keptHalfwords _ _ _ = ks
  intro h
  cases ks with
  | nil => exact absurd rfl h
  | cons _ _ => simp [movSeqLines]

end Backend.Proof

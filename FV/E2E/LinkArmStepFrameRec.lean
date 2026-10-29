module

public import FV.E2E.LinkArmStepX30

@[expose] public section

/-!
# The lines that name `x30`: the frame record and `ret` (SEM1, `docs/plans/uninit.md` §5.8 (1))

Besides `bl`/`blr` (hooked lines), the backend's code names `x30` only in the frame-record pair
of the prologue and epilogue and in `ret` (`GprFoot.gprFree_exec_inst` covers every other
instruction). From two states equal but for `x30` and memory in `Z` (`StEqOutX Z`):

* `stEqOutX_stpFR`: `stp x29, x30, [sp, #off]!` keeps `StEqOutX` up to the stored `x30`, the
  high 8 bytes of the record (`HiBytes A 8 16`, `A` the new `sp`);
* `stEqOutX_ldpFR`: `ldp x29, x30, [sp], #off` keeps `StEqOutX Z` when the low 8 bytes of the
  record (the saved `x29`) are outside `Z`: `x29` is reloaded from equal bytes, `x30` may differ;
* `stEqOutX_ret`: after `ret` the states agree on every register but `x30` and the pc (the
  register part of `RetAgree`), and on the memory outside `Z`.

Helpers: `HiBytes`, `byte_cast_append_lo`, `writeM_eq_lo`, `stEqOutX_write_mem_bytes_append`,
`readM_lo_congr`, `stEqOutX_w30`.
-/

namespace E2E

open Arm Backend Backend.Proof Concurrency.ArmFoot Concurrency.ArmThread GprFoot

/-- The bytes `A + k` for `lo ≤ k < n`. -/
def HiBytes (A : BitVec 64) (lo n : Nat) (a : BitVec 64) : Prop :=
  ∃ k, lo ≤ k ∧ k < n ∧ A + BitVec.ofNat 64 k = a

theorem byte_cast_append_lo {D N : Nat} (x y : BitVec D) (hc : D + D = N * 8) {k : Nat}
    (hk : 8 * k + 8 ≤ D) :
    (BitVec.cast hc (x ++ y)).extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and, show 8 * k + i < D from by omega, ite_true]

/-- Two writes whose low `lo` bytes agree give memories that agree outside the high bytes. -/
theorem writeM_eq_lo {N : Nat} (hN : N ≤ 2 ^ 64) (A : BitVec 64) (v v' : BitVec (N * 8))
    (m m' : Memory) (lo : Nat) (hv : ∀ k < lo, k < N → v.extractLsb' (8 * k) 8 = v'.extractLsb' (8 * k) 8)
    (a : BitVec 64) (ha : ¬ HiBytes A lo N a) (hm : m a = m' a) :
    writeM N A v m a = writeM N A v' m' a := by
  by_cases hin : ∃ k < N, A + BitVec.ofNat 64 k = a
  · obtain ⟨k, hk, rfl⟩ := hin
    rw [writeM_apply_in _ _ _ _ _ hN hk, writeM_apply_in _ _ _ _ _ hN hk]
    by_cases hkl : k < lo
    · exact hv k hkl hk
    · exact absurd ⟨k, by omega, hk, rfl⟩ ha
  · have hout : ∀ k < N, A + BitVec.ofNat 64 k ≠ a := fun k hk e => hin ⟨k, hk, e⟩
    rw [writeM_apply_out _ _ _ _ _ hout, writeM_apply_out _ _ _ _ _ hout]; exact hm

/-- **Storing two values that agree in their low part**: the memories agree outside `Z` and the
high bytes. -/
theorem stEqOutX_write_mem_bytes_append {Z : BitVec 64 → Prop} {s t : ArmState}
    (h : StEqOutX Z s t) {D N : Nat} (hN : N ≤ 2 ^ 64) (hc : D + D = N * 8) (A : BitVec 64)
    (x x' y : BitVec D) (lo : Nat) (hlo : 8 * lo ≤ D) :
    StEqOutX (fun a => Z a ∨ HiBytes A lo N a) (write_mem_bytes N A (BitVec.cast hc (x ++ y)) s)
      (write_mem_bytes N A (BitVec.cast hc (x' ++ y)) t) := by
  rw [write_mem_bytes_eq, write_mem_bytes_eq]
  refine ⟨fun f hf => ?_, ?_, fun a ha => ?_⟩
  · rw [Concurrency.ArmFoot.r_setMem, Concurrency.ArmFoot.r_setMem]; exact h.1 f hf
  · simp only [setMem_program]; exact h.2.1
  · simp only [setMem_mem]
    refine writeM_eq_lo hN A _ _ _ _ lo (fun k hk _ => ?_) a (fun h' => ha (.inr h'))
      (h.2.2 a fun h' => ha (.inl h'))
    rw [byte_cast_append_lo _ _ _ (by omega), byte_cast_append_lo _ _ _ (by omega)]

/-- Two `x30` writes keep `StEqOutX`. -/
theorem stEqOutX_w30 {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t)
    (v v' : BitVec 64) : StEqOutX Z (Arm.w (.GPR 30#5) v s) (Arm.w (.GPR 30#5) v' t) := by
  refine ⟨fun f hf => ?_, ?_, fun x hx => ?_⟩
  · rw [r_of_w_different hf, r_of_w_different hf]; exact h.1 f hf
  · rw [Arm.w_program, Arm.w_program]; exact h.2.1
  · rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]; exact h.2.2 x hx

theorem read_gpr_eqX {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t) {i : BitVec 5}
    (hi : ¬ i = 30#5) (n : Nat) : read_gpr n i s = read_gpr n i t := by
  simp only [read_gpr, h.1 (.GPR i) (by simpa using hi)]

theorem checkSP_eqX {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t) :
    CheckSPAlignment s = CheckSPAlignment t := by
  simp only [CheckSPAlignment, read_gpr_eqX h (i := 31#5) (by decide)]

/-- The data size of a 64-bit general-purpose register pair, as the semantics computes it. -/
theorem pairWidth_eq : (8 <<< if (!decide ((0 : BitVec 1) = 1#1)) = true then
    2 + (BitVec.extractLsb' 1 1 (2 : BitVec 2)).toNat else 2 + BitVec.toNat (2 : BitVec 2)) = 64 := by
  decide

/-! ## `stp x29, x30, [sp, #off]!` -/

/-- `stp x29, x30, [sp, #(8 * imm7)]!` (64-bit store pair, pre-indexed). -/
def stpFR (imm7 : BitVec 7) : ArmInst :=
  .LDST (.Reg_pair_pre_indexed { opc := 2, V := 0, L := 0, imm7, Rt2 := 30, Rn := 31, Rt := 29 })

/-- The new `sp` of `stpFR` (the record's address). -/
def stpAddr (imm7 : BitVec 7) (t : ArmState) : BitVec 64 :=
  read_gpr 64 31 t + BitVec.signExtend 64 imm7 <<< 3

/-- **The frame-record store**: `StEqOutX` up to the stored `x30` (the record's high 8 bytes). -/
theorem stEqOutX_stpFR {Z : BitVec 64 → Prop} {s t : ArmState} (imm7 : BitVec 7)
    (h : StEqOutX Z s t) :
    StEqOutX (fun a => Z a ∨ HiBytes (stpAddr imm7 t) 8 16 a) (exec_inst (stpFR imm7) s)
      (exec_inst (stpFR imm7) t) := by
  have e31 : read_gpr 64 (31 : BitVec 5) s = read_gpr 64 31 t := read_gpr_eqX h (by decide) 64
  have epc : read_pc s = read_pc t := h.1 .PC (by simp)
  have eck := checkSP_eqX h
  simp only [stpFR, exec_inst, LDST.exec_reg_pair_pre_indexed, LDST.exec_reg_pair_common,
    LDST.reg_pair_operation, LDST.reg_pair_constrain_unpredictable, ldst_read, ldst_write]
  simp (config := { decide := true }) only [Bool.not_false, Bool.false_eq_true, decide_false,
    Bool.true_and, and_false, or_false, ite_false, ite_true, BitVec.lsb, true_and,
    show (BitVec.extractLsb' 1 1 (2 : BitVec 2)).toNat = 1 from rfl,
    show ((0 : BitVec 1) = 1#1) = False from by decide, Nat.reduceAdd, Nat.reduceShiftLeft,
    Nat.reduceDiv, Nat.reduceMul, decide_false, Bool.not_false, ↓reduceIte,
    BitVec.toNat_ofNat]
  rw [e31, epc]
  simp only [eck]
  simp (config := { decide := true }) only [read_gpr_zr, ne_eq, not_false_eq_true, ite_true,
    read_gpr_eqX h (i := 29) (by decide)]
  simp only [write_pc]
  apply stEqOutX_w
  split
  · exact (stEqOutX_write_err h _).mono fun a ha => .inl ha
  · simp only [write_gpr]
    apply stEqOutX_w
    refine StEqOutX.mono (stEqOutX_write_mem_bytes_append h (by decide +revert)
      (by decide +revert) _ _ _ _ 8 (by decide +revert))
      fun a ha => ha.imp id fun ⟨k, h1, h2, h3⟩ => ⟨k, h1, by have := pairWidth_eq; omega, ?_⟩
    rw [← h3]; rfl

/-! ## `ldp x29, x30, [sp], #off` -/

/-- `ldp x29, x30, [sp], #(8 * imm7)` (64-bit load pair, post-indexed). -/
def ldpFR (imm7 : BitVec 7) : ArmInst :=
  .LDST (.Reg_pair_post_indexed { opc := 2, V := 0, L := 1, imm7, Rt2 := 30, Rn := 31, Rt := 29 })

theorem readM_lo_congr {N D : Nat} (hD : D ≤ N * 8) (h8 : 8 ∣ D) (A : BitVec 64) (m m' : Memory)
    (hm : ∀ k, 8 * k < D → m (A + BitVec.ofNat 64 k) = m' (A + BitVec.ofNat 64 k)) :
    (readM N A m).extractLsb' 0 D = (readM N A m').extractLsb' 0 D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add]
  have hk := readM_byte N A m (i / 8) (by omega)
  have hk' := readM_byte N A m' (i / 8) (by omega)
  have e1 := congrArg (fun z => z.getLsbD (i % 8)) hk
  have e2 := congrArg (fun z => z.getLsbD (i % 8)) hk'
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i from by omega] at e1 e2
  rw [e1, e2]
  simp only [read_store, hm (i / 8) (by omega)]

/-- **The frame-record load**: `StEqOutX Z` is kept when the saved `x29` (the record's low 8
bytes) is outside `Z`; the reloaded `x30` may differ. -/
theorem stEqOutX_ldpFR {Z : BitVec 64 → Prop} {s t : ArmState} (imm7 : BitVec 7)
    (h : StEqOutX Z s t) (hlo : ∀ k < 8, ¬ Z (read_gpr 64 31 t + BitVec.ofNat 64 k)) :
    StEqOutX Z (exec_inst (ldpFR imm7) s) (exec_inst (ldpFR imm7) t) := by
  have e31 : read_gpr 64 (31 : BitVec 5) s = read_gpr 64 31 t := read_gpr_eqX h (by decide) 64
  have epc : read_pc s = read_pc t := h.1 .PC (by simp)
  have eck := checkSP_eqX h
  simp only [ldpFR, exec_inst, LDST.exec_reg_pair_post_indexed, LDST.exec_reg_pair_common,
    LDST.reg_pair_operation, LDST.reg_pair_constrain_unpredictable, ldst_read, ldst_write]
  simp (config := { decide := true }) only [Bool.not_false, Bool.false_eq_true, decide_false,
    Bool.true_and, and_false, or_false, ite_false, ite_true, BitVec.lsb, true_and,
    show (BitVec.extractLsb' 1 1 (2 : BitVec 2)).toNat = 1 from rfl,
    show ((0 : BitVec 1) = 1#1) = False from by decide, Nat.reduceAdd, Nat.reduceShiftLeft,
    Nat.reduceDiv, Nat.reduceMul, decide_false, Bool.not_false, ↓reduceIte,
    BitVec.toNat_ofNat]
  rw [e31, epc]
  simp only [eck]
  simp only [write_pc]
  apply stEqOutX_w
  split
  · exact stEqOutX_write_err h _
  · simp only [write_gpr]
    apply stEqOutX_w
    simp (config := { decide := true }) only [write_gpr_zr, ne_eq, not_false_eq_true, ite_true,
      write_gpr]
    apply stEqOutX_w30
    rw [read_mem_bytes_eq, read_mem_bytes_eq,
      readM_lo_congr (by decide +revert) (by decide +revert) _ s.mem t.mem fun k hk =>
        h.2.2 _ (hlo k (by
          have h64 : ∀ j, 8 * j < (8 <<< if (!decide ((0 : BitVec 1) = 1#1)) = true then
              2 + (BitVec.extractLsb' 1 1 (2 : BitVec 2)).toNat else 2 + BitVec.toNat (2 : BitVec 2))
              → j < 8 := by
            intro j hj
            have : (8 <<< if (!decide ((0 : BitVec 1) = 1#1)) = true then
              2 + (BitVec.extractLsb' 1 1 (2 : BitVec 2)).toNat else 2 + BitVec.toNat (2 : BitVec 2))
              = 64 := by decide
            omega
          exact h64 k hk))]
    exact stEqOutX_w h _ _

/-! ## `ret` -/

/-- `ret` (`br x30`'s return form). -/
def retI : ArmInst := .BR (.Uncond_branch_reg { opc := 2, op2 := 31, op3 := 0, Rn := 30, op4 := 0 })

/-- **`ret`**: the states agree on every register but `x30` and the pc, on the program, and on the
memory outside `Z`. -/
theorem stEqOutX_ret {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t) :
    (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → r f (exec_inst retI s) = r f (exec_inst retI t)) ∧
      (exec_inst retI s).program = (exec_inst retI t).program ∧
      ∀ a, ¬ Z a → (exec_inst retI s).mem a = (exec_inst retI t).mem a := by
  simp (config := { decide := true }) only [retI, exec_inst, BR.exec_uncond_branch_reg,
    ↓reduceIte, ite_false, ite_true]
  refine ⟨fun f hp h30 => ?_, ?_, fun a ha => ?_⟩
  · simp only [write_pc]
    rw [r_of_w_different hp, r_of_w_different hp]; exact h.1 f h30
  · simp only [write_pc]; rw [Arm.w_program, Arm.w_program]; exact h.2.1
  · simp only [write_pc]
    rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]; exact h.2.2 a ha

end E2E

module

public import FV.Arm.Exec

@[expose] public section

/-!
# Memory footprints of the Arm model's instructions (T2d, #302)

The per-thread event semantics (`FV/Concurrency/ArmThread.lean`) runs one thread of the Arm model
against a memory it does not own: a step reads the bytes of its footprint from the environment and
writes the bytes of its footprint to it. That is sound only if an instruction depends on and
changes the memory only through its accesses. This file proves it for the instruction classes of
the model (`FV/Arm/Exec.lean`):

* `exec_nonldst`: every instruction outside the load/store classes commutes with replacing the
  memory (`setMem`): it neither reads nor writes memory;
* `stepi_setMem`: hence a `stepi` at such an instruction (the fetch reads the program, not the
  memory);
* `read_mem_bytes_eq`, `write_mem_bytes_eq`: the byte accessors as functions of the memory alone
  (`readM`, `writeM`), the vocabulary of the footprints of the load/store instructions.

Plan: `docs/plans/atomics.md` (T2d).
-/

namespace Concurrency.ArmFoot

open Arm

/-- The state `s` with memory `m`. -/
def setMem (m : Memory) (s : ArmState) : ArmState := { s with mem := m }

@[simp] theorem setMem_mem (m : Memory) (s : ArmState) : (setMem m s).mem = m := rfl

theorem setMem_self (s : ArmState) : setMem s.mem s = s := rfl

theorem setMem_setMem (m m' : Memory) (s : ArmState) : setMem m (setMem m' s) = setMem m s := rfl

theorem setMem_program (m : Memory) (s : ArmState) : (setMem m s).program = s.program := rfl

theorem r_setMem (fld : StateField) (m : Memory) (s : ArmState) :
    r fld (setMem m s) = r fld s := by
  unfold setMem; cases fld <;> unfold r <;> rfl

theorem w_setMem (fld : StateField) (v : state_value fld) (m : Memory) (s : ArmState) :
    w fld v (setMem m s) = setMem m (w fld v s) := by
  unfold setMem; cases fld <;> unfold w <;> rfl

theorem w_mem (fld : StateField) (v : state_value fld) (s : ArmState) : (w fld v s).mem = s.mem := by
  cases fld <;> unfold w <;> rfl

theorem ite_setMem {c : Prop} [Decidable c] (m : Memory) (a b : ArmState) :
    (if c then setMem m a else setMem m b) = setMem m (if c then a else b) := by
  split <;> rfl

theorem dite_setMem {c : Prop} [Decidable c] (m : Memory) (a : c → ArmState) (b : ¬ c → ArmState) :
    (if h : c then setMem m (a h) else setMem m (b h)) = setMem m (if h : c then a h else b h) := by
  split <;> rfl

theorem fetch_inst_setMem (a : BitVec 64) (m : Memory) (s : ArmState) :
    fetch_inst a (setMem m s) = fetch_inst a s := by
  unfold fetch_inst; rfl

/-- An instruction semantics that neither reads nor writes memory. -/
def MemFree (f : ArmState → ArmState) : Prop := ∀ m s, f (setMem m s) = setMem m (f s)

/-- Commutation with `setMem` by pushing it through the state accessors (straight-line code and
conditionals on register values), or, for `match`-heavy semantics, by case analysis first. -/
macro "memfree" : tactic => `(tactic| first
  | ((simp only [state_simp_rules, r_setMem, w_setMem, ite_setMem, dite_setMem] <;> try rfl) <;>
      done)
  | ((simp only [state_simp_rules, r_setMem, w_setMem, ite_setMem, dite_setMem] <;>
      (repeat' split) <;>
      (try simp only [state_simp_rules, r_setMem, w_setMem, ite_setMem, dite_setMem]) <;>
      (try rfl) <;> (try simp_all)) <;> done))

section classes

variable (m : Memory) (s : ArmState)

theorem add_sub_imm (i) : DPI.exec_add_sub_imm i (setMem m s) =
    setMem m (DPI.exec_add_sub_imm i s) := by unfold DPI.exec_add_sub_imm; memfree
theorem pc_rel_addressing (i) : DPI.exec_pc_rel_addressing i (setMem m s) =
    setMem m (DPI.exec_pc_rel_addressing i s) := by unfold DPI.exec_pc_rel_addressing; memfree
theorem logical_imm (i) : DPI.exec_logical_imm i (setMem m s) =
    setMem m (DPI.exec_logical_imm i s) := by unfold DPI.exec_logical_imm; memfree
theorem bitfield (i) : DPI.exec_bitfield i (setMem m s) =
    setMem m (DPI.exec_bitfield i s) := by unfold DPI.exec_bitfield; memfree
theorem move_wide_imm (i) : DPI.exec_move_wide_imm i (setMem m s) =
    setMem m (DPI.exec_move_wide_imm i s) := by unfold DPI.exec_move_wide_imm; memfree
theorem extract (i) : DPI.exec_extract i (setMem m s) =
    setMem m (DPI.exec_extract i s) := by unfold DPI.exec_extract; memfree

theorem compare_branch (i) : BR.exec_compare_branch i (setMem m s) =
    setMem m (BR.exec_compare_branch i s) := by unfold BR.exec_compare_branch; memfree
theorem uncond_branch_imm (i) : BR.exec_uncond_branch_imm i (setMem m s) =
    setMem m (BR.exec_uncond_branch_imm i s) := by unfold BR.exec_uncond_branch_imm; memfree
theorem uncond_branch_reg (i) : BR.exec_uncond_branch_reg i (setMem m s) =
    setMem m (BR.exec_uncond_branch_reg i s) := by unfold BR.exec_uncond_branch_reg; memfree
theorem cond_branch_imm (i) : BR.exec_cond_branch_imm i (setMem m s) =
    setMem m (BR.exec_cond_branch_imm i s) := by unfold BR.exec_cond_branch_imm; memfree
theorem hints (i) : BR.exec_hints i (setMem m s) =
    setMem m (BR.exec_hints i s) := by unfold BR.exec_hints; memfree
theorem barrier (i) : BR.exec_barrier i (setMem m s) =
    setMem m (BR.exec_barrier i s) := by unfold BR.exec_barrier; memfree
theorem test_branch (i) : BR.exec_test_branch i (setMem m s) =
    setMem m (BR.exec_test_branch i s) := by unfold BR.exec_test_branch; memfree
theorem mrs (i) : BR.exec_mrs i (setMem m s) =
    setMem m (BR.exec_mrs i s) := by unfold BR.exec_mrs; memfree

theorem add_sub_carry (i) : DPR.exec_add_sub_carry i (setMem m s) =
    setMem m (DPR.exec_add_sub_carry i s) := by unfold DPR.exec_add_sub_carry; memfree
theorem add_sub_shifted_reg (i) : DPR.exec_add_sub_shifted_reg i (setMem m s) =
    setMem m (DPR.exec_add_sub_shifted_reg i s) := by unfold DPR.exec_add_sub_shifted_reg; memfree
theorem conditional_select (i) : DPR.exec_conditional_select i (setMem m s) =
    setMem m (DPR.exec_conditional_select i s) := by unfold DPR.exec_conditional_select; memfree
theorem data_processing_one_source (i) : DPR.exec_data_processing_one_source i (setMem m s) =
    setMem m (DPR.exec_data_processing_one_source i s) := by
  unfold DPR.exec_data_processing_one_source; memfree
theorem data_processing_two_source (i) : DPR.exec_data_processing_two_source i (setMem m s) =
    setMem m (DPR.exec_data_processing_two_source i s) := by
  unfold DPR.exec_data_processing_two_source; memfree
theorem logical_shifted_reg (i) : DPR.exec_logical_shifted_reg i (setMem m s) =
    setMem m (DPR.exec_logical_shifted_reg i s) := by unfold DPR.exec_logical_shifted_reg; memfree
theorem data_processing_madd (i) : DPR.exec_data_processing_madd i (setMem m s) =
    setMem m (DPR.exec_data_processing_madd i s) := by unfold DPR.exec_data_processing_madd; memfree
theorem data_processing_msub (i) : DPR.exec_data_processing_msub i (setMem m s) =
    setMem m (DPR.exec_data_processing_msub i s) := by unfold DPR.exec_data_processing_msub; memfree
theorem data_processing_mulh (u i) : DPR.exec_data_processing_mulh u i (setMem m s) =
    setMem m (DPR.exec_data_processing_mulh u i s) := by
  unfold DPR.exec_data_processing_mulh; memfree
theorem data_processing_maddl (u o i) : DPR.exec_data_processing_maddl u o i (setMem m s) =
    setMem m (DPR.exec_data_processing_maddl u o i s) := by
  unfold DPR.exec_data_processing_maddl; memfree
theorem data_processing_three_source (i) : DPR.exec_data_processing_three_source i (setMem m s) =
    setMem m (DPR.exec_data_processing_three_source i s) := by
  unfold DPR.exec_data_processing_three_source
  simp only [write_err, w_setMem, data_processing_madd, data_processing_msub,
    data_processing_mulh, data_processing_maddl]
  repeat' split
  all_goals first | rfl | simp_all | contradiction
theorem add_sub_ext_reg (i) : DPR.exec_add_sub_ext_reg i (setMem m s) =
    setMem m (DPR.exec_add_sub_ext_reg i s) := by unfold DPR.exec_add_sub_ext_reg; memfree
theorem conditional_compare_imm (i) : DPR.exec_conditional_compare_imm i (setMem m s) =
    setMem m (DPR.exec_conditional_compare_imm i s) := by
  unfold DPR.exec_conditional_compare_imm; memfree
theorem conditional_compare_reg (i) : DPR.exec_conditional_compare_reg i (setMem m s) =
    setMem m (DPR.exec_conditional_compare_reg i s) := by
  unfold DPR.exec_conditional_compare_reg; memfree

theorem advanced_simd_copy (i) : DPSFP.exec_advanced_simd_copy i (setMem m s) =
    setMem m (DPSFP.exec_advanced_simd_copy i s) := by
  unfold DPSFP.exec_advanced_simd_copy; memfree
theorem rev_vector (i) : DPSFP.exec_rev_vector i (setMem m s) =
    setMem m (DPSFP.exec_rev_vector i s) := by unfold DPSFP.exec_rev_vector; memfree
theorem cnt (i) : DPSFP.exec_cnt i (setMem m s) =
    setMem m (DPSFP.exec_cnt i s) := by unfold DPSFP.exec_cnt; memfree
theorem advanced_simd_two_reg_misc (i) : DPSFP.exec_advanced_simd_two_reg_misc i (setMem m s) =
    setMem m (DPSFP.exec_advanced_simd_two_reg_misc i s) := by
  unfold DPSFP.exec_advanced_simd_two_reg_misc
  split <;> simp only [cnt, rev_vector]
theorem advanced_simd_three_same (i) : DPSFP.exec_advanced_simd_three_same i (setMem m s) =
    setMem m (DPSFP.exec_advanced_simd_three_same i s) := by
  unfold DPSFP.exec_advanced_simd_three_same; memfree
theorem conversion_between_FP_and_Int (i) :
    DPSFP.exec_conversion_between_FP_and_Int i (setMem m s) =
      setMem m (DPSFP.exec_conversion_between_FP_and_Int i s) := by
  unfold DPSFP.exec_conversion_between_FP_and_Int; memfree
theorem advanced_simd_across_lanes (i) : DPSFP.exec_advanced_simd_across_lanes i (setMem m s) =
    setMem m (DPSFP.exec_advanced_simd_across_lanes i s) := by
  unfold DPSFP.exec_advanced_simd_across_lanes; memfree
theorem fp_data_processing_one_source (i) :
    DPSFP.exec_fp_data_processing_one_source i (setMem m s) =
      setMem m (DPSFP.exec_fp_data_processing_one_source i s) := by
  unfold DPSFP.exec_fp_data_processing_one_source; memfree
theorem fp_immediate (i) : DPSFP.exec_fp_immediate i (setMem m s) =
    setMem m (DPSFP.exec_fp_immediate i s) := by unfold DPSFP.exec_fp_immediate; memfree
theorem fp_conditional_select (i) : DPSFP.exec_fp_conditional_select i (setMem m s) =
    setMem m (DPSFP.exec_fp_conditional_select i s) := by
  unfold DPSFP.exec_fp_conditional_select; memfree
theorem advanced_simd_modified_immediate (i) :
    DPSFP.exec_advanced_simd_modified_immediate i (setMem m s) =
      setMem m (DPSFP.exec_advanced_simd_modified_immediate i s) := by
  unfold DPSFP.exec_advanced_simd_modified_immediate; memfree
theorem fp_data_processing_two_source (i) :
    DPSFP.exec_fp_data_processing_two_source i (setMem m s) =
      setMem m (DPSFP.exec_fp_data_processing_two_source i s) := by
  unfold DPSFP.exec_fp_data_processing_two_source; memfree
theorem fp_data_processing_three_source (i) :
    DPSFP.exec_fp_data_processing_three_source i (setMem m s) =
      setMem m (DPSFP.exec_fp_data_processing_three_source i s) := by
  unfold DPSFP.exec_fp_data_processing_three_source; memfree
theorem fp_compare (i) : DPSFP.exec_fp_compare i (setMem m s) =
    setMem m (DPSFP.exec_fp_compare i s) := by unfold DPSFP.exec_fp_compare; memfree

theorem reserved (i) : Reserved.exec_reserved i (setMem m s) =
    setMem m (Reserved.exec_reserved i s) := by unfold Reserved.exec_reserved; memfree

end classes

/-- A load/store instruction (the classes that access memory). -/
def ArmInst.isLDST : ArmInst → Bool
  | .LDST _ => true
  | _ => false

/-- **The non-memory instructions neither read nor write memory.** -/
theorem exec_nonldst (ai : ArmInst) (h : ArmInst.isLDST ai = false) : MemFree (exec_inst ai) := by
  intro m s
  cases ai with
  | LDST i => cases h
  | DPI i => cases i <;> simp only [exec_inst, add_sub_imm, pc_rel_addressing, logical_imm,
      bitfield, move_wide_imm, extract]
  | BR i => cases i <;> simp only [exec_inst, compare_branch, uncond_branch_imm,
      uncond_branch_reg, cond_branch_imm, hints, barrier, test_branch, mrs]
  | DPR i => cases i <;> simp only [exec_inst, add_sub_carry, add_sub_shifted_reg,
      conditional_select, data_processing_one_source, data_processing_two_source,
      logical_shifted_reg, data_processing_three_source, add_sub_ext_reg,
      conditional_compare_imm, conditional_compare_reg]
  | DPSFP i => cases i <;> simp only [exec_inst, advanced_simd_copy, advanced_simd_two_reg_misc,
      advanced_simd_three_same, conversion_between_FP_and_Int, advanced_simd_across_lanes,
      fp_data_processing_one_source, fp_immediate, fp_conditional_select,
      advanced_simd_modified_immediate, fp_data_processing_two_source,
      fp_data_processing_three_source, fp_compare]
  | RES i => simp only [exec_inst, reserved]

/-- The instruction `stepi` executes in `s` (`none`: no instruction fetched or decoded). -/
def decodeAt (s : ArmState) : Option ArmInst :=
  match fetch_inst (r .PC s) s with
  | some w => decode_raw_inst w
  | none => none

theorem decodeAt_setMem (m : Memory) (s : ArmState) : decodeAt (setMem m s) = decodeAt s := by
  simp only [decodeAt, r_setMem, fetch_inst_setMem]

/-- **A step at a non-memory instruction neither reads nor writes memory.** -/
theorem stepi_setMem (m : Memory) (s : ArmState)
    (h : ∀ ai, decodeAt s = some ai → ArmInst.isLDST ai = false) :
    stepi (setMem m s) = setMem m (stepi s) := by
  unfold stepi
  simp only [read_err, read_pc, r_setMem, fetch_inst_setMem]
  split
  · split
    · simp only [write_err, w_setMem]
    · rename_i w hw
      split
      · simp only [write_err, w_setMem]
      · rename_i ai hai
        exact exec_nonldst ai (h ai (by simp [decodeAt, hw, hai])) m s
  · rfl

/-! ## The byte accessors as functions of the memory -/

/-- `n` bytes at `a` of the memory `m` (little-endian), as `read_mem_bytes`. -/
def readM : (n : Nat) → BitVec 64 → Memory → BitVec (n * 8)
  | 0, _, _ => 0#0
  | n + 1, a, m => ((readM n (a + 1#64) m) ++ read_store a m).cast (by omega)

/-- `m` with the `n` bytes of `v` stored at `a`, as `write_mem_bytes`. -/
def writeM : (n : Nat) → BitVec 64 → BitVec (n * 8) → Memory → Memory
  | 0, _, _, m => m
  | n + 1, a, v, m =>
    writeM n (a + 1#64) (BitVec.setWidth (n * 8) (v >>> 8))
      (write_store a (BitVec.extractLsb' 0 8 v) m)

theorem read_mem_bytes_eq (n : Nat) (a : BitVec 64) (s : ArmState) :
    read_mem_bytes n a s = readM n a s.mem := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [read_mem_bytes, readM, ih, read_mem]

theorem write_mem_bytes_eq (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (s : ArmState) :
    write_mem_bytes n a v s = setMem (writeM n a v s.mem) s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
    simp only [write_mem_bytes, writeM, ih, write_mem]
    rfl

/-! ## Bytes of `readM` / `writeM` -/

theorem bv_byte_append_zero {n : Nat} (x : BitVec (n * 8)) (y : BitVec 8) (h : n * 8 + 8 = (n + 1) * 8) :
    ((x ++ y).cast h).extractLsb' 0 8 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_append, hi]

theorem bv_byte_append_succ {n k : Nat} (x : BitVec (n * 8)) (y : BitVec 8) (h : n * 8 + 8 = (n + 1) * 8) :
    ((x ++ y).cast h).extractLsb' (8 * (k + 1)) 8 = x.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append]
  by_cases h1 : i < 8
  · simp only [h1, decide_true, Bool.true_and, show ¬ (8 * (k + 1) + i < 8) from by omega,
      ite_false]
    congr 1; omega
  · omega

theorem bv_shift_append {n : Nat} (x : BitVec (n * 8)) (y : BitVec 8) (h : n * 8 + 8 = (n + 1) * 8) :
    BitVec.setWidth (n * 8) (((x ++ y).cast h) >>> 8) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_cast,
    BitVec.getLsbD_append, hi, decide_true, Bool.true_and, show ¬ (8 + i < 8) from by omega,
    ite_false]
  congr 1; omega

theorem bv_byte_shift {n k : Nat} (v : BitVec ((n + 1) * 8)) (hk : k < n) :
    (BitVec.setWidth (n * 8) (v >>> 8)).extractLsb' (8 * k) 8 = v.extractLsb' (8 * (k + 1)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi,
    decide_true, Bool.true_and]
  simp only [show 8 * k + i < n * 8 from by omega, decide_true, Bool.true_and]
  congr 1; omega

theorem bv_eq_of_bytes {n : Nat} {x y : BitVec (n * 8)}
    (h : ∀ k < n, x.extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hk := h (i / 8) (by omega)
  have := congrArg (fun z => z.getLsbD (i % 8)) hk
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and] at this
  rwa [show 8 * (i / 8) + i % 8 = i from by omega] at this

theorem readM_byte : ∀ (n : Nat) (a : BitVec 64) (m : Memory) (k : Nat), k < n →
    (readM n a m).extractLsb' (8 * k) 8 = read_store (a + BitVec.ofNat 64 k) m
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, a, m, 0, _ => by
    simp only [readM]; rw [bv_byte_append_zero]; simp
  | n + 1, a, m, k + 1, hk => by
    simp only [readM]; rw [bv_byte_append_succ, readM_byte n (a + 1#64) m k (by omega)]
    congr 1
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem writeM_apply_out : ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (m : Memory)
    (x : BitVec 64), (∀ k < n, a + BitVec.ofNat 64 k ≠ x) → writeM n a v m x = m x
  | 0, _, _, _, _, _ => rfl
  | n + 1, a, v, m, x, h => by
    simp only [writeM]
    rw [writeM_apply_out n _ _ _ x (fun k hk e => h (k + 1) (by omega) (by
      rw [← e, BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega))]
    have hx : a ≠ x := fun e => h 0 (by omega) (by simpa using e)
    show read_store x (write_store a _ m) = read_store x m
    simp [read_store, write_store, hx.symm]

theorem writeM_apply_in : ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (m : Memory) (k : Nat),
    n ≤ 2 ^ 64 → k < n → writeM n a v m (a + BitVec.ofNat 64 k) = v.extractLsb' (8 * k) 8
  | 0, _, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, a, v, m, 0, hn, _ => by
    simp only [writeM]
    rw [writeM_apply_out]
    · simp [write_store]
    · intro k hk e
      have := congrArg BitVec.toNat e
      simp [BitVec.toNat_add] at this
      omega
  | n + 1, a, v, m, k + 1, hn, hk => by
    simp only [writeM]
    have e : a + BitVec.ofNat 64 (k + 1) = a + 1#64 + BitVec.ofNat 64 k := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    rw [e, writeM_apply_in n _ _ _ k (by omega) (by omega), bv_byte_shift _ (by omega)]

theorem writeM_readM : ∀ (n : Nat) (a : BitVec 64) (m : Memory), writeM n a (readM n a m) m = m
  | 0, _, _ => rfl
  | n + 1, a, m => by
    simp only [writeM, readM]
    rw [bv_byte_append_zero, bv_shift_append]
    have : write_store a (read_store a m) m = m := by
      funext x; simp only [write_store, read_store]; split <;> simp_all
    rw [this, writeM_readM]

theorem readM_writeM (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (m : Memory)
    (hn : n ≤ 2 ^ 64) : readM n a (writeM n a v m) = v := by
  apply bv_eq_of_bytes; intro k hk
  rw [readM_byte _ _ _ _ hk, read_store, writeM_apply_in _ _ _ _ _ hn hk]

theorem readM_congr : ∀ (n : Nat) (a : BitVec 64) (m m' : Memory),
    (∀ k < n, read_store (a + BitVec.ofNat 64 k) m = read_store (a + BitVec.ofNat 64 k) m') →
    readM n a m = readM n a m' := by
  intro n a m m' h
  apply bv_eq_of_bytes; intro k hk
  rw [readM_byte _ _ _ _ hk, readM_byte _ _ _ _ hk, h k hk]

/-- A full-memory write does not depend on the memory written to. -/
theorem writeM_full (a : BitVec 64) (v : BitVec (2 ^ 64 * 8)) (m m' : Memory) :
    writeM (2 ^ 64) a v m = writeM (2 ^ 64) a v m' := by
  funext x
  have hx : x = a + BitVec.ofNat 64 (x - a).toNat := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega
  have hk : (x - a).toNat < 2 ^ 64 := (x - a).isLt
  rw [hx, writeM_apply_in _ _ _ _ _ (Nat.le_refl _) hk, writeM_apply_in _ _ _ _ _ (Nat.le_refl _) hk]

theorem readM_full_inj {a : BitVec 64} {m m' : Memory}
    (h : readM (2 ^ 64) a m = readM (2 ^ 64) a m') : m = m' := by
  rw [← writeM_readM (2 ^ 64) a m, h, writeM_full _ _ m m', writeM_readM]

end Concurrency.ArmFoot

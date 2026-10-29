module

public import FV.Arm.Exec

@[expose] public section

/-!
# General-purpose register footprints of the Arm instructions (SEM1, `docs/plans/uninit.md` §5.8)

The two-run lock-step of prophecy determinism (§5.8 (1)) compares runs whose states differ in
`x30`: the canonical callee entry returns to `raStar`, the actual one to its call site. It needs
to know which instructions read (or write) `x30`. This file gives every instruction class of the
Arm model its **general-purpose register footprint**:

* `setGpr k v s`: `s` with `x_k := v`; `GprFree k f`: `f` commutes with `setGpr k`, i.e. it
  neither reads nor writes `x_k`;
* `ArmInst.gprs ai`: the general-purpose registers `ai` names: its register fields that denote
  GPRs (the SIMD&FP classes name none; a load/store's data register only when it is not a SIMD&FP
  access; a conversion conservatively both), and `x30` for `bl`/`blr` (the link register);
* **`gprFree_exec_inst`**: `k ∉ ai.gprs → k ≠ 31 → GprFree k (exec_inst ai)`.

So `exec_inst ai` reads and writes `x30` only if `30 ∈ ai.gprs`: among the instructions the
backend emits, `bl`/`blr` (link), `ret` (its `Rn` is 30), and the frame-record pair
`stp x29, x30` / `ldp x29, x30` (`Rt2 = 30`) — Cranelift never allocates `x30`, which the
per-line check `ArmInst.gprs` decides on the compiled code.
-/

namespace E2E.GprFoot

open Arm

/-- `s` with general-purpose register `x_k` set to `v`. -/
def setGpr (k : BitVec 5) (v : BitVec 64) (s : ArmState) : ArmState := w (.GPR k) v s

/-- **`f` neither reads nor writes `x_k`**: it commutes with setting it. -/
def GprFree (k : BitVec 5) (f : ArmState → ArmState) : Prop :=
  ∀ v s, f (setGpr k v s) = setGpr k v (f s)

theorem r_setGpr {k : BitVec 5} {fld : StateField} (h : fld ≠ .GPR k) (v : BitVec 64)
    (s : ArmState) : r fld (setGpr k v s) = r fld s :=
  r_of_w_different h

theorem w_setGpr {k : BitVec 5} {fld : StateField} (h : fld ≠ .GPR k) (x : state_value fld)
    (v : BitVec 64) (s : ArmState) : w fld x (setGpr k v s) = setGpr k v (w fld x s) :=
  w_of_w_commute h

theorem ite_setGpr {c : Prop} [Decidable c] (k : BitVec 5) (v : BitVec 64) (a b : ArmState) :
    (if c then setGpr k v a else setGpr k v b) = setGpr k v (if c then a else b) := by
  split <;> rfl

theorem dite_setGpr {c : Prop} [Decidable c] (k : BitVec 5) (v : BitVec 64) (a : c → ArmState)
    (b : ¬ c → ArmState) :
    (if h : c then setGpr k v (a h) else setGpr k v (b h)) =
      setGpr k v (if h : c then a h else b h) := by
  split <;> rfl

theorem setGpr_mem (k : BitVec 5) (v : BitVec 64) (s : ArmState) :
    (setGpr k v s).mem = s.mem := by
  unfold setGpr w write_base_gpr; rfl

theorem setGpr_program (k : BitVec 5) (v : BitVec 64) (s : ArmState) :
    (setGpr k v s).program = s.program := w_program

theorem read_mem_bytes_setGpr (n : Nat) (a : BitVec 64) (k : BitVec 5) (v : BitVec 64)
    (s : ArmState) : read_mem_bytes n a (setGpr k v s) = read_mem_bytes n a s :=
  read_mem_bytes_of_w

theorem write_mem_setGpr (a : BitVec 64) (x : BitVec 8) (k : BitVec 5) (v : BitVec 64)
    (s : ArmState) : write_mem a x (setGpr k v s) = setGpr k v (write_mem a x s) := by
  unfold setGpr write_mem w write_base_gpr; rfl

theorem write_mem_bytes_setGpr : ∀ (n : Nat) (a : BitVec 64) (x : BitVec (n * 8)) (k : BitVec 5)
    (v : BitVec 64) (s : ArmState),
    write_mem_bytes n a x (setGpr k v s) = setGpr k v (write_mem_bytes n a x s)
  | 0, _, _, _, _, _ => rfl
  | n + 1, a, x, k, v, s => by
    unfold write_mem_bytes
    simp only
    rw [write_mem_setGpr, write_mem_bytes_setGpr n]

theorem fetch_inst_setGpr (a : BitVec 64) (k : BitVec 5) (v : BitVec 64) (s : ArmState) :
    fetch_inst a (setGpr k v s) = fetch_inst a s := fetch_inst_of_w

/-- Commutation with `setGpr k` by pushing it through the state accessors, the side conditions
(`fld ≠ .GPR k`) discharged from the hypotheses (straight-line code and conditionals), or, for
`match`-heavy semantics, by case analysis first. -/
macro "gprfree" : tactic => `(tactic| first
  | ((simp only [state_simp_rules, r_setGpr, w_setGpr, ite_setGpr, dite_setGpr,
      read_mem_bytes_setGpr, write_mem_bytes_setGpr, setGpr_mem, ne_eq, reduceCtorEq, CheckSPAlignment,
      not_false_eq_true, *] <;> try rfl) <;> done)
  | ((simp only [state_simp_rules, r_setGpr, w_setGpr, ite_setGpr, dite_setGpr,
      read_mem_bytes_setGpr, write_mem_bytes_setGpr, setGpr_mem, ne_eq, reduceCtorEq, CheckSPAlignment,
      not_false_eq_true, *] <;>
      (repeat' split) <;>
      (try simp only [state_simp_rules, r_setGpr, w_setGpr, ite_setGpr, dite_setGpr,
        read_mem_bytes_setGpr, write_mem_bytes_setGpr, setGpr_mem, ne_eq, reduceCtorEq, CheckSPAlignment,
        not_false_eq_true, *]) <;>
      (try rfl) <;> (try simp_all)) <;> done))

/-! ## The instruction classes

Every class lemma takes `hk : ¬ 31#5 = k` (the stack pointer is register 31, which the alignment
checks read) and the register fields of the class that may denote a GPR. -/

section classes

variable {k : BitVec 5}

theorem add_sub_imm (hk : ¬ 31#5 = k) (i : Add_sub_imm_cls) (hn : ¬ i.Rn = k)
    (hd : ¬ i.Rd = k) : GprFree k (DPI.exec_add_sub_imm i) := by
  intro v s; unfold DPI.exec_add_sub_imm; gprfree
theorem pc_rel_addressing (hk : ¬ 31#5 = k) (i : PC_rel_addressing_cls) (hd : ¬ i.Rd = k) :
    GprFree k (DPI.exec_pc_rel_addressing i) := by
  intro v s; unfold DPI.exec_pc_rel_addressing; gprfree
theorem logical_imm (hk : ¬ 31#5 = k) (i : Logical_imm_cls) (hn : ¬ i.Rn = k)
    (hd : ¬ i.Rd = k) : GprFree k (DPI.exec_logical_imm i) := by
  intro v s; unfold DPI.exec_logical_imm; gprfree
theorem bitfield (hk : ¬ 31#5 = k) (i : Bitfield_cls) (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPI.exec_bitfield i) := by
  intro v s; unfold DPI.exec_bitfield; gprfree
theorem move_wide_imm (hk : ¬ 31#5 = k) (i : Move_wide_imm_cls) (hd : ¬ i.Rd = k) :
    GprFree k (DPI.exec_move_wide_imm i) := by
  intro v s; unfold DPI.exec_move_wide_imm; gprfree
theorem extract (hk : ¬ 31#5 = k) (i : Extract_cls) (hm : ¬ i.Rm = k) (hn : ¬ i.Rn = k)
    (hd : ¬ i.Rd = k) : GprFree k (DPI.exec_extract i) := by
  intro v s; unfold DPI.exec_extract; gprfree

theorem compare_branch (hk : ¬ 31#5 = k) (i : Compare_branch_cls) (ht : ¬ i.Rt = k) :
    GprFree k (BR.exec_compare_branch i) := by
  intro v s; unfold BR.exec_compare_branch; gprfree
theorem uncond_branch_imm (hk : ¬ 31#5 = k) (i : Uncond_branch_imm_cls)
    (hl : i.op = 1#1 → ¬ 30#5 = k) : GprFree k (BR.exec_uncond_branch_imm i) := by
  intro v s; unfold BR.exec_uncond_branch_imm
  by_cases h : i.op = 0#1
  · gprfree
  · have hl := hl (by revert h; generalize i.op = o; decide +revert)
    gprfree
theorem uncond_branch_reg (hk : ¬ 31#5 = k) (i : Uncond_branch_reg_cls) (hn : ¬ i.Rn = k)
    (hl : i.opc = 0b0001#4 → ¬ 30#5 = k) : GprFree k (BR.exec_uncond_branch_reg i) := by
  intro v s; unfold BR.exec_uncond_branch_reg
  by_cases h : i.opc = 0b0001#4
  · have hl := hl h
    gprfree
  · gprfree
theorem cond_branch_imm (hk : ¬ 31#5 = k) (i : Cond_branch_imm_cls) :
    GprFree k (BR.exec_cond_branch_imm i) := by
  intro v s; unfold BR.exec_cond_branch_imm; gprfree
theorem hints (hk : ¬ 31#5 = k) (i : Hints_cls) : GprFree k (BR.exec_hints i) := by
  intro v s; unfold BR.exec_hints; gprfree
theorem barrier (hk : ¬ 31#5 = k) (i : Barrier_cls) : GprFree k (BR.exec_barrier i) := by
  intro v s; unfold BR.exec_barrier; gprfree
theorem test_branch (hk : ¬ 31#5 = k) (i : Test_branch_cls) (ht : ¬ i.Rt = k) :
    GprFree k (BR.exec_test_branch i) := by
  intro v s; unfold BR.exec_test_branch; gprfree
theorem mrs (hk : ¬ 31#5 = k) (i : Mrs_cls) (ht : ¬ i.Rt = k) : GprFree k (BR.exec_mrs i) := by
  intro v s; unfold BR.exec_mrs; gprfree

theorem add_sub_carry (hk : ¬ 31#5 = k) (i : Add_sub_carry_cls) (hm : ¬ i.Rm = k)
    (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) : GprFree k (DPR.exec_add_sub_carry i) := by
  intro v s; unfold DPR.exec_add_sub_carry; gprfree
theorem add_sub_shifted_reg (hk : ¬ 31#5 = k) (i : Add_sub_shifted_reg_cls) (hm : ¬ i.Rm = k)
    (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) : GprFree k (DPR.exec_add_sub_shifted_reg i) := by
  intro v s; unfold DPR.exec_add_sub_shifted_reg; gprfree
theorem conditional_select (hk : ¬ 31#5 = k) (i : Conditional_select_cls) (hm : ¬ i.Rm = k)
    (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) : GprFree k (DPR.exec_conditional_select i) := by
  intro v s; unfold DPR.exec_conditional_select; gprfree
theorem data_processing_one_source (hk : ¬ 31#5 = k) (i : Data_processing_one_source_cls)
    (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) : GprFree k (DPR.exec_data_processing_one_source i) := by
  intro v s; unfold DPR.exec_data_processing_one_source; gprfree
theorem data_processing_two_source (hk : ¬ 31#5 = k) (i : Data_processing_two_source_cls)
    (hm : ¬ i.Rm = k) (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPR.exec_data_processing_two_source i) := by
  intro v s; unfold DPR.exec_data_processing_two_source; gprfree
theorem logical_shifted_reg (hk : ¬ 31#5 = k) (i : Logical_shifted_reg_cls) (hm : ¬ i.Rm = k)
    (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) : GprFree k (DPR.exec_logical_shifted_reg i) := by
  intro v s; unfold DPR.exec_logical_shifted_reg; gprfree
theorem data_processing_madd (hk : ¬ 31#5 = k) (i : Data_processing_three_source_cls)
    (hm : ¬ i.Rm = k) (ha : ¬ i.Ra = k) (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPR.exec_data_processing_madd i) := by
  intro v s; unfold DPR.exec_data_processing_madd; gprfree
theorem data_processing_msub (hk : ¬ 31#5 = k) (i : Data_processing_three_source_cls)
    (hm : ¬ i.Rm = k) (ha : ¬ i.Ra = k) (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPR.exec_data_processing_msub i) := by
  intro v s; unfold DPR.exec_data_processing_msub; gprfree
theorem data_processing_mulh (hk : ¬ 31#5 = k) (u : Bool) (i : Data_processing_three_source_cls)
    (hm : ¬ i.Rm = k) (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPR.exec_data_processing_mulh u i) := by
  intro v s; unfold DPR.exec_data_processing_mulh; gprfree
theorem data_processing_maddl (hk : ¬ 31#5 = k) (u o : Bool) (i : Data_processing_three_source_cls)
    (hm : ¬ i.Rm = k) (ha : ¬ i.Ra = k) (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPR.exec_data_processing_maddl u o i) := by
  intro v s; unfold DPR.exec_data_processing_maddl; gprfree
theorem data_processing_three_source (hk : ¬ 31#5 = k) (i : Data_processing_three_source_cls)
    (hm : ¬ i.Rm = k) (ha : ¬ i.Ra = k) (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPR.exec_data_processing_three_source i) := by
  intro v s
  unfold DPR.exec_data_processing_three_source
  simp only [write_err, w_setGpr (show StateField.ERR ≠ .GPR k by simp),
    data_processing_madd hk i hm ha hn hd v s, data_processing_msub hk i hm ha hn hd v s,
    data_processing_mulh hk _ i hm hn hd v s, data_processing_maddl hk _ _ i hm ha hn hd v s]
  repeat' split
  all_goals first | rfl | simp_all | contradiction
theorem add_sub_ext_reg (hk : ¬ 31#5 = k) (i : Add_sub_ext_reg_cls) (hm : ¬ i.Rm = k)
    (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) : GprFree k (DPR.exec_add_sub_ext_reg i) := by
  intro v s; unfold DPR.exec_add_sub_ext_reg; gprfree
theorem conditional_compare_imm (hk : ¬ 31#5 = k) (i : Conditional_compare_imm_cls)
    (hn : ¬ i.Rn = k) : GprFree k (DPR.exec_conditional_compare_imm i) := by
  intro v s; unfold DPR.exec_conditional_compare_imm; gprfree
theorem conditional_compare_reg (hk : ¬ 31#5 = k) (i : Conditional_compare_reg_cls)
    (hm : ¬ i.Rm = k) (hn : ¬ i.Rn = k) : GprFree k (DPR.exec_conditional_compare_reg i) := by
  intro v s; unfold DPR.exec_conditional_compare_reg; gprfree

theorem advanced_simd_copy (hk : ¬ 31#5 = k) (i : Advanced_simd_copy_cls) (hn : ¬ i.Rn = k)
    (hd : ¬ i.Rd = k) : GprFree k (DPSFP.exec_advanced_simd_copy i) := by
  intro v s; unfold DPSFP.exec_advanced_simd_copy; gprfree
theorem advanced_simd_two_reg_misc (hk : ¬ 31#5 = k) (i : Advanced_simd_two_reg_misc_cls) :
    GprFree k (DPSFP.exec_advanced_simd_two_reg_misc i) := by
  intro v s
  unfold DPSFP.exec_advanced_simd_two_reg_misc DPSFP.exec_cnt DPSFP.exec_rev_vector
  gprfree
theorem advanced_simd_three_same (hk : ¬ 31#5 = k) (i : Advanced_simd_three_same_cls) :
    GprFree k (DPSFP.exec_advanced_simd_three_same i) := by
  intro v s; unfold DPSFP.exec_advanced_simd_three_same; gprfree
theorem conversion_between_FP_and_Int (hk : ¬ 31#5 = k) (i : Conversion_between_FP_and_Int_cls)
    (hn : ¬ i.Rn = k) (hd : ¬ i.Rd = k) :
    GprFree k (DPSFP.exec_conversion_between_FP_and_Int i) := by
  intro v s
  unfold DPSFP.exec_conversion_between_FP_and_Int DPSFP.exec_fmov_general DPSFP.exec_fp_int_cvt
  gprfree
theorem advanced_simd_across_lanes (hk : ¬ 31#5 = k) (i : Advanced_simd_across_lanes_cls) :
    GprFree k (DPSFP.exec_advanced_simd_across_lanes i) := by
  intro v s; unfold DPSFP.exec_advanced_simd_across_lanes; gprfree
theorem fp_data_processing_one_source (hk : ¬ 31#5 = k) (i : FP_data_processing_one_source_cls) :
    GprFree k (DPSFP.exec_fp_data_processing_one_source i) := by
  intro v s; unfold DPSFP.exec_fp_data_processing_one_source; gprfree
theorem fp_immediate (hk : ¬ 31#5 = k) (i : FP_immediate_cls) :
    GprFree k (DPSFP.exec_fp_immediate i) := by
  intro v s; unfold DPSFP.exec_fp_immediate; gprfree
theorem fp_conditional_select (hk : ¬ 31#5 = k) (i : FP_conditional_select_cls) :
    GprFree k (DPSFP.exec_fp_conditional_select i) := by
  intro v s; unfold DPSFP.exec_fp_conditional_select; gprfree
theorem advanced_simd_modified_immediate (hk : ¬ 31#5 = k)
    (i : Advanced_simd_modified_immediate_cls) :
    GprFree k (DPSFP.exec_advanced_simd_modified_immediate i) := by
  intro v s; unfold DPSFP.exec_advanced_simd_modified_immediate; gprfree
theorem fp_data_processing_two_source (hk : ¬ 31#5 = k) (i : FP_data_processing_two_source_cls) :
    GprFree k (DPSFP.exec_fp_data_processing_two_source i) := by
  intro v s; unfold DPSFP.exec_fp_data_processing_two_source; gprfree
theorem fp_data_processing_three_source (hk : ¬ 31#5 = k)
    (i : FP_data_processing_three_source_cls) :
    GprFree k (DPSFP.exec_fp_data_processing_three_source i) := by
  intro v s; unfold DPSFP.exec_fp_data_processing_three_source; gprfree
theorem fp_compare (hk : ¬ 31#5 = k) (i : FP_compare_cls) : GprFree k (DPSFP.exec_fp_compare i) := by
  intro v s; unfold DPSFP.exec_fp_compare; gprfree

/-! ### Loads and stores: the shared operations -/

theorem checkSP_setGpr (hk : ¬ 31#5 = k) (v : BitVec 64) (s : ArmState) :
    CheckSPAlignment (setGpr k v s) = CheckSPAlignment s :=
  CheckSPAlignment_w_different_eq (by simpa using hk)

theorem read_gpr_setGpr {i : BitVec 5} (h : ¬ i = k) (n : Nat) (v : BitVec 64) (s : ArmState) :
    read_gpr n i (setGpr k v s) = read_gpr n i s := by
  simp only [read_gpr, r_setGpr (show StateField.GPR i ≠ .GPR k by simpa using h)]

theorem write_gpr_setGpr {i : BitVec 5} (h : ¬ i = k) (n : Nat) (x : BitVec n) (v : BitVec 64)
    (s : ArmState) : write_gpr n i x (setGpr k v s) = setGpr k v (write_gpr n i x s) := by
  simp only [write_gpr, w_setGpr (show StateField.GPR i ≠ .GPR k by simpa using h)]

theorem ldst_read_setGpr {b : Bool} {i : BitVec 5} (h : b = true ∨ ¬ i = k) (n : Nat)
    (v : BitVec 64) (s : ArmState) : ldst_read b n i (setGpr k v s) = ldst_read b n i s := by
  rcases h with rfl | h
  · simp only [ldst_read, ite_true, read_sfp, r_setGpr (show StateField.SFP i ≠ .GPR k by simp)]
  · cases b <;> simp only [ldst_read, read_sfp, read_gpr_zr, read_gpr_setGpr h,
      r_setGpr (show StateField.SFP i ≠ .GPR k by simp), Bool.false_eq_true, ite_false, ite_true]

theorem ldst_write_setGpr {b : Bool} {i : BitVec 5} (h : b = true ∨ ¬ i = k) (n : Nat)
    (x : BitVec n) (v : BitVec 64) (s : ArmState) :
    ldst_write b n i x (setGpr k v s) = setGpr k v (ldst_write b n i x s) := by
  rcases h with rfl | h
  · simp only [ldst_write, ite_true, write_sfp, w_setGpr (show StateField.SFP i ≠ .GPR k by simp)]
  · cases b
    · simp only [ldst_write, write_gpr_zr, write_gpr_setGpr h, Bool.false_eq_true, ite_false]
      split <;> rfl
    · simp only [ldst_write, ite_true, write_sfp,
        w_setGpr (show StateField.SFP i ≠ .GPR k by simp)]

theorem write_gpr_zr_setGpr {i : BitVec 5} (h : ¬ i = k) (n : Nat) (x : BitVec n) (v : BitVec 64)
    (s : ArmState) : write_gpr_zr n i x (setGpr k v s) = setGpr k v (write_gpr_zr n i x s) := by
  simp only [write_gpr_zr, write_gpr_setGpr h]; split <;> rfl

theorem write_err_setGpr (e : StateError) (v : BitVec 64) (s : ArmState) :
    write_err e (setGpr k v s) = setGpr k v (write_err e s) :=
  w_setGpr (by simp) _ _ _

theorem write_pc_setGpr (x v : BitVec 64) (s : ArmState) :
    write_pc x (setGpr k v s) = setGpr k v (write_pc x s) :=
  w_setGpr (by simp) _ _ _

theorem read_pc_setGpr (v : BitVec 64) (s : ArmState) : read_pc (setGpr k v s) = read_pc s :=
  r_setGpr (by simp) _ _

theorem write_sfp_setGpr (n : Nat) (i : BitVec 5) (x : BitVec n) (v : BitVec 64) (s : ArmState) :
    write_sfp n i x (setGpr k v s) = setGpr k v (write_sfp n i x s) := by
  simp only [write_sfp, w_setGpr (show StateField.SFP i ≠ .GPR k by simp)]

theorem reg_imm_operation_setGpr (hk : ¬ 31#5 = k) {str : String} {op : BitVec 1}
    {signed wback postindex simd : Bool} {datasize regsize : Nat} {Rn Rt : BitVec 5}
    {offset : BitVec 64} {H : 8 ∣ datasize} (hn : ¬ Rn = k) (ht : simd = true ∨ ¬ Rt = k)
    (v : BitVec 64) (s : ArmState) :
    LDST.reg_imm_operation str op signed wback postindex simd datasize regsize Rn Rt offset
      (setGpr k v s) H =
    setGpr k v (LDST.reg_imm_operation str op signed wback postindex simd datasize regsize Rn Rt
      offset s H) := by
  unfold LDST.reg_imm_operation
  simp only [checkSP_setGpr hk, read_gpr_setGpr hn]
  split
  · exact write_err_setGpr _ _ _
  · simp only [ldst_read_setGpr ht, read_mem_bytes_setGpr, write_mem_bytes_setGpr,
      write_sfp_setGpr]
    rcases ht with rfl | ht
    · repeat' split
      all_goals first | rfl | (simp only [write_gpr_setGpr hn]; done) | simp_all
    · repeat' split
      all_goals first
        | rfl
        | (simp only [write_gpr_setGpr hn, write_gpr_zr_setGpr ht]; done)
        | simp_all [write_gpr_zr_setGpr ht]

/-- The shared single-register load/store (`exec_reg_imm_common`). -/
theorem reg_imm_common (hk : ¬ 31#5 = k) (i : LDST.Reg_imm_cls) (str : String) (hn : ¬ i.Rn = k)
    (ht : i.SIMD? = true ∨ ¬ i.Rt = k) (hm : ∀ Rm o S, i.imm = .reg Rm o S → ¬ Rm = k) :
    GprFree k (LDST.exec_reg_imm_common i str) := by
  intro v s
  have hoff : ∀ sc, i.imm.value sc (setGpr k v s) = i.imm.value sc s := by
    intro sc
    cases h : i.imm with
    | reg Rm o S => simp only [LDST.Reg_offset.value, read_gpr_zr, read_gpr_setGpr (hm Rm o S h)]
    | _ => rfl
  unfold LDST.exec_reg_imm_common
  simp only [hoff, reg_imm_operation_setGpr hk hn ht, write_pc_setGpr, read_pc_setGpr,
    write_err_setGpr, ite_setGpr]

theorem reg_imm_post_indexed (hk : ¬ 31#5 = k) (i : Reg_imm_post_indexed_cls) (hn : ¬ i.Rn = k)
    (ht : i.V = 1#1 ∨ ¬ i.Rt = k) : GprFree k (LDST.exec_reg_imm_post_indexed i) := by
  intro v s; unfold LDST.exec_reg_imm_post_indexed
  exact reg_imm_common hk _ _ hn (by simpa using ht) (by simp) v s
theorem reg_imm_unsigned_offset (hk : ¬ 31#5 = k) (i : Reg_unsigned_imm_cls) (hn : ¬ i.Rn = k)
    (ht : i.V = 1#1 ∨ ¬ i.Rt = k) : GprFree k (LDST.exec_reg_imm_unsigned_offset i) := by
  intro v s; unfold LDST.exec_reg_imm_unsigned_offset
  exact reg_imm_common hk _ _ hn (by simpa using ht) (by simp) v s
theorem reg_imm_pre_indexed (hk : ¬ 31#5 = k) (i : Reg_imm_pre_indexed_cls) (hn : ¬ i.Rn = k)
    (ht : i.V = 1#1 ∨ ¬ i.Rt = k) : GprFree k (LDST.exec_reg_imm_pre_indexed i) := by
  intro v s; unfold LDST.exec_reg_imm_pre_indexed
  exact reg_imm_common hk _ _ hn (by simpa using ht) (by simp) v s
theorem reg_reg_offset (hk : ¬ 31#5 = k) (i : Reg_reg_offset_cls) (hm : ¬ i.Rm = k)
    (hn : ¬ i.Rn = k) (ht : i.V = 1#1 ∨ ¬ i.Rt = k) : GprFree k (LDST.exec_reg_reg_offset i) := by
  intro v s; unfold LDST.exec_reg_reg_offset
  split
  · exact write_err_setGpr _ _ _
  · refine reg_imm_common hk _ _ hn (by simpa using ht) ?_ v s
    intro Rm o S h
    injection h with h1
    exact h1 ▸ hm
theorem ldstur (hk : ¬ 31#5 = k) (i : Reg_unscaled_imm_cls) (hn : ¬ i.Rn = k) :
    GprFree k (LDST.exec_ldstur i) := by
  intro v s; unfold LDST.exec_ldstur
  simp only [checkSP_setGpr hk, read_gpr_setGpr hn, read_pc_setGpr, write_pc_setGpr,
    write_err_setGpr, read_mem_bytes_setGpr, write_mem_bytes_setGpr, write_sfp_setGpr,
    read_sfp, r_setGpr (show StateField.SFP i.Rt ≠ .GPR k by simp), ite_setGpr]
theorem reg_unscaled_imm (hk : ¬ 31#5 = k) (i : Reg_unscaled_imm_cls) (hn : ¬ i.Rn = k)
    (ht : i.VR = 1#1 ∨ ¬ i.Rt = k) : GprFree k (LDST.exec_reg_unscaled_imm i) := by
  intro v s; unfold LDST.exec_reg_unscaled_imm
  split
  · exact ldstur hk i hn v s
  · rename_i hv
    unfold LDST.exec_reg_unscaled_imm_gpr
    exact reg_imm_common hk _ _ hn (.inr (ht.resolve_left hv)) (by simp) v s

/-- The shared pair load/store (`reg_pair_operation`). -/
theorem reg_pair_operation_setGpr (hk : ¬ 31#5 = k) {i : LDST.Reg_pair_cls} {str : String}
    {signed : Bool} {datasize : Nat} {offset : BitVec 64} {H : 8 ∣ datasize} (hn : ¬ i.Rn = k)
    (ht : i.SIMD? = true ∨ (¬ i.Rt = k ∧ ¬ i.Rt2 = k)) (v : BitVec 64) (s : ArmState) :
    LDST.reg_pair_operation i str signed datasize offset (setGpr k v s) H =
      setGpr k v (LDST.reg_pair_operation i str signed datasize offset s H) := by
  unfold LDST.reg_pair_operation
  simp only [checkSP_setGpr hk, read_gpr_setGpr hn]
  split
  · exact write_err_setGpr _ _ _
  · have ht1 : i.SIMD? = true ∨ ¬ i.Rt = k := ht.imp id And.left
    have ht2 : i.SIMD? = true ∨ ¬ i.Rt2 = k := ht.imp id And.right
    simp only [ldst_read_setGpr ht1, ldst_read_setGpr ht2, read_mem_bytes_setGpr,
      write_mem_bytes_setGpr, ldst_write_setGpr ht1, ldst_write_setGpr ht2]
    rcases ht with hs | ⟨h1, h2⟩
    · repeat' split
      all_goals first | rfl | (simp only [write_gpr_setGpr hn]; done) | simp_all
    · repeat' split
      all_goals first
        | rfl
        | (simp only [write_gpr_setGpr hn, write_gpr_zr_setGpr h1, write_gpr_zr_setGpr h2]; done)
        | simp_all [write_gpr_zr_setGpr h1, write_gpr_zr_setGpr h2]

theorem reg_pair_common (hk : ¬ 31#5 = k) (i : LDST.Reg_pair_cls) (str : String)
    (hn : ¬ i.Rn = k) (ht : i.SIMD? = true ∨ (¬ i.Rt = k ∧ ¬ i.Rt2 = k)) :
    GprFree k (LDST.exec_reg_pair_common i str) := by
  intro v s
  unfold LDST.exec_reg_pair_common
  simp only [reg_pair_operation_setGpr hk hn ht, write_pc_setGpr, read_pc_setGpr,
    write_err_setGpr, ite_setGpr]

theorem reg_pair_pre_indexed (hk : ¬ 31#5 = k) (i : Reg_pair_pre_indexed_cls) (hn : ¬ i.Rn = k)
    (ht : i.V = 1#1 ∨ (¬ i.Rt = k ∧ ¬ i.Rt2 = k)) :
    GprFree k (LDST.exec_reg_pair_pre_indexed i) := by
  intro v s; unfold LDST.exec_reg_pair_pre_indexed
  exact reg_pair_common hk _ _ hn (by simpa using ht) v s
theorem reg_pair_post_indexed (hk : ¬ 31#5 = k) (i : Reg_pair_post_indexed_cls) (hn : ¬ i.Rn = k)
    (ht : i.V = 1#1 ∨ (¬ i.Rt = k ∧ ¬ i.Rt2 = k)) :
    GprFree k (LDST.exec_reg_pair_post_indexed i) := by
  intro v s; unfold LDST.exec_reg_pair_post_indexed
  exact reg_pair_common hk _ _ hn (by simpa using ht) v s
theorem reg_pair_signed_offset (hk : ¬ 31#5 = k) (i : Reg_pair_signed_offset_cls)
    (hn : ¬ i.Rn = k) (ht : i.V = 1#1 ∨ (¬ i.Rt = k ∧ ¬ i.Rt2 = k)) :
    GprFree k (LDST.exec_reg_pair_signed_offset i) := by
  intro v s; unfold LDST.exec_reg_pair_signed_offset
  exact reg_pair_common hk _ _ hn (by simpa using ht) v s
theorem reg_exclusive (hk : ¬ 31#5 = k) (i : Reg_exclusive_cls) (hs : ¬ i.Rs = k)
    (hn : ¬ i.Rn = k) (ht : ¬ i.Rt = k) : GprFree k (LDST.exec_reg_exclusive i) := by
  intro v s; unfold LDST.exec_reg_exclusive; gprfree
theorem reg_literal (hk : ¬ 31#5 = k) (i : Reg_literal_cls) (ht : i.V = 1#1 ∨ ¬ i.Rt = k) :
    GprFree k (LDST.exec_reg_literal i) := by
  intro v s; unfold LDST.exec_reg_literal
  rcases ht with ht | ht <;> gprfree

theorem reserved (hk : ¬ 31#5 = k) (i : ReservedInst) : GprFree k (Reserved.exec_reserved i) := by
  intro v s; cases i; unfold Reserved.exec_reserved Reserved.exec_udf; gprfree

end classes

/-! ## Every instruction -/

/-- **The general-purpose registers an instruction names** (module doc): the register fields
that may denote a GPR (a load/store's data registers only for a non-SIMD&FP access; the SIMD&FP
copy and conversion classes conservatively both), and `x30` for `bl`/`blr`. -/
def _root_.Arm.ArmInst.gprs : ArmInst → List (BitVec 5)
  | .DPI (.Add_sub_imm i) => [i.Rn, i.Rd]
  | .DPI (.PC_rel_addressing i) => [i.Rd]
  | .DPI (.Logical_imm i) => [i.Rn, i.Rd]
  | .DPI (.Bitfield i) => [i.Rn, i.Rd]
  | .DPI (.Move_wide_imm i) => [i.Rd]
  | .DPI (.Extract i) => [i.Rm, i.Rn, i.Rd]
  | .BR (.Compare_branch i) => [i.Rt]
  | .BR (.Uncond_branch_imm i) => if i.op = 1#1 then [30#5] else []
  | .BR (.Uncond_branch_reg i) => if i.opc = 0b0001#4 then [i.Rn, 30#5] else [i.Rn]
  | .BR (.Cond_branch_imm _) => []
  | .BR (.Hints _) => []
  | .BR (.Barrier _) => []
  | .BR (.Test_branch i) => [i.Rt]
  | .BR (.Mrs i) => [i.Rt]
  | .DPR (.Add_sub_carry i) => [i.Rm, i.Rn, i.Rd]
  | .DPR (.Add_sub_shifted_reg i) => [i.Rm, i.Rn, i.Rd]
  | .DPR (.Conditional_select i) => [i.Rm, i.Rn, i.Rd]
  | .DPR (.Data_processing_one_source i) => [i.Rn, i.Rd]
  | .DPR (.Data_processing_two_source i) => [i.Rm, i.Rn, i.Rd]
  | .DPR (.Logical_shifted_reg i) => [i.Rm, i.Rn, i.Rd]
  | .DPR (.Data_processing_three_source i) => [i.Rm, i.Ra, i.Rn, i.Rd]
  | .DPR (.Add_sub_ext_reg i) => [i.Rm, i.Rn, i.Rd]
  | .DPR (.Conditional_compare_imm i) => [i.Rn]
  | .DPR (.Conditional_compare_reg i) => [i.Rm, i.Rn]
  | .DPSFP (.Advanced_simd_copy i) => [i.Rn, i.Rd]
  | .DPSFP (.Conversion_between_FP_and_Int i) => [i.Rn, i.Rd]
  | .DPSFP _ => []
  | .LDST (.Reg_imm_post_indexed i) => i.Rn :: if i.V = 1#1 then [] else [i.Rt]
  | .LDST (.Reg_unsigned_imm i) => i.Rn :: if i.V = 1#1 then [] else [i.Rt]
  | .LDST (.Reg_unscaled_imm i) => i.Rn :: if i.VR = 1#1 then [] else [i.Rt]
  | .LDST (.Reg_pair_pre_indexed i) => i.Rn :: if i.V = 1#1 then [] else [i.Rt, i.Rt2]
  | .LDST (.Reg_pair_post_indexed i) => i.Rn :: if i.V = 1#1 then [] else [i.Rt, i.Rt2]
  | .LDST (.Reg_pair_signed_offset i) => i.Rn :: if i.V = 1#1 then [] else [i.Rt, i.Rt2]
  | .LDST (.Reg_imm_pre_indexed i) => i.Rn :: if i.V = 1#1 then [] else [i.Rt]
  | .LDST (.Reg_reg_offset i) => i.Rm :: i.Rn :: if i.V = 1#1 then [] else [i.Rt]
  | .LDST (.Reg_exclusive i) => [i.Rs, i.Rn, i.Rt]
  | .LDST (.Reg_literal i) => if i.V = 1#1 then [] else [i.Rt]
  | .RES _ => []

/-- A register the instruction names. -/
macro "gpr_named" : tactic => `(tactic| (simp_all [Arm.ArmInst.gprs]))

/-- **The general-purpose register footprint**: an instruction neither reads nor writes a GPR
`x_k` (`k ≠ 31`) it does not name. -/
theorem gprFree_exec_inst (ai : ArmInst) {k : BitVec 5} (hk : ¬ 31#5 = k)
    (h : ∀ x ∈ ai.gprs, ¬ x = k) : GprFree k (exec_inst ai) := by
  intro v s
  have m : ∀ x, x ∈ ai.gprs → ¬ x = k := h
  cases ai with
  | DPI x =>
    cases x with
    | Add_sub_imm i => exact add_sub_imm hk i (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Logical_imm i => exact logical_imm hk i (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | PC_rel_addressing i => exact pc_rel_addressing hk i (m _ (by gpr_named)) v s
    | Bitfield i => exact bitfield hk i (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Move_wide_imm i => exact move_wide_imm hk i (m _ (by gpr_named)) v s
    | Extract i =>
      exact extract hk i (m _ (by gpr_named)) (m _ (by gpr_named)) (m _ (by gpr_named)) v s
  | BR x =>
    cases x with
    | Compare_branch i => exact compare_branch hk i (m _ (by gpr_named)) v s
    | Uncond_branch_imm i =>
      exact uncond_branch_imm hk i (fun ho => m _ (by simp [Arm.ArmInst.gprs, ho])) v s
    | Uncond_branch_reg i =>
      refine uncond_branch_reg hk i ?_ (fun ho => m _ (by simp [Arm.ArmInst.gprs, ho])) v s
      exact m _ (by simp only [Arm.ArmInst.gprs]; split <;> simp)
    | Cond_branch_imm i => exact cond_branch_imm hk i v s
    | Hints i => exact hints hk i v s
    | Barrier i => exact barrier hk i v s
    | Test_branch i => exact test_branch hk i (m _ (by gpr_named)) v s
    | Mrs i => exact mrs hk i (m _ (by gpr_named)) v s
  | DPR x =>
    cases x with
    | Add_sub_carry i =>
      exact add_sub_carry hk i (m _ (by gpr_named)) (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Add_sub_shifted_reg i =>
      exact add_sub_shifted_reg hk i (m _ (by gpr_named)) (m _ (by gpr_named))
        (m _ (by gpr_named)) v s
    | Conditional_select i =>
      exact conditional_select hk i (m _ (by gpr_named)) (m _ (by gpr_named))
        (m _ (by gpr_named)) v s
    | Data_processing_one_source i =>
      exact data_processing_one_source hk i (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Data_processing_two_source i =>
      exact data_processing_two_source hk i (m _ (by gpr_named)) (m _ (by gpr_named))
        (m _ (by gpr_named)) v s
    | Logical_shifted_reg i =>
      exact logical_shifted_reg hk i (m _ (by gpr_named)) (m _ (by gpr_named))
        (m _ (by gpr_named)) v s
    | Data_processing_three_source i =>
      exact data_processing_three_source hk i (m _ (by gpr_named)) (m _ (by gpr_named))
        (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Add_sub_ext_reg i =>
      exact add_sub_ext_reg hk i (m _ (by gpr_named)) (m _ (by gpr_named))
        (m _ (by gpr_named)) v s
    | Conditional_compare_imm i => exact conditional_compare_imm hk i (m _ (by gpr_named)) v s
    | Conditional_compare_reg i =>
      exact conditional_compare_reg hk i (m _ (by gpr_named)) (m _ (by gpr_named)) v s
  | DPSFP x =>
    cases x with
    | Advanced_simd_two_reg_misc i => exact advanced_simd_two_reg_misc hk i v s
    | Advanced_simd_copy i =>
      exact advanced_simd_copy hk i (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Advanced_simd_three_same i => exact advanced_simd_three_same hk i v s
    | Conversion_between_FP_and_Int i =>
      exact conversion_between_FP_and_Int hk i (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Advanced_simd_across_lanes i => exact advanced_simd_across_lanes hk i v s
    | FP_data_processing_one_source i => exact fp_data_processing_one_source hk i v s
    | FP_immediate i => exact fp_immediate hk i v s
    | FP_conditional_select i => exact fp_conditional_select hk i v s
    | Advanced_simd_modified_immediate i => exact advanced_simd_modified_immediate hk i v s
    | FP_data_processing_two_source i => exact fp_data_processing_two_source hk i v s
    | FP_data_processing_three_source i => exact fp_data_processing_three_source hk i v s
    | FP_compare i => exact fp_compare hk i v s
  | LDST x =>
    cases x with
    | Reg_imm_post_indexed i =>
      refine reg_imm_post_indexed hk i (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr (m _ (by simp [Arm.ArmInst.gprs, hv]))
    | Reg_unsigned_imm i =>
      refine reg_imm_unsigned_offset hk i (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr (m _ (by simp [Arm.ArmInst.gprs, hv]))
    | Reg_unscaled_imm i =>
      refine reg_unscaled_imm hk i (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.VR = 1#1
      · exact .inl hv
      · exact .inr (m _ (by simp [Arm.ArmInst.gprs, hv]))
    | Reg_pair_pre_indexed i =>
      refine reg_pair_pre_indexed hk i (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr ⟨m _ (by simp [Arm.ArmInst.gprs, hv]), m _ (by simp [Arm.ArmInst.gprs, hv])⟩
    | Reg_pair_post_indexed i =>
      refine reg_pair_post_indexed hk i (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr ⟨m _ (by simp [Arm.ArmInst.gprs, hv]), m _ (by simp [Arm.ArmInst.gprs, hv])⟩
    | Reg_pair_signed_offset i =>
      refine reg_pair_signed_offset hk i (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr ⟨m _ (by simp [Arm.ArmInst.gprs, hv]), m _ (by simp [Arm.ArmInst.gprs, hv])⟩
    | Reg_imm_pre_indexed i =>
      refine reg_imm_pre_indexed hk i (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr (m _ (by simp [Arm.ArmInst.gprs, hv]))
    | Reg_reg_offset i =>
      refine reg_reg_offset hk i (m _ (by gpr_named)) (m _ (by gpr_named)) ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr (m _ (by simp [Arm.ArmInst.gprs, hv]))
    | Reg_exclusive i =>
      exact reg_exclusive hk i (m _ (by gpr_named)) (m _ (by gpr_named)) (m _ (by gpr_named)) v s
    | Reg_literal i =>
      refine reg_literal hk i ?_ v s
      by_cases hv : i.V = 1#1
      · exact .inl hv
      · exact .inr (m _ (by simp [Arm.ArmInst.gprs, hv]))
  | RES i => exact reserved hk i v s

end E2E.GprFoot

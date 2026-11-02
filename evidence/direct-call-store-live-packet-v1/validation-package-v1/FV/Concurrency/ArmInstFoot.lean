import FV.Concurrency.ArmThread

/-!
# Precise footprints of every Arm instruction (T2h, #311, layer 1)

`ArmThread.Footprint f s evs` says that the step `f` at `s` reads and writes memory only through
the events `evs`. T2d proved it for the non-memory classes (no event) and for `ldar`/`ldaxr`/
`stlr`/`stlxr` at a `stepi` (`footprint_load_excl`, `footprint_store_excl`). This file gives
**every instruction its precise footprint, as a function of the state**:

* `instEvs ai s`: the events of `exec_inst ai` at `s`, with the case split of the semantics: the
  access of a single-register load/store (`immEvs`: unsigned, unscaled, pre- and post-indexed and
  register-offset forms, GPR and SIMD&FP; `ldsturEvs`), of a pair (`pairEvs`: one access of both
  registers' bytes), of a literal load (`literalEvs`), of an exclusive or acquire/release access
  (`exclEvs`, kinds `exclKind`), the barrier event of a full barrier, none otherwise; a read event's
  bytes are those of `s`'s memory, a write event's those of the source registers;
* `footprint_exec_inst`: `Footprint (exec_inst ai) s (instEvs ai s)` for every `ai` and `s`;
* `stepEvs s` and `footprint_stepi`: the same for `stepi` (no event at an error or when nothing is
  decoded, except the barrier event of a full barrier); `kindsOk_stepEvs`: the events have the
  kinds `ArmThread.KindsOk` asks of the instruction's class (`cls`).

The footprint shapes are `foot_none`/`foot_read`/`foot_write`: an instruction that depends on the
memory only through `n` bytes at `a` (resp. writes exactly `v` there) has the read (write) event.
Plan: `docs/plans/atomics.md` §3e.
-/

namespace Concurrency.ArmInstFoot

open Arm ArmFoot ArmThread

/-! ## Footprint shapes -/

theorem foot_none {f : ArmState → ArmState} {s : ArmState}
    (h : ∀ m m', f (setMem m s) = setMem m (f (setMem m' s))) : Footprint f s [] := by
  intro m _
  simp only [applyR, applyW]
  exact h m s.mem

theorem foot_read {f : ArmState → ArmState} {s : ArmState} {k : AKind} (hk : k.dir = .R)
    {a : BitVec 64} {n : Nat} (hn : n ≤ 2 ^ 64)
    (h : ∀ m m', readM n a m = readM n a m' → f (setMem m s) = setMem m (f (setMem m' s)))
    (v : BitVec (n * 8)) : Footprint f s [⟨k, a, n, v⟩] := by
  intro m hm
  have hv : readM n a m = v := hm _ List.mem_cons_self hk
  simp only [applyR, applyW, hk, show (Dir.R = Dir.W) = False from by simp, ite_true, ite_false]
  exact h m _ (by rw [hv, readM_writeM _ _ _ _ hn])

theorem foot_write {f : ArmState → ArmState} {s : ArmState} {k : AKind} (hk : k.dir = .W)
    {a : BitVec 64} {n : Nat} {v : BitVec (n * 8)}
    (h : ∀ m m', f (setMem m s) = setMem (writeM n a v m) (f (setMem m' s))) :
    Footprint f s [⟨k, a, n, v⟩] := by
  intro m _
  simp only [applyR, applyW, hk, show (Dir.W = Dir.R) = False from by simp, ite_true, ite_false]
  exact h m s.mem

/-! ## Load/store register (immediate, register offset) -/

theorem shl_div (sc : Nat) : (8 <<< sc) / 8 * 8 = 8 <<< sc := by
  simp only [Nat.shiftLeft_eq]; rw [Nat.mul_comm 8, Nat.mul_div_cancel _ (by decide)]

theorem read_gpr_sm (n : Nat) (i : BitVec 5) (m : Memory) (s : ArmState) :
    read_gpr n i (setMem m s) = read_gpr n i s := by simp only [read_gpr, r_setMem]

theorem read_gpr_zr_sm (n : Nat) (i : BitVec 5) (m : Memory) (s : ArmState) :
    read_gpr_zr n i (setMem m s) = read_gpr_zr n i s := by
  simp only [read_gpr_zr, read_gpr_sm]

theorem check_sp_sm (m : Memory) (s : ArmState) :
    CheckSPAlignment (setMem m s) ↔ CheckSPAlignment s := by
  simp only [CheckSPAlignment, read_gpr_sm]

theorem offset_value_sm (o : LDST.Reg_offset) (sc : Nat) (m : Memory) (s : ArmState) :
    o.value sc (setMem m s) = o.value sc s := by
  cases o <;> simp only [LDST.Reg_offset.value, read_gpr_zr_sm]

theorem pc_sm (m : Memory) (s : ArmState) : read_pc (setMem m s) = read_pc s := by
  simp only [read_pc, r_setMem]

theorem writeM_setMem (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (m : Memory) (s : ArmState) :
    write_mem_bytes n a v (setMem m s) = setMem (writeM n a v m) s := by
  rw [write_mem_bytes_eq]; rfl

theorem readM_setMem (n : Nat) (a : BitVec 64) (m : Memory) (s : ArmState) :
    read_mem_bytes n a (setMem m s) = readM n a m := by
  rw [read_mem_bytes_eq]; rfl

/-- The access of a single-register load/store (`exec_reg_imm_common`), with the same case
split as the semantics. -/
def immEvs (inst : LDST.Reg_imm_cls) (s : ArmState) : List Ev :=
  let scale := if inst.SIMD? then ((BitVec.lsb inst.opc 1) ++ inst.size).toNat
    else inst.size.toNat
  if inst.SIMD? ∧ ¬ LDST.supported_simd_reg_imm inst.size inst.opc then []
  else if inst.SIMD? ∧ scale > 4 then []
  else if ¬ inst.SIMD? ∧ inst.size = 0b11#2 ∧ inst.opc = 0b10#2 then []
  else if ¬ inst.SIMD? ∧ BitVec.lsb inst.size 1 = 1#1 ∧ inst.opc = 0b11#2 then []
  else if LDST.reg_imm_constrain_unpredictable inst.wback inst.SIMD? inst.Rn inst.Rt then []
  else
    let datasize := 8 <<< scale
    let signed := ¬ inst.SIMD? ∧ BitVec.lsb inst.opc 1 = 1#1
    let memop : BitVec 1 := if signed then 1#1 else BitVec.lsb inst.opc 0
    let base := read_gpr 64 inst.Rn s
    let address := if inst.postindex then base else base + inst.imm.value scale s
    if inst.Rn = 31#5 ∧ ¬ CheckSPAlignment s then []
    else if memop = 0#1 then
      [⟨.plainW, address, datasize / 8,
        BitVec.cast (shl_div scale).symm (ldst_read inst.SIMD? datasize inst.Rt s)⟩]
    else [⟨.plainR, address, datasize / 8, readM (datasize / 8) address s.mem⟩]

theorem foot_err (e : StateError) (s : ArmState) : Footprint (write_err e) s [] :=
  foot_none fun m m' => by simp only [write_err, w_setMem, setMem_setMem]

theorem check_sp_sm' (m : Memory) (s : ArmState) :
    CheckSPAlignment (setMem m s) = CheckSPAlignment s := propext (check_sp_sm m s)

theorem read_sfp_sm (n : Nat) (i : BitVec 5) (m : Memory) (s : ArmState) :
    read_sfp n i (setMem m s) = read_sfp n i s := by simp only [read_sfp, r_setMem]

theorem ldst_read_sm (b : Bool) (n : Nat) (i : BitVec 5) (m : Memory) (s : ArmState) :
    ldst_read b n i (setMem m s) = ldst_read b n i s := by
  simp only [ldst_read, read_sfp_sm, read_gpr_zr_sm]

theorem write_gpr_sm (n : Nat) (i : BitVec 5) (v : BitVec n) (m : Memory) (s : ArmState) :
    write_gpr n i v (setMem m s) = setMem m (write_gpr n i v s) := by
  simp only [write_gpr, w_setMem]

theorem write_gpr_zr_sm (n : Nat) (i : BitVec 5) (v : BitVec n) (m : Memory) (s : ArmState) :
    write_gpr_zr n i v (setMem m s) = setMem m (write_gpr_zr n i v s) := by
  simp only [write_gpr_zr, write_gpr_sm]; split <;> rfl

theorem write_sfp_sm (n : Nat) (i : BitVec 5) (v : BitVec n) (m : Memory) (s : ArmState) :
    write_sfp n i v (setMem m s) = setMem m (write_sfp n i v s) := by
  simp only [write_sfp, w_setMem]

theorem write_pc_sm (v : BitVec 64) (m : Memory) (s : ArmState) :
    write_pc v (setMem m s) = setMem m (write_pc v s) := by
  simp only [write_pc, w_setMem]

theorem write_err_sm (e : StateError) (m : Memory) (s : ArmState) :
    write_err e (setMem m s) = setMem m (write_err e s) := by
  simp only [write_err, w_setMem]

theorem footprint_reg_imm (inst : LDST.Reg_imm_cls) (str : String) (s : ArmState) :
    Footprint (LDST.exec_reg_imm_common inst str) s (immEvs inst s) := by
  intro m hm
  unfold immEvs at hm ⊢
  unfold LDST.exec_reg_imm_common LDST.reg_imm_operation
  simp only [read_gpr_sm, check_sp_sm', offset_value_sm, pc_sm, readM_setMem, ldst_read_sm] at hm ⊢
  by_cases h1 : inst.SIMD? = true ∧ ¬ LDST.supported_simd_reg_imm inst.size inst.opc = true
  · simp only [ite_eq_left h1, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h1] at hm ⊢
  by_cases h2 : inst.SIMD? = true ∧ (if inst.SIMD? = true then (BitVec.lsb inst.opc 1 ++ inst.size).toNat
    else inst.size.toNat) > 4
  · simp only [ite_eq_left h2, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h2] at hm ⊢
  by_cases h3 : ¬inst.SIMD? = true ∧ inst.size = 3#2 ∧ inst.opc = 2#2
  · simp only [ite_eq_left h3, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h3] at hm ⊢
  by_cases h4 : ¬inst.SIMD? = true ∧ BitVec.lsb inst.size 1 = 1#1 ∧ inst.opc = 3#2
  · simp only [ite_eq_left h4, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h4] at hm ⊢
  by_cases h5 : LDST.reg_imm_constrain_unpredictable inst.wback inst.SIMD? inst.Rn inst.Rt = true
  · simp only [ite_eq_left h5, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h5] at hm ⊢
  by_cases h6 : inst.Rn = 31#5 ∧ ¬CheckSPAlignment s
  · simp only [ite_eq_left h6, applyR, applyW, write_err_sm, write_pc_sm, setMem_setMem]
  simp only [ite_eq_right h6] at hm ⊢
  generalize (if ¬inst.SIMD? = true ∧ BitVec.lsb inst.opc 1 = 1#1 then 1#1
    else BitVec.lsb inst.opc 0) = op at hm ⊢
  by_cases h7 : op = 0#1
  · subst h7
    simp only [ite_true, applyR, applyW, AKind.dir, show (Dir.W = Dir.R) = False from by simp,
      ite_false, setMem_self, write_mem_bytes_eq, setMem_mem, write_gpr_sm,
      write_pc_sm, ite_setMem, setMem_setMem]
  · obtain rfl : op = 1#1 := by bv_omega
    simp only [show ((1#1 : BitVec 1) = 0#1) = False from by decide, ite_false] at hm ⊢
    generalize (if inst.postindex = true then read_gpr 64 inst.Rn s else read_gpr 64 inst.Rn s +
      inst.imm.value (if inst.SIMD? = true then (BitVec.lsb inst.opc 1 ++ inst.size).toNat
        else inst.size.toNat) s) = A at hm ⊢
    have hv := hm _ List.mem_cons_self rfl
    simp only at hv
    simp only [applyR, applyW, AKind.dir, show (Dir.R = Dir.W) = False from by simp, ite_true,
      ite_false, writeM_readM, hv, setMem_self, write_gpr_sm, write_gpr_zr_sm, write_sfp_sm,
      write_pc_sm, ite_setMem]

/-! ## Load/store register (unscaled immediate, SIMD&FP) -/

theorem shl_div' (sc : Nat) : 8 <<< sc = (8 <<< sc) / 8 * 8 := (shl_div sc).symm

/-- The access of `LDUR`/`STUR` (SIMD&FP). -/
def ldsturEvs (inst : Reg_unscaled_imm_cls) (s : ArmState) : List Ev :=
  let scale := (BitVec.extractLsb' 1 1 inst.opc ++ inst.size).toNat
  if scale > 4 then []
  else if inst.Rn = 31#5 ∧ ¬ CheckSPAlignment s then []
  else
    let address := read_gpr 64 inst.Rn s + BitVec.signExtend 64 inst.imm9
    if BitVec.getLsbD inst.opc 0 = true then
      [⟨.plainR, address, (8 <<< scale) / 8, readM ((8 <<< scale) / 8) address s.mem⟩]
    else
      [⟨.plainW, address, (8 <<< scale) / 8,
        BitVec.cast (shl_div' scale) (read_sfp (8 <<< scale) inst.Rt s)⟩]

theorem footprint_ldstur (inst : Reg_unscaled_imm_cls) (s : ArmState) :
    Footprint (LDST.exec_ldstur inst) s (ldsturEvs inst s) := by
  intro m hm
  unfold ldsturEvs at hm ⊢
  unfold LDST.exec_ldstur
  simp only [read_gpr_sm, check_sp_sm', readM_setMem, read_sfp_sm] at hm ⊢
  by_cases h1 : (BitVec.extractLsb' 1 1 inst.opc ++ inst.size).toNat > 4
  · simp only [ite_eq_left h1, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h1] at hm ⊢
  by_cases h2 : inst.Rn = 31#5 ∧ ¬CheckSPAlignment s
  · simp only [ite_eq_left h2, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h2] at hm ⊢
  generalize read_gpr 64 inst.Rn s + BitVec.signExtend 64 inst.imm9 = A at hm ⊢
  by_cases h3 : BitVec.getLsbD inst.opc 0 = true
  · simp only [h3, ite_true] at hm ⊢
    have hv := hm _ List.mem_cons_self rfl
    simp only at hv
    simp only [applyR, applyW, AKind.dir, show (Dir.R = Dir.W) = False from by simp, ite_true,
      ite_false, writeM_readM, hv, setMem_self, write_sfp_sm, write_pc_sm, pc_sm,
      show (MemOp.MemOp_LOAD = MemOp.MemOp_STORE) = False from by simp]
  · simp only [h3, ite_false, Bool.false_eq_true] at hm ⊢
    simp only [applyR, applyW, AKind.dir, show (Dir.W = Dir.R) = False from by simp, ite_true,
      ite_false, setMem_self, write_mem_bytes_eq, setMem_mem, write_pc_sm, pc_sm, setMem_setMem]

/-! ## Load/store register pair -/

/-- The access of `LDP`/`STP` (`exec_reg_pair_common`): one access of both registers' bytes. -/
def pairEvs (inst : LDST.Reg_pair_cls) (s : ArmState) : List Ev :=
  if (!inst.SIMD? ∧ ((!inst.L? ∧ BitVec.lsb inst.opc 0 = 1#1) ∨ (inst.opc = 0b11#2))
      ∨ inst.SIMD? ∧ (inst.opc = 0b11#2)
      ∨ LDST.reg_pair_constrain_unpredictable inst.wback inst) then []
  else
    let scale := if !inst.SIMD? then 2 + (BitVec.toNat (BitVec.lsb inst.opc 1))
      else 2 + (BitVec.toNat inst.opc)
    let datasize := 8 <<< scale
    let offset := (BitVec.signExtend 64 inst.imm7) <<< scale
    if inst.Rn = 31#5 ∧ ¬ CheckSPAlignment s then []
    else
      let address := if inst.postindex then read_gpr 64 inst.Rn s
        else read_gpr 64 inst.Rn s + offset
      match inst.L? with
      | false =>
        have h3 : datasize + datasize = 2 * (datasize / 8) * 8 := by
          rw [Nat.mul_assoc, shl_div]; omega
        [⟨.plainW, address, 2 * (datasize / 8), BitVec.cast h3
          (ldst_read inst.SIMD? datasize inst.Rt2 s ++ ldst_read inst.SIMD? datasize inst.Rt s)⟩]
      | true => [⟨.plainR, address, 2 * (datasize / 8),
          readM (2 * (datasize / 8)) address s.mem⟩]

theorem footprint_reg_pair (inst : LDST.Reg_pair_cls) (str : String) (s : ArmState) :
    Footprint (LDST.exec_reg_pair_common inst str) s (pairEvs inst s) := by
  intro m hm
  unfold pairEvs at hm ⊢
  unfold LDST.exec_reg_pair_common LDST.reg_pair_operation
  simp only [read_gpr_sm, check_sp_sm', pc_sm, readM_setMem, ldst_read_sm] at hm ⊢
  split
  · rename_i h1
    simp only [applyR, applyW, write_err_sm, setMem_setMem]
  rename_i h1
  simp only [h1, ite_false] at hm ⊢
  by_cases h2 : inst.Rn = 31#5 ∧ ¬CheckSPAlignment s
  · simp only [ite_eq_left h2, applyR, applyW, write_err_sm, write_pc_sm, setMem_setMem]
  simp only [ite_eq_right h2] at hm ⊢
  generalize (if inst.postindex = true then read_gpr 64 inst.Rn s else read_gpr 64 inst.Rn s +
    BitVec.signExtend 64 inst.imm7 <<< (if (!inst.SIMD?) = true then
      2 + (BitVec.lsb inst.opc 1).toNat else 2 + inst.opc.toNat)) = A at hm ⊢
  cases hL : inst.L?
  · simp only [hL] at hm ⊢
    simp only [applyR, applyW, AKind.dir, show (Dir.W = Dir.R) = False from by simp, ite_true,
      ite_false, setMem_self, write_mem_bytes_eq, setMem_mem, write_gpr_sm, write_pc_sm, ite_setMem,
      setMem_setMem]
  · simp only [hL] at hm ⊢
    have hv := hm _ List.mem_cons_self rfl
    simp only at hv
    simp only [applyR, applyW, AKind.dir, show (Dir.R = Dir.W) = False from by simp, ite_true,
      ite_false, writeM_readM, hv, setMem_self, write_gpr_sm, write_gpr_zr_sm, write_sfp_sm,
      ldst_write, write_pc_sm, ite_setMem]

/-! ## Load register (literal) -/

/-- The read of a literal load of `n` bytes. -/
def litEv (n : Nat) (inst : Reg_literal_cls) (s : ArmState) : List Ev :=
  [⟨.plainR, LDST.literal_address inst.imm19 s, n,
    readM n (LDST.literal_address inst.imm19 s) s.mem⟩]

/-- The access of a literal load. -/
def literalEvs (inst : Reg_literal_cls) (s : ArmState) : List Ev :=
  if inst.opc = 0b00#2 then litEv 4 inst s
  else if inst.opc = 0b01#2 then litEv 8 inst s
  else if inst.opc = 0b10#2 then litEv (if inst.V = 1#1 then 16 else 4) inst s
  else []

theorem lit_shape (inst : Reg_literal_cls) {n : Nat} (hn : n ≤ 2 ^ 64)
    (h : ∀ (m m' : Memory) (s : ArmState),
      readM n (LDST.literal_address inst.imm19 s) m = readM n (LDST.literal_address inst.imm19 s) m' →
      LDST.exec_reg_literal inst (setMem m s) = setMem m (LDST.exec_reg_literal inst (setMem m' s)))
    (s : ArmState) : Footprint (LDST.exec_reg_literal inst) s (litEv n inst s) :=
  foot_read rfl hn (fun m m' hmm => h m m' s hmm) _

theorem footprint_literal (inst : Reg_literal_cls) (s : ArmState) :
    Footprint (LDST.exec_reg_literal inst) s (literalEvs inst s) := by
  have hopc : inst.opc = 0#2 ∨ inst.opc = 1#2 ∨ inst.opc = 2#2 ∨ inst.opc = 3#2 := by bv_omega
  rcases hopc with h | h | h | h
  · rw [show literalEvs inst s = litEv 4 inst s by simp only [literalEvs, h, ite_true]]
    refine lit_shape inst (by decide) (fun m m' s hmm => ?_) s
    unfold LDST.exec_reg_literal
    simp only [h, LDST.literal_address, pc_sm, read_mem_bytes_eq, setMem_mem] at hmm ⊢
    rw [hmm]
    by_cases hV : inst.V = 1#1 <;> simp only [hV, ite_true, ite_false, write_sfp_sm,
      write_gpr_zr_sm, write_pc_sm, setMem_setMem]
  · rw [show literalEvs inst s = litEv 8 inst s by
      simp only [literalEvs, h, ite_false, ite_true, show ((1#2 : BitVec 2) = 0#2) = False by decide]]
    refine lit_shape inst (by decide) (fun m m' s hmm => ?_) s
    unfold LDST.exec_reg_literal
    simp only [h, LDST.literal_address, pc_sm, read_mem_bytes_eq, setMem_mem] at hmm ⊢
    rw [hmm]
    by_cases hV : inst.V = 1#1 <;> simp only [hV, ite_true, ite_false, write_sfp_sm,
      write_gpr_zr_sm, write_pc_sm, setMem_setMem]
  · by_cases hV : inst.V = 1#1
    · rw [show literalEvs inst s = litEv 16 inst s by
        simp only [literalEvs, h, hV, ite_false, ite_true, show ((2#2 : BitVec 2) = 0#2) = False by
          decide, show ((2#2 : BitVec 2) = 1#2) = False by decide]]
      refine lit_shape inst (by decide) (fun m m' s hmm => ?_) s
      unfold LDST.exec_reg_literal
      simp only [h, hV, LDST.literal_address, pc_sm, read_mem_bytes_eq, setMem_mem,
        ite_true] at hmm ⊢
      rw [hmm]
      simp only [write_sfp_sm, write_pc_sm, setMem_setMem]
    · rw [show literalEvs inst s = litEv 4 inst s by
        simp only [literalEvs, h, hV, ite_false, ite_true, show ((2#2 : BitVec 2) = 0#2) = False by
          decide, show ((2#2 : BitVec 2) = 1#2) = False by decide]]
      refine lit_shape inst (by decide) (fun m m' s hmm => ?_) s
      unfold LDST.exec_reg_literal
      simp only [h, hV, LDST.literal_address, pc_sm, read_mem_bytes_eq, setMem_mem,
        ite_false] at hmm ⊢
      rw [hmm]
      simp only [write_gpr_zr_sm, write_pc_sm, setMem_setMem]
  · rw [show literalEvs inst s = [] by
      simp only [literalEvs, h, ite_false, show ((3#2 : BitVec 2) = 0#2) = False by decide,
        show ((3#2 : BitVec 2) = 1#2) = False by decide, show ((3#2 : BitVec 2) = 2#2) = False by
        decide]]
    refine foot_none fun m m' => ?_
    unfold LDST.exec_reg_literal
    simp only [h]
    by_cases hV : inst.V = 1#1 <;> simp only [hV, ite_true, ite_false] <;>
      (repeat' split) <;> first
        | (rename_i hh; simp at hh; done)
        | (rename_i hh _; simp at hh; done)
        | simp only [write_err_sm, setMem_setMem]

/-! ## Load/store exclusive, load-acquire/store-release -/

/-- The kind of the access of an exclusive / acquire-release instruction (as `ArmThread.Cls.kind`
of its class). -/
def exclKind (inst : Reg_exclusive_cls) : AKind :=
  if inst.L = 1#1 then (if inst.ord = 1#1 then .acqR else if inst.o0 = 1#1 then .acqXR else .plainR)
  else (if inst.ord = 1#1 then .relW else if inst.o0 = 1#1 then .relXW else .plainW)

theorem exclKind_R {inst : Reg_exclusive_cls} (h : inst.L = 1#1) : (exclKind inst).dir = .R := by
  simp only [exclKind, h, ite_true]; split <;> (try split) <;> rfl

theorem exclKind_W {inst : Reg_exclusive_cls} (h : ¬ inst.L = 1#1) : (exclKind inst).dir = .W := by
  simp only [exclKind, h, ite_false]; split <;> (try split) <;> rfl

/-- The access of `ldar`/`ldxr`/`ldaxr`/`stlr`/`stxr`/`stlxr` (a store exclusive of the model
always succeeds). -/
def exclEvs (inst : Reg_exclusive_cls) (s : ArmState) : List Ev :=
  if inst.Rn = 31#5 ∧ ¬ CheckSPAlignment s then []
  else if inst.L = 1#1 then
    [⟨exclKind inst, read_gpr 64 inst.Rn s, (8 <<< inst.size.toNat) / 8,
      readM ((8 <<< inst.size.toNat) / 8) (read_gpr 64 inst.Rn s) s.mem⟩]
  else
    [⟨exclKind inst, read_gpr 64 inst.Rn s, (8 <<< inst.size.toNat) / 8,
      BitVec.cast (shl_div' _) (ldst_read false (8 <<< inst.size.toNat) inst.Rt s)⟩]

theorem footprint_excl (inst : Reg_exclusive_cls) (s : ArmState) :
    Footprint (LDST.exec_reg_exclusive inst) s (exclEvs inst s) := by
  intro m hm
  unfold exclEvs at hm ⊢
  unfold LDST.exec_reg_exclusive
  simp only [read_gpr_sm, check_sp_sm', readM_setMem, ldst_read_sm] at hm ⊢
  by_cases h1 : inst.Rn = 31#5 ∧ ¬CheckSPAlignment s
  · simp only [ite_eq_left h1, applyR, applyW, write_err_sm, setMem_setMem]
  simp only [ite_eq_right h1] at hm ⊢
  by_cases hL : inst.L = 1#1
  · simp only [hL, ite_true] at hm ⊢
    have hv := hm _ List.mem_cons_self (exclKind_R hL)
    simp only at hv
    simp only [applyR, applyW, exclKind_R hL, show (Dir.R = Dir.W) = False from by simp, ite_true,
      ite_false, writeM_readM, hv, setMem_self, write_gpr_zr_sm, write_pc_sm, pc_sm]
  · simp only [hL, ite_false] at hm ⊢
    simp only [applyR, applyW, exclKind_W hL, show (Dir.W = Dir.R) = False from by simp, ite_true,
      ite_false, setMem_self, write_mem_bytes_eq, setMem_mem, write_gpr_zr_sm, write_pc_sm, pc_sm,
      setMem_setMem]

/-! ## Every instruction -/

/-- The barrier event of a full `dmb`/`dsb` (`ArmThread.cls`: `.dmb`). -/
def dmbEv : Ev := ⟨.dmb, 0, 0, 0#0⟩

/-- Whether a barrier is a full barrier (as `ArmThread.cls`). -/
def fullBarrier (i : Barrier_cls) : Prop :=
  (i.op2 = 0b101#3 ∨ i.op2 = 0b100#3) ∧ i.CRm.extractLsb' 0 2 = 0b11#2

instance (i : Barrier_cls) : Decidable (fullBarrier i) := by unfold fullBarrier; infer_instance

/-- **The memory events of an instruction executed in state `s`**: the access of a load/store
(the read bytes from `s`'s memory), the barrier event of a full barrier, none otherwise. -/
def instEvs : ArmInst → ArmState → List Ev
  | .LDST (.Reg_imm_post_indexed i), s =>
    immEvs ⟨i.size, i.opc, i.Rn, i.Rt, i.V = 1#1, true, true, .simm9 i.imm9⟩ s
  | .LDST (.Reg_unsigned_imm i), s =>
    immEvs ⟨i.size, i.opc, i.Rn, i.Rt, i.V = 1#1, false, false, .uimm12 i.imm12⟩ s
  | .LDST (.Reg_unscaled_imm i), s =>
    if i.VR = 0b1#1 then ldsturEvs i s
    else immEvs ⟨i.size, i.opc, i.Rn, i.Rt, false, false, false, .simm9 i.imm9⟩ s
  | .LDST (.Reg_pair_pre_indexed i), s =>
    pairEvs ⟨i.opc, i.V = 1#1, i.L = 1#1, true, false, i.imm7, i.Rt2, i.Rn, i.Rt⟩ s
  | .LDST (.Reg_pair_post_indexed i), s =>
    pairEvs ⟨i.opc, i.V = 1#1, i.L = 1#1, true, true, i.imm7, i.Rt2, i.Rn, i.Rt⟩ s
  | .LDST (.Reg_pair_signed_offset i), s =>
    pairEvs ⟨i.opc, i.V = 1#1, i.L = 1#1, false, false, i.imm7, i.Rt2, i.Rn, i.Rt⟩ s
  | .LDST (.Reg_imm_pre_indexed i), s =>
    immEvs ⟨i.size, i.opc, i.Rn, i.Rt, i.V = 1#1, true, false, .simm9 i.imm9⟩ s
  | .LDST (.Reg_reg_offset i), s =>
    if BitVec.lsb i.option 1 = 0#1 then []
    else immEvs ⟨i.size, i.opc, i.Rn, i.Rt, i.V = 1#1, false, false, .reg i.Rm i.option i.S⟩ s
  | .LDST (.Reg_exclusive i), s => exclEvs i s
  | .LDST (.Reg_literal i), s => literalEvs i s
  | .BR (.Barrier i), _ => if fullBarrier i then [dmbEv] else []
  | _, _ => []

theorem foot_memFree {f : ArmState → ArmState} {s : ArmState} (h : MemFree f) :
    Footprint f s [] :=
  foot_none fun m m' => by rw [h, h m' s, setMem_setMem]

theorem foot_memFree_dmb {f : ArmState → ArmState} {s : ArmState} (h : MemFree f) :
    Footprint f s [dmbEv] := by
  intro m _
  simp only [applyR, applyW, dmbEv, AKind.dir, show (Dir.F = Dir.R) = False from by simp,
    show (Dir.F = Dir.W) = False from by simp, ite_false]
  rw [h, h s.mem s, setMem_setMem]

/-- **Every instruction has a precise footprint**: run on any memory holding the bytes of its
read events, it writes exactly its write events (`instEvs`) and leaves the same registers. -/
theorem footprint_exec_inst (ai : ArmInst) (s : ArmState) :
    Footprint (exec_inst ai) s (instEvs ai s) := by
  cases ai with
  | LDST i =>
    cases i with
    | Reg_imm_post_indexed i => exact footprint_reg_imm _ _ s
    | Reg_unsigned_imm i => exact footprint_reg_imm _ _ s
    | Reg_unscaled_imm i =>
      show Footprint (LDST.exec_reg_unscaled_imm i) s _
      unfold LDST.exec_reg_unscaled_imm instEvs
      by_cases h : i.VR = 0b1#1
      · simp only [h, ite_true]; exact footprint_ldstur i s
      · simp only [h, ite_false]; exact footprint_reg_imm _ _ s
    | Reg_pair_pre_indexed i => exact footprint_reg_pair _ _ s
    | Reg_pair_post_indexed i => exact footprint_reg_pair _ _ s
    | Reg_pair_signed_offset i => exact footprint_reg_pair _ _ s
    | Reg_imm_pre_indexed i => exact footprint_reg_imm _ _ s
    | Reg_reg_offset i =>
      show Footprint (LDST.exec_reg_reg_offset i) s _
      unfold LDST.exec_reg_reg_offset instEvs
      by_cases h : BitVec.lsb i.option 1 = 0#1
      · simp only [h, ite_true]
        exact foot_none fun m m' => by simp only [write_err_sm, setMem_setMem]
      · simp only [h, ite_false]; exact footprint_reg_imm _ _ s
    | Reg_exclusive i => exact footprint_excl i s
    | Reg_literal i => exact footprint_literal i s
  | BR i =>
    cases i with
    | Barrier i =>
      show Footprint (BR.exec_barrier i) s (if fullBarrier i then [dmbEv] else [])
      split
      · exact foot_memFree_dmb (fun m s => ArmFoot.barrier m s i)
      · exact foot_memFree (fun m s => ArmFoot.barrier m s i)
    | _ => exact foot_memFree fun m s => exec_nonldst (.BR _) rfl m s
  | DPI i => exact foot_memFree fun m s => exec_nonldst (.DPI i) rfl m s
  | DPR i => exact foot_memFree fun m s => exec_nonldst (.DPR i) rfl m s
  | DPSFP i => exact foot_memFree fun m s => exec_nonldst (.DPSFP i) rfl m s
  | RES i => exact foot_memFree fun m s => exec_nonldst (.RES i) rfl m s

/-! ## `stepi` -/

/-- The events of a step at an error (it does nothing): the barrier event of a full barrier. -/
def errEvs : ArmInst → List Ev
  | .BR (.Barrier i) => if fullBarrier i then [dmbEv] else []
  | _ => []

/-- **The memory events of a step** of `stepi` from `s`: the instruction's (`instEvs`) when `s`
is error-free and the pc holds an instruction; else none, except the barrier event of a full
barrier at the pc (a step at an error does nothing, so any barrier event is a footprint). -/
def stepEvs (s : ArmState) : List Ev :=
  match decodeAt s with
  | some ai => if read_err s = .None then instEvs ai s else errEvs ai
  | none => []

theorem stepi_err {s : ArmState} (h : read_err s ≠ .None) : stepi s = s := by
  unfold stepi; dsimp only; split
  · rename_i he; exact absurd he h
  · rfl

/-- **Every step of `stepi` has a precise footprint.** -/
theorem footprint_stepi (s : ArmState) : Footprint stepi s (stepEvs s) := by
  unfold stepEvs
  split
  · rename_i ai hd
    by_cases he : read_err s = .None
    · simp only [he, ite_true]
      intro m hm
      have he' : ∀ m', read_err (setMem m' s) = .None := fun m' => by
        simp only [read_err, r_setMem]; exact he
      have hd' : ∀ m', decodeAt (setMem m' s) = some ai := fun m' => by rw [decodeAt_setMem]; exact hd
      rw [stepi_of_decodeAt (he' _) (hd' _), stepi_of_decodeAt (he' _) (hd' _)]
      exact footprint_exec_inst ai s m hm
    · simp only [he, ite_false]
      have he' : ∀ m', read_err (setMem m' s) ≠ .None := fun m' => by
        simp only [read_err, r_setMem]; exact he
      have hfree : ∀ m m', stepi (setMem m s) = setMem m (stepi (setMem m' s)) := fun m m' => by
        rw [stepi_err (he' m), stepi_err (he' m'), setMem_setMem]
      unfold errEvs
      split
      · split
        · intro m _
          simp only [applyR, applyW, dmbEv, AKind.dir, show (Dir.F = Dir.R) = False from by simp,
            show (Dir.F = Dir.W) = False from by simp, ite_false]
          exact hfree m s.mem
        · exact foot_none hfree
      · exact foot_none hfree
  · rename_i hd
    refine foot_none fun m m' => ?_
    have h0 : ∀ ai, decodeAt s = some ai → ArmInst.isLDST ai = false := fun ai h => by
      rw [hd] at h; cases h
    rw [stepi_setMem m s h0, stepi_setMem m' s h0, setMem_setMem]

/-! ## Kinds -/

/-- Plain accesses only. -/
def Plain (evs : List Ev) : Prop := ∀ e ∈ evs, e.k = .plainR ∨ e.k = .plainW

theorem plain_nil : Plain [] := fun _ h => by cases h

theorem plain_single {e : Ev} (h : e.k = .plainR ∨ e.k = .plainW) : Plain [e] := by
  intro e' he'; simp only [List.mem_singleton] at he'; subst he'; exact h

theorem plain_ite {c : Prop} [Decidable c] {a b : List Ev} (ha : Plain a) (hb : Plain b) :
    Plain (if c then a else b) := by
  split
  · exact ha
  · exact hb

macro "plain_tac" : tactic => `(tactic| ((try dsimp only); repeat (first
  | exact plain_nil
  | exact plain_single (.inl rfl)
  | exact plain_single (.inr rfl)
  | apply plain_ite
  | split)))

theorem plain_immEvs (inst : LDST.Reg_imm_cls) (s : ArmState) : Plain (immEvs inst s) := by
  unfold immEvs; plain_tac

theorem plain_ldsturEvs (inst : Reg_unscaled_imm_cls) (s : ArmState) : Plain (ldsturEvs inst s) := by
  unfold ldsturEvs; plain_tac

theorem plain_pairEvs (inst : LDST.Reg_pair_cls) (s : ArmState) : Plain (pairEvs inst s) := by
  unfold pairEvs; plain_tac

theorem plain_literalEvs (inst : Reg_literal_cls) (s : ArmState) : Plain (literalEvs inst s) := by
  unfold literalEvs litEv; plain_tac

theorem kindsOk_plain {evs : List Ev} (h : Plain evs) : KindsOk .plain evs := by
  refine ⟨fun e he => ?_, (fun h => by cases h)⟩
  rcases h e he with hk | hk <;> rw [hk] <;> rfl

theorem kindsOk_nil (c : Cls) (hc : c ≠ .dmb) : KindsOk c [] :=
  And.intro (fun _ h => nomatch h) (fun h => absurd h hc)

/-- The class of an exclusive / acquire-release instruction (as `ArmThread.cls`). -/
def exclCls (i : Reg_exclusive_cls) : Cls :=
  if i.ord = 1#1 then (if i.L = 1#1 then .ldar else .stlr)
  else if i.L = 1#1 then .ldx (i.o0 = 1#1) i.Rn i.size else .stx (i.o0 = 1#1) i.Rs i.Rn

theorem exclCls_ne (i : Reg_exclusive_cls) : exclCls i ≠ .dmb := by
  unfold exclCls; split <;> (try split) <;> simp

theorem kindsOk_excl (i : Reg_exclusive_cls) (s : ArmState) : KindsOk (exclCls i) (exclEvs i s) := by
  refine ⟨fun e he => ?_, fun h => absurd h (exclCls_ne i)⟩
  unfold exclEvs at he
  split at he
  · cases he
  have hk : e.k = exclKind i := by
    split at he <;> simp only [List.mem_singleton] at he <;> subst he <;> rfl
  have hd : (exclKind i).dir = if i.L = 1#1 then .R else .W := by
    by_cases hL : i.L = 1#1
    · rw [exclKind_R hL]; simp [hL]
    · rw [exclKind_W hL]; simp [hL]
  rw [hk, hd]
  unfold exclCls exclKind
  by_cases hL : i.L = 1#1 <;> by_cases ho : i.ord = 1#1 <;> by_cases h0 : i.o0 = 1#1 <;>
    simp [ho, h0, hL, Cls.kind]

/-- The class of a decoded instruction (`ArmThread.cls`). -/
def clsOf : ArmInst → Cls
  | .LDST (.Reg_exclusive i) => exclCls i
  | .BR (.Barrier i) => if fullBarrier i then .dmb else if i.op2 = 0b010#3 then .clrex else .plain
  | _ => .plain

theorem cls_of_decode {s : ArmState} {ai : ArmInst} (h : decodeAt s = some ai) :
    cls s = clsOf ai := by
  unfold cls; rw [h]
  cases ai with
  | LDST i => cases i <;> rfl
  | BR i =>
    cases i with
    | Barrier i => rfl
    | _ => rfl
  | _ => rfl

theorem stepEvs_of_decode {s : ArmState} {ai : ArmInst} (h : decodeAt s = some ai) :
    stepEvs s = if read_err s = .None then instEvs ai s else errEvs ai := by
  unfold stepEvs; rw [h]

theorem kindsOk_barrier (i : Barrier_cls) :
    KindsOk (if fullBarrier i then .dmb else if i.op2 = 0b010#3 then .clrex else .plain)
      (if fullBarrier i then [dmbEv] else []) := by
  split
  · refine ⟨fun e he => ?_, fun _ => ⟨dmbEv, List.mem_singleton_self _, rfl⟩⟩
    simp only [List.mem_singleton] at he; subst he; rfl
  · exact kindsOk_nil _ (by split <;> simp)

/-- **The events of a step have the kinds of the instruction's class** (`ArmThread.KindsOk`). -/
theorem kindsOk_stepEvs (s : ArmState) : KindsOk (cls s) (stepEvs s) := by
  rcases hd : decodeAt s with _ | ai
  · unfold cls stepEvs; rw [hd]; exact kindsOk_plain plain_nil
  rw [cls_of_decode hd, stepEvs_of_decode hd]
  by_cases he : read_err s = .None
  · simp only [he, ite_true]
    cases ai with
    | LDST i =>
      cases i with
      | Reg_exclusive i => exact kindsOk_excl i s
      | Reg_imm_post_indexed i => exact kindsOk_plain (plain_immEvs _ s)
      | Reg_unsigned_imm i => exact kindsOk_plain (plain_immEvs _ s)
      | Reg_unscaled_imm i =>
        simp only [instEvs]; split
        · exact kindsOk_plain (plain_ldsturEvs _ s)
        · exact kindsOk_plain (plain_immEvs _ s)
      | Reg_pair_pre_indexed i => exact kindsOk_plain (plain_pairEvs _ s)
      | Reg_pair_post_indexed i => exact kindsOk_plain (plain_pairEvs _ s)
      | Reg_pair_signed_offset i => exact kindsOk_plain (plain_pairEvs _ s)
      | Reg_imm_pre_indexed i => exact kindsOk_plain (plain_immEvs _ s)
      | Reg_reg_offset i =>
        simp only [instEvs]; split
        · exact kindsOk_plain plain_nil
        · exact kindsOk_plain (plain_immEvs _ s)
      | Reg_literal i => exact kindsOk_plain (plain_literalEvs _ s)
    | BR i =>
      cases i with
      | Barrier i => exact kindsOk_barrier i
      | _ => exact kindsOk_plain plain_nil
    | _ => exact kindsOk_plain plain_nil
  · simp only [he, ite_false]
    cases ai with
    | LDST i =>
      cases i with
      | Reg_exclusive i => exact kindsOk_nil _ (exclCls_ne i)
      | _ => exact kindsOk_plain plain_nil
    | BR i =>
      cases i with
      | Barrier i => exact kindsOk_barrier i
      | _ => exact kindsOk_plain plain_nil
    | _ => exact kindsOk_plain plain_nil

end Concurrency.ArmInstFoot

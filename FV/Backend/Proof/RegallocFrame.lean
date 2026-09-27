import FV.Backend.Proof.RegallocOperands
import FV.Backend.Regalloc
import FV.Arm.Memory.MemoryProofs

/-!
# Frame and move lowering (M6 proof, deliverable: edits, spills, reloads)

`lowerRFunc` turns every `RItem.move src dst` into `RAFrame.moveInsts`: `mov` between X
registers, `str`/`ldr` at `sp + offset` for spill and callee-save slots, float register moves
through the 16-byte `fmoveTmp` slot. `MStep.move` models a move as `m[dst ↦ m src]`. Here:

* `locVal fr s`: the location store an Arm state represents (registers by `regVal`, frame
  slots by the bytes at `sp + RAFrame.offset`);
* `FrameOk fr sp0 F`: the layout facts the lowering needs — distinct frame locations have
  separate slots, all inside the frame addresses `F` (masked out of the world);
* `lower_move_reg_int`, `lower_spill_int`, `lower_reload_int`: the lowered code of an int
  register move, an int spill and an int reload (unsigned-offset encoding) changes
  `locVal` exactly as `MStep.move` changes the store, keeps the world (`SameWorld F`) and `sp`;
  `move_agree` restates that as preservation of "the store agrees with the Arm state".

Not proven here (see `docs/contracts/regalloc-proof.md`): the other two spill encodings
(`stur` for offsets < 256, the x16 sequence for large offsets), float moves via `fmoveTmp`,
callee-save slots (same shape as spills), `FrameOk` for `RAFrame.compute`, prologue/epilogue.
-/

namespace Backend.Proof
open Backend

/-- Slot size of a frame location (int spill / x save: 8 bytes; float: 16). -/
def slotBytes : Loc → Nat
  | .stack _ .int => 8
  | .save (.x _) => 8
  | _ => 16

def spOf (s : Arm.ArmState) : BitVec 64 := Arm.r (.GPR 31#5) s

/-- The value of location `l` in Arm state `s` for frame `fr`: registers by `regVal`, frame
slots by the bytes at `sp + offset` (an 8-byte slot zero-extended). -/
def locVal (fr : RAFrame) (s : Arm.ArmState) : Loc → CV
  | .reg r => regVal s r
  | l => match fr.offset l with
    | .ok off =>
      if slotBytes l = 8 then ofX (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) s)
      else Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 off) s
    | .error _ => 0

/-- The frame layout facts the lowering relies on, for stack pointer `sp0` and frame
addresses `F`: distinct frame locations have separate slots, and every slot lies in `F`. -/
structure FrameOk (fr : RAFrame) (sp0 : BitVec 64) (F : BitVec 64 → Prop) : Prop where
  sep : ∀ l l' o o', l ≠ l' → fr.offset l = .ok o → fr.offset l' = .ok o' →
    Arm.mem_separate' (sp0 + BitVec.ofNat 64 o) (slotBytes l) (sp0 + BitVec.ofNat 64 o') (slotBytes l')
  inF : ∀ l o, fr.offset l = .ok o → ∀ k < slotBytes l,
    F (sp0 + BitVec.ofNat 64 o + BitVec.ofNat 64 k)

theorem offset_reg (fr : RAFrame) (r : Reg) : ∃ e, fr.offset (.reg r) = .error e := ⟨_, rfl⟩

/-- `locVal` of a frame location depends only on memory and `sp`. -/
theorem locVal_frame_congr {fr : RAFrame} {s t : Arm.ArmState} {l : Loc} (hl : ∀ r, l ≠ .reg r)
    (hsp : spOf t = spOf s) (hmem : t.mem = s.mem) : locVal fr t l = locVal fr s l := by
  have hr : ∀ n a, Arm.read_mem_bytes n a t = Arm.read_mem_bytes n a s := by
    intro n a
    rw [Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes,
      Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes, hmem]
  cases l with
  | reg r => exact absurd rfl (hl r)
  | _ => simp only [locVal, hsp, hr]


/-- Locations the lowering maintains: allocatable registers and frame slots. -/
def ValidLoc (l : Loc) : Prop := ∀ r, l = .reg r → r.allocatable = true

theorem exec_mov64 (ctx : FnCtx) (env : Env) {n0 n1 : Nat} (hn0 : n0 < 29) (hn1 : n1 < 29)
    (s : Arm.ArmState) :
    execMInst ctx env (.mov .size64 (.x n0) (.x n1)) s =
      some (Arm.w (.GPR (rnum n0)) (Arm.r (.GPR (rnum n1)) s) (Arm.w .PC (Arm.r .PC s + 4#64) s)) := by
  have hl : MInst.lines ctx (.mov .size64 (.x n0) (.x n1)) {} =
      .ok ([.ins (.mov true (.x n0) (.x n1))], {}) := rfl
  have ha : Insn.toArmInst env (.mov true (.x n0) (.x n1)) = .ok (.DPR (.Logical_shifted_reg
      { sf := 1#1, opc := 1#2, shift := 0#2, N := 0#1, Rm := rnum n1, imm6 := 0#6, Rn := 31#5,
        Rd := rnum n0 })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, show n0 ≤ 30 by omega,
      show n1 ≤ 30 by omega, rnum, b1]; rfl
  simp only [execMInst, hl, execLines, ha]
  congr 1
  simp [Arm.exec_inst, Arm.DPR.exec_logical_shifted_reg, Arm.DPR.exec_logical_shifted_reg_op,
    Arm.DPR.decode_op, Arm.read_gpr_zr, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr,
    rnum_ne31 hn0, rnum_ne31 hn1, Arm.decode_shift, Arm.shift_reg, Arm.read_pc, Arm.write_pc]

/-- **Lowering of an int register move** (`mov xb, xa`) implements `MStep.move`: the store
becomes `m[reg b ↦ m (reg a)]`, the world and `sp` are unchanged. -/
theorem lower_move_reg_int (fr : RAFrame) (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env)
    {a b : Nat} (ha : (Reg.x a).allocatable = true) (hb : (Reg.x b).allocatable = true)
    {s w : Arm.ArmState} (hw : SameWorld F s w) :
    fr.moveInsts (.reg (.x a)) (.reg (.x b)) = .ok [.inst (.mov .size64 (.x b) (.x a))] ∧
    ∃ s', execMInst ctx env (.mov .size64 (.x b) (.x a)) s = some s' ∧ SameWorld F s' w ∧
      spOf s' = spOf s ∧
      ∀ l, ValidLoc l → locVal fr s' l = upd (locVal fr s) (.reg (.x b)) (locVal fr s (.reg (.x a))) l := by
  rcases allocatable_cases ha with ⟨a', ea, hha⟩ | ⟨_, ea, _⟩ <;> cases ea
  rcases allocatable_cases hb with ⟨b', eb, hhb⟩ | ⟨_, eb, _⟩ <;> cases eb
  refine ⟨rfl, _, exec_mov64 ctx env hhb.1 hha.1 s, ?_⟩
  obtain ⟨hW, hD, hO⟩ := gpr_write_sound hhb hw (Arm.r (.GPR (rnum a)) s) (Arm.r .PC s + 4#64)
  have hsp : spOf (Arm.w (.GPR (rnum b)) (Arm.r (.GPR (rnum a)) s)
      (Arm.w .PC (Arm.r .PC s + 4#64) s)) = spOf s := by
    simp only [spOf]
    rw [Arm.r_of_w_different (by simpa using (rnum_ne31 hhb.1).symm),
      Arm.r_of_w_different (by simp)]
  refine ⟨hW, hsp, fun l hl => ?_⟩
  by_cases e : l = .reg (.x b)
  · subst e; simp only [upd, if_true, locVal, hD]; rfl
  · simp only [upd, e, if_false]
    cases l with
    | reg r => exact hO r (hl r rfl) (fun h => e (by rw [h]))
    | stack k c =>
      have hm : (Arm.w (.GPR (rnum b)) (Arm.r (.GPR (rnum a)) s)
          (Arm.w .PC (Arm.r .PC s + 4#64) s)).mem = s.mem := by
        rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]
      exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm
    | save r =>
      have hm : (Arm.w (.GPR (rnum b)) (Arm.r (.GPR (rnum a)) s)
          (Arm.w .PC (Arm.r .PC s + 4#64) s)).mem = s.mem := by
        rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]
      exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm


theorem write_bytes_outside {b : BitVec 64} :
    ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (m : Arm.Memory),
      (∀ k < n, b ≠ a + BitVec.ofNat 64 k) → Arm.Memory.write_bytes n a v m b = m b
  | 0, _, _, _, _ => rfl
  | n + 1, a, v, m, h => by
    unfold Arm.Memory.write_bytes
    simp only
    rw [write_bytes_outside n (a + 1#64) _ _ (fun k hk e => h (k + 1) (by omega) (by
      rw [e]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    simp [Arm.Memory.write, Arm.write_store, h0]

theorem SameWorld.write_mem_bytes_inF {F} {s w : Arm.ArmState} (hw : SameWorld F s w) (n : Nat)
    (a : BitVec 64) (v : BitVec (n * 8)) (hF : ∀ k < n, F (a + BitVec.ofNat 64 k)) :
    SameWorld F (Arm.write_mem_bytes n a v s) w := by
  refine ⟨fun f hf => ?_, fun b hb => ?_, ?_⟩
  · rw [Arm.r_of_write_mem_bytes]; exact hw.1 f hf
  · rw [Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
    simp only
    rw [write_bytes_outside n a v _ (fun k hk e => hb (by rw [e]; exact hF k hk))]
    exact hw.2.1 b hb
  · rw [Arm.write_mem_bytes_program]; exact hw.2.2

theorem slotBytes_cases (l : Loc) : slotBytes l = 8 ∨ slotBytes l = 16 := by
  unfold slotBytes; split <;> simp

theorem spOf_write (s : Arm.ArmState) (p : BitVec 64) (n : Nat) (y : BitVec 64) (v : BitVec (n * 8)) :
    spOf (Arm.w .PC p (Arm.write_mem_bytes n y v s)) = spOf s := by
  simp only [spOf]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]

theorem read_after_write_sep {s : Arm.ArmState} {p x y : BitVec 64} {xn n : Nat} {v : BitVec (n * 8)}
    (hsep : Arm.mem_separate' x xn y n) :
    Arm.read_mem_bytes xn x (Arm.w .PC p (Arm.write_mem_bytes n y v s)) = Arm.read_mem_bytes xn x s := by
  rw [Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes, Arm.ArmState.mem_w_eq_mem,
    Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
  simp only
  rw [Arm.Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' hsep,
    ← Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes]

/-- A frame location separate from a store is unchanged by it. -/
theorem locVal_frame_write {fr : RAFrame} {s : Arm.ArmState} {l : Loc} (hl : ∀ r, l ≠ .reg r)
    {p y : BitVec 64} {n : Nat} {v : BitVec (n * 8)}
    (hsep : ∀ o, fr.offset l = .ok o →
      Arm.mem_separate' (spOf s + BitVec.ofNat 64 o) (slotBytes l) y n) :
    locVal fr (Arm.w .PC p (Arm.write_mem_bytes n y v s)) l = locVal fr s l := by
  cases l with
  | reg r => exact absurd rfl (hl r)
  | stack k c =>
    simp only [locVal, spOf_write]
    split
    · rename_i o ho
      rcases slotBytes_cases (.stack k c) with h | h <;> simp only [h, if_true] <;>
        (have := hsep o ho; rw [h] at this; rw [read_after_write_sep this]) <;> simp
    · rfl
  | save r =>
    simp only [locVal, spOf_write]
    split
    · rename_i o ho
      rcases slotBytes_cases (.save r) with h | h <;> simp only [h, if_true] <;>
        (have := hsep o ho; rw [h] at this; rw [read_after_write_sep this]) <;> simp
    · rfl

/-- **Lowering of an int spill** (`str xa, [sp, #off]`, the unsigned-offset encoding:
`256 ≤ off`, `off` a multiple of 8 below 32768) implements `MStep.move` for
`reg (x a) → stack k int`, given the frame layout `FrameOk` and an aligned `sp`. -/
theorem lower_spill_int (fr : RAFrame) {sp0 : BitVec 64} {F : BitVec 64 → Prop}
    (hfr : FrameOk fr sp0 F) (ctx : FnCtx) (env : Env) {a k off : Nat}
    (ha : (Reg.x a).allocatable = true) (hoff : fr.offset (.stack k .int) = .ok off)
    (h256 : 256 ≤ off) (h8 : off % 8 = 0) (h12 : off / 8 < 4096)
    {s w : Arm.ArmState} (hw : SameWorld F s w) (hsp : spOf s = sp0)
    (halign : Arm.CheckSPAlignment s) :
    fr.moveInsts (.reg (.x a)) (.stack k .int) = .ok [.inst (slotStore .int (.x a) off)] ∧
    ∃ s', execMInst ctx env (slotStore .int (.x a) off) s = some s' ∧ SameWorld F s' w ∧
      spOf s' = sp0 ∧
      ∀ l, ValidLoc l →
        locVal fr s' l = upd (locVal fr s) (.stack k .int) (locVal fr s (.reg (.x a))) l := by
  rcases allocatable_cases ha with ⟨a', ea, hha⟩ | ⟨_, ea, _⟩ <;> cases ea
  refine ⟨by simp [RAFrame.moveInsts, hoff, Reg.realClass?]; rfl, ?_⟩
  have hl : MInst.lines ctx (slotStore .int (.x a) off) {} =
      .ok ([.ins (.store .store64 (.x a) (.unsignedOffset .sp off)) trustedFlags.trapCode], {}) := by
    simp [MInst.lines, slotStore, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
      show (off : Int) ≤ 4095 * 8 by omega, h8, StoreOp.bytes, show (off : Int) ≤ 32760 by omega]
    rfl
  have ha' : Insn.toArmInst env (.store .store64 (.x a) (.unsignedOffset .sp off)) =
      .ok (.LDST (.Reg_unsigned_imm
        { size := 3#2, V := 0#1, opc := 0#2, imm12 := BitVec.ofNat 12 (off / 8),
          Rn := 31#5, Rt := rnum a })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
      Reg.encZR, Reg.encSP, show a ≤ 30 by omega, rnum, uField, h8, h12, StoreOp.bytes]
    rfl
  have halign' : Arm.Aligned (Arm.r (.GPR 31#5) s) 4 := by
    have := halign
    simp only [Arm.CheckSPAlignment, Arm.read_gpr, BitVec.setWidth_eq] at this
    exact this
  have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm
        { size := 3#2, V := 0#1, opc := 0#2, imm12 := BitVec.ofNat 12 (off / 8),
          Rn := 31#5, Rt := rnum a })) s =
      Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.write_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) (Arm.r (.GPR (rnum a)) s) s) := by
    rw [← ldst_offset off h8 h12]
    simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
      Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
      Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
      rnum_ne31 hha.1, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, Arm.CheckSPAlignment, halign', spOf]
    rfl
  refine ⟨Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.write_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) (Arm.r (.GPR (rnum a)) s) s),
    by simp only [execMInst, hl, execLines, ha', he], ?_, ?_, ?_⟩
  · exact SameWorld.w_left (by simp [Masked]) (SameWorld.write_mem_bytes_inF hw 8 _ _
      (fun j hj => by rw [hsp]; exact hfr.inF _ off hoff j hj))
  · rw [spOf_write, hsp]
  · intro l hl
    by_cases e : l = .stack k .int
    · subst e
      simp only [upd, if_true, locVal, hoff, slotBytes, spOf_write]
      rw [Arm.read_mem_bytes_of_w, Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)]
      rfl
    · simp only [upd, e, if_false]
      cases l with
      | reg r =>
        simp only [locVal]
        rw [regVal_w (by cases r <;> simp [Reg.field]), regVal_write_mem_bytes]
      | stack k' c =>
        exact locVal_frame_write (fun r h => Loc.noConfusion h) (fun o ho => by
          rw [hsp]; exact hfr.sep _ _ o off e ho hoff)
      | save r =>
        exact locVal_frame_write (fun r h => Loc.noConfusion h) (fun o ho => by
          rw [hsp]; exact hfr.sep _ _ o off e ho hoff)


/-- **Lowering of an int reload** (`ldr xb, [sp, #off]`, unsigned-offset encoding) implements
`MStep.move` for `stack k int → reg (x b)`. -/
theorem lower_reload_int (fr : RAFrame) {F : BitVec 64 → Prop} (ctx : FnCtx) (env : Env)
    {b k off : Nat} (hb : (Reg.x b).allocatable = true) (hoff : fr.offset (.stack k .int) = .ok off)
    (h256 : 256 ≤ off) (h8 : off % 8 = 0) (h12 : off / 8 < 4096)
    {s w : Arm.ArmState} (hw : SameWorld F s w) (halign : Arm.CheckSPAlignment s) :
    fr.moveInsts (.stack k .int) (.reg (.x b)) = .ok [.inst (slotLoad .int (.x b) off)] ∧
    ∃ s', execMInst ctx env (slotLoad .int (.x b) off) s = some s' ∧ SameWorld F s' w ∧
      spOf s' = spOf s ∧
      ∀ l, ValidLoc l →
        locVal fr s' l = upd (locVal fr s) (.reg (.x b)) (locVal fr s (.stack k .int)) l := by
  rcases allocatable_cases hb with ⟨b', eb, hhb⟩ | ⟨_, eb, _⟩ <;> cases eb
  refine ⟨by simp [RAFrame.moveInsts, hoff, Reg.realClass?]; rfl, ?_⟩
  have hl : MInst.lines ctx (slotLoad .int (.x b) off) {} =
      .ok ([.ins (.load .uload64 (.x b) (.unsignedOffset .sp off)) trustedFlags.trapCode], {}) := by
    simp [MInst.lines, slotLoad, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
      h8, LoadOp.bytes, show (off : Int) ≤ 32760 by omega]
    rfl
  have ha' : Insn.toArmInst env (.load .uload64 (.x b) (.unsignedOffset .sp off)) =
      .ok (.LDST (.Reg_unsigned_imm
        { size := 3#2, V := 0#1, opc := 1#2, imm12 := BitVec.ofNat 12 (off / 8),
          Rn := 31#5, Rt := rnum b })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
      Reg.encZR, Reg.encSP, show b ≤ 30 by omega, rnum, uField, h8, h12, LoadOp.bytes]
    rfl
  have halign' : Arm.Aligned (Arm.r (.GPR 31#5) s) 4 := by
    have := halign
    simp only [Arm.CheckSPAlignment, Arm.read_gpr, BitVec.setWidth_eq] at this
    exact this
  have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm
        { size := 3#2, V := 0#1, opc := 1#2, imm12 := BitVec.ofNat 12 (off / 8),
          Rn := 31#5, Rt := rnum b })) s =
      Arm.w (.GPR (rnum b)) (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
    rw [← ldst_offset off h8 h12, Arm.w_of_w_commute (by simp)]
    simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
      Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
      Arm.LDST.reg_imm_constrain_unpredictable, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr,
      rnum_ne31 hhb.1, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb, halign, spOf]
    rfl
  obtain ⟨hW, hD, hO⟩ := gpr_write_sound hhb hw
    (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) s) (Arm.r .PC s + 4#64)
  have hsp : spOf (Arm.w (.GPR (rnum b)) (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) s)
      (Arm.w .PC (Arm.r .PC s + 4#64) s)) = spOf s := by
    simp only [spOf]
    rw [Arm.r_of_w_different (by simpa using (rnum_ne31 hhb.1).symm),
      Arm.r_of_w_different (by simp)]
  refine ⟨_, by simp only [execMInst, hl, execLines, ha', he], hW, hsp, fun l hl => ?_⟩
  by_cases e : l = .reg (.x b)
  · subst e; simp only [upd, if_true, locVal, hD, hoff, slotBytes]
  · simp only [upd, e, if_false]
    have hm : (Arm.w (.GPR (rnum b)) (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s)).mem = s.mem := by
      rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]
    cases l with
    | reg r => exact hO r (hl r rfl) (fun h => e (by rw [h]))
    | stack k c => exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm
    | save r => exact locVal_frame_congr (fun r h => Loc.noConfusion h) hsp hm


/-- The lowering lemmas above give exactly `MStep.move`'s store: if the location store `m`
agrees with the Arm state on the maintained locations before, `m[dst ↦ m src]` agrees after. -/
theorem move_agree {fr : RAFrame} {s s' : Arm.ArmState} {m : Loc → CV} {src dst : Loc}
    (hm : ∀ l, ValidLoc l → m l = locVal fr s l) (hsrc : ValidLoc src)
    (h : ∀ l, ValidLoc l → locVal fr s' l = upd (locVal fr s) dst (locVal fr s src) l) :
    ∀ l, ValidLoc l → upd m dst (m src) l = locVal fr s' l := by
  intro l hl
  rw [h l hl]
  simp only [upd]
  split
  · exact hm src hsrc
  · exact hm l hl

end Backend.Proof

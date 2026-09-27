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
* `lower_move_reg_int`: the lowered code of an int register move changes `locVal` exactly
  as `MStep.move` changes the store, keeps the world (`SameWorld F`) and `sp` (every other
  move kind: `RegallocMoves.lower_move`);
  `move_agree` restates that as preservation of "the store agrees with the Arm state".

Spills, reloads, save/restore and float moves: `RegallocSlots`/`RegallocMoves`; the layout
of `RAFrame.compute`: `RegallocLayout.frameOk_compute`.
-/

namespace Backend.Proof
open Backend

/-- Slot size of a frame location (int spill / x save: 8 bytes; float: 16). -/
def slotBytes : Loc → Nat
  | .stack _ .int => 8
  | .save (.x _) => 8
  | _ => 16

/-- The value of location `l` in Arm state `s` for frame `fr`: registers by `regVal`, frame
slots by the bytes at `sp + offset` (an 8-byte slot zero-extended). -/
def locVal (fr : RAFrame) (s : Arm.ArmState) : Loc → CV
  | .reg r => regVal s r
  | l => match fr.offset l with
    | .ok off =>
      if slotBytes l = 8 then ofX (Arm.read_mem_bytes 8 (spOf s + BitVec.ofNat 64 off) s)
      else Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 off) s
    | .error _ => 0

/-- The frame locations the allocated code can use: int spill slots below `spillSlots`, float
spill slots below `spillSlots` when the code uses float slots at all (otherwise the float area
is empty), every save slot (`offset` fails for registers without one). -/
def Live (rf : RFunc) : Loc → Prop
  | .stack k .int => k < rf.spillSlots
  | .stack k .float => k < rf.spillSlots ∧ rf.floatStack = true
  | _ => True

/-- The frame layout facts the lowering relies on, for the live locations `D`, stack pointer
`sp0` and frame addresses `F`: distinct live frame locations have separate slots, every slot
lies in `F`; when `T` (the code has float register moves) the 16-byte `fmoveTmp` slot is in
`F` and separate from every live slot. -/
structure FrameOk (fr : RAFrame) (D : Loc → Prop) (T : Prop) (sp0 : BitVec 64)
    (F : BitVec 64 → Prop) : Prop where
  sep : ∀ l l' o o', D l → D l' → l ≠ l' → fr.offset l = .ok o → fr.offset l' = .ok o' →
    Arm.mem_separate' (sp0 + BitVec.ofNat 64 o) (slotBytes l) (sp0 + BitVec.ofNat 64 o') (slotBytes l')
  inF : ∀ l o, D l → fr.offset l = .ok o → ∀ k < slotBytes l,
    F (sp0 + BitVec.ofNat 64 o + BitVec.ofNat 64 k)
  tmpSep : T → ∀ l o, D l → fr.offset l = .ok o →
    Arm.mem_separate' (sp0 + BitVec.ofNat 64 o) (slotBytes l) (sp0 + BitVec.ofNat 64 fr.fmoveTmp) 16
  tmpF : T → ∀ k < 16, F (sp0 + BitVec.ofNat 64 fr.fmoveTmp + BitVec.ofNat 64 k)

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
  have he : Arm.exec_inst (.DPR (.Logical_shifted_reg
      { sf := 1#1, opc := 1#2, shift := 0#2, N := 0#1, Rm := rnum n1, imm6 := 0#6, Rn := 31#5,
        Rd := rnum n0 })) s =
      Arm.w (.GPR (rnum n0)) (Arm.r (.GPR (rnum n1)) s) (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
    simp [Arm.exec_inst, Arm.DPR.exec_logical_shifted_reg, Arm.DPR.exec_logical_shifted_reg_op,
      Arm.DPR.decode_op, Arm.read_gpr_zr, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr,
      rnum_ne31 hn0, rnum_ne31 hn1, Arm.decode_shift, Arm.shift_reg, Arm.read_pc, Arm.write_pc]
  simp only [execMInst, hl]
  rw [execLines_one ha (by rw [he, Arm.r_of_w_different (by simp), Arm.r_of_w_same]), he]

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

/-- The lowering lemmas give exactly `MStep.move`'s store: if the location store `m` agrees
with the Arm state on the maintained locations (valid and in `L`) before, `m[dst ↦ m src]`
agrees after. -/
theorem move_agree {fr : RAFrame} {L : Loc → Prop} {s s' : Arm.ArmState} {m : Loc → CV}
    {src dst : Loc} (hm : ∀ l, ValidLoc l → L l → m l = locVal fr s l) (hsrc : ValidLoc src)
    (hsrcL : L src)
    (h : ∀ l, ValidLoc l → L l → locVal fr s' l = upd (locVal fr s) dst (locVal fr s src) l) :
    ∀ l, ValidLoc l → L l → upd m dst (m src) l = locVal fr s' l := by
  intro l hl hL
  rw [h l hl hL]
  simp only [upd]
  split
  · exact hm src hsrc hsrcL
  · exact hm l hl hL

end Backend.Proof

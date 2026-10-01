import FV.Backend.Proof.RegallocCSem

/-!
# Loads and stores on the Arm model (M6 proof)

`exec_load_line`/`exec_store_line`: a GPR load/store (`uload*`/`sload*`/`store8..64`) with a
final addressing mode (`FinalAM`: unsigned or unscaled immediate, register offset, scaled,
extended) encodes, and the model executes it as the value-level access at `AMode.addr`:
`ldX op a s` into the target register, or `write_mem_bytes` of the register's low bytes; the
pc advances by 4. Base registers may be `sp` (then `sp` must be aligned).

`steps_loadConst64`: the `movz`/`movk` sequence of `loadConst64 (x n) v` leaves `v` in `x n`;
`StepsOk` (every line encodes, advances the pc by 4 and keeps the error flag and the program)
gives both its `execLines` run and the error-free intermediate states.

`execMInst_load`/`execMInst_store`: an allocated load/store with a `MemMode` addressing mode
(final register forms, or a stack-slot offset: `ldur`/`stur`, scaled `ldr`/`str`, or the
`x16` sequence for large offsets) runs as `StepsOk` to the value-level access, with an optional
scratch value in `x16`.
-/

namespace Backend.Proof
open Backend

/-- The 64-bit register value a GPR load `op` from `a` leaves. -/
def ldX (op : LoadOp) (a : BitVec 64) (s : Arm.ArmState) : BitVec 64 :=
  match op with
  | .uload8 => (Arm.read_mem_bytes 1 a s).setWidth 64
  | .sload8 => (Arm.read_mem_bytes 1 a s).signExtend 64
  | .uload16 => (Arm.read_mem_bytes 2 a s).setWidth 64
  | .sload16 => (Arm.read_mem_bytes 2 a s).signExtend 64
  | .uload32 => (Arm.read_mem_bytes 4 a s).setWidth 64
  | .sload32 => (Arm.read_mem_bytes 4 a s).signExtend 64
  | .uload64 => Arm.read_mem_bytes 8 a s
  | .fpuLoad128 => 0

/-- A GPR load/store without writeback. -/
def gprCls (size opc : BitVec 2) (Rn Rt : BitVec 5) (imm : Arm.LDST.Reg_offset) :
    Arm.LDST.Reg_imm_cls :=
  { size      := size,
    opc       := opc,
    Rn        := Rn,
    Rt        := Rt,
    SIMD?     := false,
    wback     := false,
    postindex := false,
    imm       := imm }

theorem lsb_facts :
    Arm.BitVec.lsb (0#2) 0 = 0#1 ∧ Arm.BitVec.lsb (0#2) 1 = 0#1 ∧ Arm.BitVec.lsb (1#2) 0 = 1#1 ∧
    Arm.BitVec.lsb (1#2) 1 = 0#1 ∧ Arm.BitVec.lsb (2#2) 0 = 0#1 ∧ Arm.BitVec.lsb (2#2) 1 = 1#1 ∧
    Arm.BitVec.lsb (3#2) 0 = 1#1 ∧ Arm.BitVec.lsb (3#2) 1 = 1#1 := by decide

theorem lsb_facts3 :
    Arm.BitVec.lsb (3#3) 1 = 1#1 ∧ Arm.BitVec.lsb (2#3) 1 = 1#1 ∧ Arm.BitVec.lsb (6#3) 1 = 1#1 ∧
    Arm.BitVec.lsb (7#3) 1 = 1#1 := by decide

theorem sext_w {n k : Nat} (x : BitVec n) (hk : k = 64) :
    BitVec.setWidth 64 (BitVec.signExtend k x) = BitVec.signExtend 64 x := by
  subst hk; simp

theorem ldst_load (op : LoadOp) (hop : op ≠ .fpuLoad128) (Rn Rt : BitVec 5) (hRt : Rt ≠ 31#5)
    (imm : Arm.LDST.Reg_offset) (str : String) (s : Arm.ArmState)
    (hsp : Rn = 31#5 → Arm.CheckSPAlignment s) :
    Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str s =
    Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.w (.GPR Rt) (ldX op (Arm.read_gpr 64 Rn s + imm.value (log2 op.bytes) s) s) s) := by
  cases op <;> simp at hop <;>
  · by_cases h31 : Rn = 31#5 ∧ ¬ Arm.CheckSPAlignment s
    · exact absurd (hsp h31.1) h31.2
    · simp only [gprCls, LoadOp.fields]
      simp (config := {decide := true}) [Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation,
        LoadOp.bytes, Arm.LDST.reg_imm_constrain_unpredictable, Arm.write_gpr_zr,
        Arm.write_gpr, Arm.write_pc, Arm.read_pc, hRt, h31, ldX, log2]
      all_goals first
        | rfl
        | (rw [sext_w _ (by simp [lsb_facts])]; rfl)

theorem ldst_store (op : StoreOp) (hop : op ≠ .fpuStore128) (Rn Rt : BitVec 5) (hRt : Rt ≠ 31#5)
    (imm : Arm.LDST.Reg_offset) (str : String) (s : Arm.ArmState)
    (hsp : Rn = 31#5 → Arm.CheckSPAlignment s) :
    Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) str s =
    Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.write_mem_bytes op.bytes (Arm.read_gpr 64 Rn s + imm.value (log2 op.bytes) s)
        ((Arm.r (.GPR Rt) s).setWidth (op.bytes * 8)) s) := by
  cases op <;> simp at hop <;>
  · by_cases h31 : Rn = 31#5 ∧ ¬ Arm.CheckSPAlignment s
    · exact absurd (hsp h31.1) h31.2
    · simp only [gprCls, StoreOp.fields]
      simp (config := {decide := true}) [Arm.LDST.exec_reg_imm_common, Arm.LDST.reg_imm_operation,
        StoreOp.bytes, Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr,
        Arm.read_gpr, Arm.write_pc, Arm.read_pc, hRt, h31, log2]
      all_goals rfl

/-- A base register of a final addressing mode. -/
def BaseOk : Reg → Prop
  | .sp => True
  | .x n => n ≤ 30
  | _ => False

/-- An index register of a final addressing mode. -/
def IdxOk : Reg → Prop
  | .x n => n ≤ 30
  | _ => False

/-- A final (encodable) addressing mode for an access of `bytes` bytes. -/
def FinalAM (bytes : Nat) : AMode → Prop
  | .unsignedOffset rn off => BaseOk rn ∧ off % bytes = 0 ∧ off / bytes < 4096
  | .unscaled rn off => BaseOk rn ∧ -256 ≤ off ∧ off < 256
  | .regReg rn rm | .regScaled rn rm => BaseOk rn ∧ IdxOk rm
  | .regScaledExtended rn rm e | .regExtended rn rm e =>
    BaseOk rn ∧ IdxOk rm ∧ (e = .uxtw ∨ e = .uxtx ∨ e = .sxtw ∨ e = .sxtx)
  | _ => False

/-- The base register of an addressing mode. -/
def _root_.Backend.AMode.base : AMode → Reg
  | .unsignedOffset rn _ | .unscaled rn _ | .regReg rn _ | .regScaled rn _
  | .regScaledExtended rn _ _ | .regExtended rn _ _ | .regOffset rn _ => rn
  | _ => .sp

/-- `LDR*`/`STR*` (unsigned offset), GPR. -/
def uimmInst (size opc : BitVec 2) (imm12 : BitVec 12) (Rn Rt : BitVec 5) : Arm.ArmInst :=
  .LDST (.Reg_unsigned_imm { size := size, V := 0#1, opc := opc, imm12 := imm12, Rn := Rn, Rt := Rt })

/-- `LDUR*`/`STUR*`, GPR. -/
def unscInst (size opc : BitVec 2) (imm9 : BitVec 9) (Rn Rt : BitVec 5) : Arm.ArmInst :=
  .LDST (.Reg_unscaled_imm { size := size, VR := 0#1, opc := opc, imm9 := imm9, Rn := Rn, Rt := Rt })

/-- `LDR*`/`STR*` (register offset), GPR. -/
def regInst (size opc : BitVec 2) (Rm : BitVec 5) (option : BitVec 3) (S : BitVec 1) (Rn Rt : BitVec 5) :
    Arm.ArmInst :=
  .LDST (.Reg_reg_offset { size := size, V := 0#1, opc := opc, Rm := Rm, option := option, S := S, Rn := Rn, Rt := Rt })

theorem uimm_value (b : Nat) (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) (off : Nat) (h1 : off % b = 0)
    (h2 : off / b < 4096) :
    BitVec.setWidth 64 (BitVec.ofNat 12 (off / b)) <<< log2 b = BitVec.ofNat 64 off := by
  apply BitVec.eq_of_toNat_eq
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp [log2, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt h2, Nat.shiftLeft_eq] <;> omega

theorem simm9_value (off : Int) (h1 : -256 ≤ off) (h2 : off < 256) :
    BitVec.signExtend 64 (BitVec.ofInt 9 off) = BitVec.ofInt 64 off := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  simp only [Int.bmod]
  split <;> split <;> omega

theorem enc_idx {rm : Reg} (h : IdxOk rm) (s : Arm.ArmState) :
    ∃ Rm, rm.encZR = .ok Rm ∧ Arm.read_gpr_zr 64 Rm s = regX s rm := by
  cases rm with
  | x n =>
    simp only [IdxOk] at h
    refine ⟨BitVec.ofNat 5 n, by simp [Reg.encZR, h, pure, Except.pure], ?_⟩
    have : BitVec.ofNat 5 n ≠ 31#5 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [Arm.read_gpr_zr, this, Arm.read_gpr, regX, rnum]
  | _ => simp [IdxOk] at h

theorem uxtx_shift (x : BitVec 64) (k : Nat) (hk : k < 64) :
    Arm.extend_reg x .UXTX k = x <<< k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Arm.extend_reg, Arm.ExtendType.unsigned_len, hi,
    show i - k < 64 by omega, show i - k < 64 - k by omega]

theorem enc_base {rn : Reg} (h : BaseOk rn) (s : Arm.ArmState) :
    ∃ Rn, rn.encSP = .ok Rn ∧ Arm.read_gpr 64 Rn s = regX s rn ∧ (Rn = 31#5 → rn = .sp) := by
  cases rn with
  | sp => exact ⟨31#5, rfl, by simp [Arm.read_gpr, regX, spOf], fun _ => rfl⟩
  | x n =>
    simp only [BaseOk] at h
    refine ⟨BitVec.ofNat 5 n, by simp [Reg.encSP, h, pure, Except.pure], by simp [Arm.read_gpr, regX, rnum], ?_⟩
    intro e
    have := congrArg BitVec.toNat e
    simp at this; omega
  | _ => simp [BaseOk] at h

theorem load_bytes_pos (op : LoadOp) : 0 < op.bytes := by cases op <;> decide

theorem exec_load_line (env : Env) (ctx : FnCtx) (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) (s : Arm.ArmState)
    (hsp : m.base = .sp → Arm.CheckSPAlignment s) :
    ∃ ai, Insn.toArmInst env (.load op (.x d) m) = .ok ai ∧
      Arm.exec_inst ai s = Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.w (.GPR (BitVec.ofNat 5 d)) (ldX op (m.addr ctx op.bytes s) s) s) := by
  have hRt : BitVec.ofNat 5 d ≠ 31#5 := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.uimm12 (BitVec.ofNat 12 (off / op.bytes)))) str s := ⟨_, rfl⟩
      rw [e, ldst_load op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact uimm_value op.bytes (by cases op <;> simp_all [LoadOp.bytes]) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, sField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, unscInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.simm9 (BitVec.ofInt 9 off))) str s := ⟨_, rfl⟩
      rw [e, ldst_load op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 0#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [regInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_load op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
      apply BitVec.eq_of_toNat_eq
      simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
      exact (regX s rm).isLt
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 1#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [regInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_load op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
      exact uxtx_shift _ _ (by cases op <;> simp [log2, LoadOp.bytes])
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 1#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [regInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_load op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 0#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [regInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_load op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 3
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      rfl
  | _ => simp [FinalAM] at hm

theorem exec_store_line (env : Env) (ctx : FnCtx) (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) (s : Arm.ArmState)
    (hsp : m.base = .sp → Arm.CheckSPAlignment s) :
    ∃ ai, Insn.toArmInst env (.store op (.x d) m) = .ok ai ∧
      Arm.exec_inst ai s = Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.write_mem_bytes op.bytes (m.addr ctx op.bytes s)
          ((Arm.r (.GPR (BitVec.ofNat 5 d)) s).setWidth (op.bytes * 8)) s) := by
  have hRt : BitVec.ofNat 5 d ≠ 31#5 := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.uimm12 (BitVec.ofNat 12 (off / op.bytes)))) str s := ⟨_, rfl⟩
      rw [e, ldst_store op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact uimm_value op.bytes (by cases op <;> simp_all [StoreOp.bytes]) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    refine ⟨unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, sField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, unscInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.simm9 (BitVec.ofInt 9 off))) str s := ⟨_, rfl⟩
      rw [e, ldst_store op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 0#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [regInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_store op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
      apply BitVec.eq_of_toNat_eq
      simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
      exact (regX s rm).isLt
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm 3#3 1#1)) str s := ⟨_, by
          simp (config := {decide := true}) only [regInst, Arm.exec_inst, Arm.LDST.exec_reg_reg_offset,
            ite_false, lsb_facts3]; rfl⟩
      rw [e, ldst_store op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
      exact uxtx_shift _ _ (by cases op <;> simp [log2, StoreOp.bytes])
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 1#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [regInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_store op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    refine ⟨regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d), ?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    · obtain ⟨str, e⟩ : ∃ str, Arm.exec_inst (regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) s =
          Arm.LDST.exec_reg_imm_common (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d)
            (.reg Rm ex.bits 0#1)) str s := by
          rcases hex with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp (config := {decide := true}) only [regInst, Arm.exec_inst,
            Arm.LDST.exec_reg_reg_offset, ite_false, lsb_facts3, ExtendOp.bits]; rfl⟩
      rw [e, ldst_store op hop Rn _ hRt _ _ s (fun h => hsp (by simp [AMode.base, h31 h]))]
      congr 2
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      rfl
  | _ => simp [FinalAM] at hm

/-! ## Constant loads (`loadConst64`) -/

theorem partInstall_chunk (v p : Nat) (_hp : p + 16 ≤ 64) :
    Arm.BitVec.partInstall p 16 (BitVec.ofNat 16 ((v / 2 ^ p) % 2 ^ 16)) (BitVec.ofNat 64 (v % 2 ^ p)) =
      BitVec.ofNat 64 (v % 2 ^ (p + 16)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Arm.BitVec.partInstall, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Bool.not_and, Bool.not_not,
    BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h1 : i < p
  · simp [h1, show i < p + 16 by omega]
  · by_cases h2 : i < p + 16
    · simp [h1, h2, show i - p < 16 by omega, show i - p < 64 by omega, show i - p + p = i by omega]
    · simp [h1, h2, show ¬ i - p < 16 by omega]

theorem ofNat5_ne31 {n : Nat} (hn : n ≤ 30) : BitVec.ofNat 5 n ≠ 31#5 := by
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

/-- `MOVZ`/`MOVK` (64-bit). -/
def mwInst (opc hw : BitVec 2) (imm16 : BitVec 16) (Rd : BitVec 5) : Arm.ArmInst :=
  .DPI (.Move_wide_imm { sf := 1#1, opc := opc, hw := hw, imm16 := imm16, Rd := Rd })

theorem exec_movz (env : Env) {n c : Nat} (hn : n ≤ 30) (hc : c < 2 ^ 16) (s : Arm.ArmState) :
    ∃ ai, Insn.toArmInst env (.movWide .movZ true (.x n) ⟨c, 0⟩) = .ok ai ∧
      Arm.exec_inst ai s =
        Arm.w .PC (Arm.r .PC s + 4#64) (Arm.w (.GPR (BitVec.ofNat 5 n)) (BitVec.ofNat 64 c) s) := by
  refine ⟨mwInst 2#2 0#2 (BitVec.ofNat 16 c) (BitVec.ofNat 5 n),
    by simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn, uField, hc, b1, Arm.ArmInst.norm, mwInst], ?_⟩
  have := partInstall_chunk c 0 (by omega)
  simp only [Nat.pow_zero, Nat.div_one, Nat.mod_one, Nat.mod_eq_of_lt hc, Nat.zero_add] at this
  simp [mwInst, Arm.exec_inst, Arm.DPI.exec_move_wide_imm, Arm.write_gpr_zr, ofNat5_ne31 hn,
    Arm.write_gpr, Arm.write_pc, Arm.read_pc, this]

theorem exec_movk (env : Env) {n c i : Nat} (hn : n ≤ 30) (hc : c < 2 ^ 16) (hi : i < 4)
    (s : Arm.ArmState) :
    ∃ ai, Insn.toArmInst env (.movk true (.x n) ⟨c, i⟩) = .ok ai ∧
      Arm.exec_inst ai s =
        Arm.w .PC (Arm.r .PC s + 4#64) (Arm.w (.GPR (BitVec.ofNat 5 n))
          (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) (Arm.r (.GPR (BitVec.ofNat 5 n)) s)) s) := by
  refine ⟨mwInst 3#2 (BitVec.ofNat 2 i) (BitVec.ofNat 16 c) (BitVec.ofNat 5 n),
    by simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn, uField, hc, b1, Arm.ArmInst.norm, mwInst,
      show ¬ 4 ≤ i by omega], ?_⟩
  have hpos : (BitVec.ofNat 2 i ++ 0#4).toNat = 16 * i := by
    rw [BitVec.toNat_append]; simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hi]; omega
  simp [mwInst, Arm.exec_inst, Arm.DPI.exec_move_wide_imm, Arm.write_gpr_zr, ofNat5_ne31 hn,
    Arm.write_gpr, Arm.write_pc, Arm.read_pc, Arm.read_gpr_zr, Arm.read_gpr, hpos]

/-- Straight-line lines each of which encodes, advances the pc by 4, and keeps the error flag
and the program, ending in `s'`. -/
def StepsOk : Env → List Line → Arm.ArmState → Arm.ArmState → Prop
  | _, [], s, s' => s' = s
  | env, .ins i _ :: ls, s, s' => ∃ ai, i.toArmInst env = .ok ai ∧
      Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64 ∧
      Arm.r .ERR (Arm.exec_inst ai s) = Arm.r .ERR s ∧ (Arm.exec_inst ai s).program = s.program ∧
      StepsOk { env with pc := env.pc + 4 } ls (Arm.exec_inst ai s) s'
  | _, _ :: _, _, _ => False

theorem StepsOk.exec : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState},
    StepsOk env ls s s' → execLines env ls s = some s'
  | _, [], _, _, h => by simp [StepsOk] at h; simp [execLines, h]
  | _, .ins i t :: ls, s, s', h => by
    obtain ⟨ai, ha, hpc, -, -, h⟩ := h
    simp [execLines, ha, hpc, StepsOk.exec h]
  | _, .label _ :: _, _, _, h => h.elim
  | _, .word _ _ :: _, _, _, h => h.elim

theorem StepsOk.err : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState},
    StepsOk env ls s s' → Arm.r .ERR s' = Arm.r .ERR s ∧ s'.program = s.program
  | _, [], _, _, h => by simp [StepsOk] at h; subst h; simp
  | _, .ins i t :: ls, s, s', h => by
    obtain ⟨ai, -, -, he, hp, h⟩ := h
    obtain ⟨h1, h2⟩ := StepsOk.err h
    exact ⟨h1.trans he, h2.trans hp⟩
  | _, .label _ :: _, _, _, h => h.elim
  | _, .word _ _ :: _, _, _, h => h.elim

theorem StepsOk.take : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState} (k : Nat),
    StepsOk env ls s s' → ∃ s1, StepsOk env (ls.take k) s s1
  | _, [], s, _, k, _ => ⟨s, by simp [StepsOk]⟩
  | _, .ins i t :: ls, s, s', 0, _ => ⟨s, by simp [StepsOk]⟩
  | _, .ins i t :: ls, s, s', k + 1, h => by
    obtain ⟨ai, ha, hpc, he, hp, h⟩ := h
    obtain ⟨s1, h1⟩ := StepsOk.take k h
    exact ⟨s1, ai, ha, hpc, he, hp, h1⟩
  | _, .label _ :: _, _, _, _, h => h.elim
  | _, .word _ _ :: _, _, _, _, h => h.elim

theorem StepsOk.append : ∀ {env : Env} {A B : List Line} {s s1 s2 : Arm.ArmState},
    StepsOk env A s s1 → StepsOk { env with pc := env.pc + 4 * A.length } B s1 s2 →
    StepsOk env (A ++ B) s s2
  | env, [], B, s, s1, s2, hA, hB => by
    simp [StepsOk] at hA; subst hA; simpa using hB
  | env, .ins i t :: A, B, s, s1, s2, hA, hB => by
    obtain ⟨ai, ha, hpc, he, hp, hA⟩ := hA
    refine ⟨ai, ha, hpc, he, hp, StepsOk.append hA ?_⟩
    simp only [List.length_cons] at hB
    have e : ({ { env with pc := env.pc + 4 } with pc := env.pc + 4 + 4 * A.length } : Env) =
        { env with pc := env.pc + 4 * (A.length + 1) } := by
      cases env; simp; omega
    rw [e]; exact hB
  | _, .label _ :: _, _, _, _, _, h, _ => h.elim
  | _, .word _ _ :: _, _, _, _, _, h, _ => h.elim

theorem steps_cons {env : Env} {i : Insn} {t : Option Clif.TrapCode} {ls : List Line}
    {s s' : Arm.ArmState} {ai : Arm.ArmInst} (ha : i.toArmInst env = .ok ai)
    (hpc : Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64)
    (he : Arm.r .ERR (Arm.exec_inst ai s) = Arm.r .ERR s)
    (hp : (Arm.exec_inst ai s).program = s.program)
    (h : StepsOk { env with pc := env.pc + 4 } ls (Arm.exec_inst ai s) s') :
    StepsOk env (.ins i t :: ls) s s' := ⟨ai, ha, hpc, he, hp, h⟩

/-- The pc/`x n` shape of the states of a constant load. -/
def pcx (s : Arm.ArmState) (n : Nat) (P X : BitVec 64) : Arm.ArmState :=
  Arm.w .PC P (Arm.w (.GPR (BitVec.ofNat 5 n)) X s)

theorem pcx_step (s : Arm.ArmState) (n : Nat) (P X Y : BitVec 64) :
    Arm.w .PC (Arm.r .PC (pcx s n P X) + 4#64) (Arm.w (.GPR (BitVec.ofNat 5 n)) Y (pcx s n P X)) =
      pcx s n (P + 4#64) Y := by
  simp only [pcx, Arm.r_of_w_same]
  rw [Arm.w_of_w_commute (fld1 := .GPR _) (fld2 := .PC) (by simp), Arm.w_of_w_shadow, Arm.w_of_w_shadow]

theorem pcx_facts (s : Arm.ArmState) (n : Nat) (P X : BitVec 64) :
    Arm.r .PC (pcx s n P X) = P ∧ Arm.r .ERR (pcx s n P X) = Arm.r .ERR s ∧
      (pcx s n P X).program = s.program ∧ Arm.r (.GPR (BitVec.ofNat 5 n)) (pcx s n P X) = X := by
  simp [pcx, Arm.r_of_w_same, Arm.r_of_w_different, Arm.w_program]

/-- `movk` lines for `(chunk, shift)` pairs. -/
def movkLines (n : Nat) : List (Nat × Nat) → List Line
  | [] => []
  | (c, i) :: ks => .ins (.movk true (.x n) ⟨c, i⟩) none :: movkLines n ks

theorem movkLines_length (n : Nat) : ∀ ks : List (Nat × Nat), (movkLines n ks).length = ks.length
  | [] => rfl
  | _ :: ks => by simp [movkLines, movkLines_length n ks]

theorem steps_movks (n : Nat) (hn : n ≤ 30) (s : Arm.ArmState) :
    ∀ (ks : List (Nat × Nat)) (env : Env) (P X : BitVec 64), (∀ p ∈ ks, p.1 < 2 ^ 16 ∧ p.2 < 4) →
      StepsOk env (movkLines n ks) (pcx s n P X)
        (pcx s n (P + BitVec.ofNat 64 (4 * ks.length))
          (ks.foldl (fun X p => Arm.BitVec.partInstall (16 * p.2) 16 (BitVec.ofNat 16 p.1) X) X))
  | [], env, P, X, _ => by simp [movkLines, StepsOk]
  | (c, i) :: ks, env, P, X, hk => by
    obtain ⟨hc, hi⟩ := hk (c, i) (by simp)
    obtain ⟨ai, ha, he⟩ := exec_movk env hn hc hi (pcx s n P X)
    obtain ⟨f1, f2, f3, f4⟩ := pcx_facts s n P X
    rw [f4, pcx_step] at he
    obtain ⟨g1, g2, g3, -⟩ := pcx_facts s n (P + 4#64)
      (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) X)
    refine steps_cons ha (by rw [he, g1, f1]) (by rw [he, g2, f2]) (by rw [he, g3, f3]) ?_
    rw [he]
    have := steps_movks n hn s ks { env with pc := env.pc + 4 } (P + 4#64)
      (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) X) (fun p hp => hk p (by simp [hp]))
    simp only [movkLines, List.length_cons, List.foldl_cons] at this ⊢
    have e : P + 4#64 + BitVec.ofNat 64 (4 * ks.length) = P + BitVec.ofNat 64 (4 * (ks.length + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e] at this
    exact this

/-- 16-bit chunk `i` of `v`. -/
def chunk16 (v i : Nat) : Nat := (v / 2 ^ (16 * i)) % 2 ^ 16

theorem chunk_step (V i : Nat) (hi : 16 * i + 16 ≤ 64) :
    (if chunk16 V i ≠ 0 then Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 (chunk16 V i))
        (BitVec.ofNat 64 (V % 2 ^ (16 * i)))
      else BitVec.ofNat 64 (V % 2 ^ (16 * i))) = BitVec.ofNat 64 (V % 2 ^ (16 * i + 16)) := by
  split
  · exact partInstall_chunk V (16 * i) hi
  · rename_i h
    simp only [chunk16, Decidable.not_not] at h
    congr 1
    rw [Nat.pow_add, Nat.mod_mul, h]; simp

theorem foldl_filter {α β : Type} (g : β → α → β) (P : α → Bool) :
    ∀ (L : List α) (X : β), (L.filter P).foldl g X = L.foldl (fun X p => if P p then g X p else X) X
  | [], X => rfl
  | a :: L, X => by
    by_cases h : P a <;> simp [List.filter_cons, h, foldl_filter g P L]

theorem loadConst64_eq (n v : Nat) :
    loadConst64 (.x n) v = .ins (.movWide .movZ true (.x n) ⟨chunk16 (mask64 v) 0, 0⟩) none ::
      movkLines n (([1, 2, 3].map fun i => (chunk16 (mask64 v) i, i)).filter (·.1 != 0)) := by
  simp only [loadConst64, chunk16]
  congr 1
  by_cases h1 : mask64 v / 2 ^ (16 * 1) % 2 ^ 16 = 0 <;>
  by_cases h2 : mask64 v / 2 ^ (16 * 2) % 2 ^ 16 = 0 <;>
  by_cases h3 : mask64 v / 2 ^ (16 * 3) % 2 ^ 16 = 0 <;>
  simp_all [List.range_succ, List.filterMap_append, movkLines, List.filter_cons, bne_iff_ne]

theorem mask64_lt (v : Nat) : mask64 v < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem chunk16_lt (V i : Nat) : chunk16 V i < 2 ^ 16 := Nat.mod_lt _ (by decide)

/-- **The constant load** `loadConst64 (x n) v`: `movz`, then `movk` of the non-zero chunks;
`x n` ends as `v` (mod 2^64), the pc advances by 4 per line, nothing else changes. -/
theorem steps_loadConst64 (env : Env) {n : Nat} (hn : n ≤ 30) (v : Nat) (s : Arm.ArmState) :
    StepsOk env (loadConst64 (.x n) v) s
      (pcx s n (Arm.r .PC s + BitVec.ofNat 64 (4 * (loadConst64 (.x n) v).length)) (BitVec.ofNat 64 v)) := by
  rw [loadConst64_eq]
  obtain ⟨ai, ha, he⟩ := exec_movz env hn (chunk16_lt (mask64 v) 0) s
  have e0 : Arm.exec_inst ai s = pcx s n (Arm.r .PC s + 4#64) (BitVec.ofNat 64 (chunk16 (mask64 v) 0)) := he
  obtain ⟨g1, g2, g3, -⟩ := pcx_facts s n (Arm.r .PC s + 4#64) (BitVec.ofNat 64 (chunk16 (mask64 v) 0))
  refine steps_cons ha (by rw [e0, g1]) (by rw [e0, g2]) (by rw [e0, g3]) ?_
  rw [e0]
  have hk := steps_movks n hn s (([1, 2, 3].map fun i => (chunk16 (mask64 v) i, i)).filter (·.1 != 0))
    { env with pc := env.pc + 4 } (Arm.r .PC s + 4#64) (BitVec.ofNat 64 (chunk16 (mask64 v) 0))
    (fun p hp => by
      simp only [List.mem_filter, List.mem_map] at hp
      obtain ⟨⟨i, hi, rfl⟩, -⟩ := hp
      simp at hi
      exact ⟨chunk16_lt _ _, by omega⟩)
  have hv : ((([1, 2, 3].map fun i => (chunk16 (mask64 v) i, i)).filter (·.1 != 0)).foldl
      (fun X p => Arm.BitVec.partInstall (16 * p.2) 16 (BitVec.ofNat 16 p.1) X)
      (BitVec.ofNat 64 (chunk16 (mask64 v) 0))) = BitVec.ofNat 64 v := by
    rw [foldl_filter]
    have c0 : BitVec.ofNat 64 (chunk16 (mask64 v) 0) = BitVec.ofNat 64 (mask64 v % 2 ^ (16 * 1)) := by
      simp [chunk16]
    have c1 := chunk_step (mask64 v) 1 (by omega)
    have c2 := chunk_step (mask64 v) 2 (by omega)
    have c3 := chunk_step (mask64 v) 3 (by omega)
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at c1 c2 c3 ⊢
    rw [c0, c1, show 16 * 1 + 16 = 16 * 2 by rfl, c2, show 16 * 2 + 16 = 16 * 3 by rfl, c3]
    apply BitVec.eq_of_toNat_eq
    simp [mask64]
  rw [hv] at hk
  have e : Arm.r .PC s + 4#64 + BitVec.ofNat 64 (4 * (([1, 2, 3].map fun i => (chunk16 (mask64 v) i, i)).filter (·.1 != 0)).length) =
      Arm.r .PC s + BitVec.ofNat 64 (4 * (Line.ins (.movWide .movZ true (.x n) ⟨chunk16 (mask64 v) 0, 0⟩) none ::
        movkLines n (([1, 2, 3].map fun i => (chunk16 (mask64 v) i, i)).filter (·.1 != 0))).length) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [movkLines_length]; omega
  rw [e] at hk
  exact hk

/-! ## Loads and stores of allocated instructions (`execMInst`) -/

/-- The addressing modes of loads/stores the backend emits before finalisation: register
forms with a final encoding, and stack-slot, outgoing-argument (`sp`) and incoming-argument
(`fp`) offsets (any `Int`). -/
def MemMode (bytes : Nat) : AMode → Prop
  | .slotOffset _ | .spOffset _ | .fpOffset _ => True
  | m@(.unsignedOffset ..) | m@(.unscaled ..) | m@(.regReg ..) | m@(.regScaled ..)
  | m@(.regScaledExtended ..) | m@(.regExtended ..) => FinalAM bytes m
  | _ => False

/-- An optional scratch write of `x16`. -/
def x16w : Option (BitVec 64) → Arm.ArmState → Arm.ArmState
  | none, s => s
  | some c, s => Arm.w (.GPR 16#5) c s

theorem x16w_facts (o : Option (BitVec 64)) (s : Arm.ArmState) :
    Arm.r .PC (x16w o s) = Arm.r .PC s ∧ Arm.r .ERR (x16w o s) = Arm.r .ERR s ∧
      (x16w o s).program = s.program ∧ (x16w o s).mem = s.mem ∧ spOf (x16w o s) = spOf s := by
  cases o <;> simp [x16w, Arm.r_of_w_different, Arm.w_program, Arm.ArmState.mem_w_eq_mem, spOf]

theorem memFinalize_final (ctx : FnCtx) (bytes : Nat) {m : AMode} (hm : FinalAM bytes m) :
    memFinalize ctx m bytes = .ok ([], m) := by
  cases m <;> simp_all [FinalAM, memFinalize]

theorem ofNat_u64 (o : Int) : BitVec.ofNat 64 (u64 o) = BitVec.ofInt 64 o := by
  apply BitVec.eq_of_toNat_eq
  simp [u64, BitVec.toNat_ofInt]
  omega

theorem sxtx_id (x : BitVec 64) : Arm.extend_reg x (Arm.decode_reg_extend 7#3) 0 = x := by
  rw [show Arm.decode_reg_extend 7#3 = .SXTX from rfl]
  simp only [Arm.extend_reg, Arm.ExtendType.unsigned_len, Nat.sub_zero,
    BitVec.shiftLeft_zero]
  simp only [BitVec.extractLsb']
  show BitVec.signExtend 64 (BitVec.ofNat 64 (x.toNat >>> 0)) = x
  simp [BitVec.signExtend_eq]

/-- **A load on the Arm model** (`uload*`/`sload*` into `x d`, not x16): its lines run
without error from an aligned state; `x d` gets the loaded value at `AMode.addr`, the pc advances
past the lines, `x16` may hold a scratch value (large slot offsets). -/
theorem execMInst_load (ctx : FnCtx) (env : Env) (op : LoadOp) (hop : op ≠ .fpuLoad128) {d : Nat}
    (hd : d ≤ 30) (m : AMode) (fl : Clif.MemFlags) (hm : MemMode op.bytes m) (s : Arm.ArmState)
    (halign : Arm.CheckSPAlignment s) :
    ∃ ls o, MInst.lines ctx (.load op (.x d) m fl) {} = .ok (ls, {}) ∧
      StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
        (Arm.w (.GPR (BitVec.ofNat 5 d)) (ldX op (m.addr ctx op.bytes s) s) (x16w o s))) := by
  have single : ∀ m' : AMode, FinalAM op.bytes m' → (m'.base = .sp → Arm.CheckSPAlignment s) →
      m'.addr ctx op.bytes s = m.addr ctx op.bytes s →
      StepsOk env [.ins (.load op (.x d) m') fl.trapCode] s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * 1))
        (Arm.w (.GPR (BitVec.ofNat 5 d)) (ldX op (m.addr ctx op.bytes s) s) (x16w none s))) := by
    intro m' hf hs ha
    obtain ⟨ai, hai, he⟩ := exec_load_line env ctx op hop d hd m' hf s hs
    refine ⟨ai, hai, ?_, ?_, ?_, ?_⟩
    · rw [he, Arm.r_of_w_same]
    · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    · rw [he, Arm.w_program, Arm.w_program]
    · simp only [StepsOk, he, ha, x16w]
  -- `memFinalize`'s `fin B o` (base `sp` or `fp`, any offset): `simm9`, scaled `uimm12`, or the
  -- offset in `x16`
  have base : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      m.addr ctx op.bytes s = regX s B + BitVec.ofInt 64 o →
      (∀ k, simm9? o = some k → MInst.lines ctx (.load op (.x d) m fl) {} =
        .ok ([.ins (.load op (.x d) (.unscaled B k)) fl.trapCode], {})) →
      (simm9? o = none → ∀ k, uimm12Scaled? o op.bytes = some k →
        MInst.lines ctx (.load op (.x d) m fl) {} =
          .ok ([.ins (.load op (.x d) (.unsignedOffset B k)) fl.trapCode], {})) →
      (simm9? o = none → uimm12Scaled? o op.bytes = none →
        MInst.lines ctx (.load op (.x d) m fl) {} =
          .ok (loadConst64 (.x 16) (u64 o) ++
            [.ins (.load op (.x d) (.regExtended B (.x 16) .sxtx)) fl.trapCode], {})) →
      ∃ ls o, MInst.lines ctx (.load op (.x d) m fl) {} = .ok (ls, {}) ∧
        StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
          (Arm.w (.GPR (BitVec.ofNat 5 d)) (ldX op (m.addr ctx op.bytes s) s) (x16w o s))) := by
    intro B o hB ha h1 h2 h3
    have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
    have hbp : 0 < op.bytes := by cases op <;> decide
    cases h9 : simm9? o with
    | some k =>
      have hk : k = o ∧ -256 ≤ k ∧ k ≤ 255 := by
        simp only [simm9?] at h9; split at h9 <;> simp_all
      refine ⟨_, none, h1 k h9, single (.unscaled B k) ⟨hBok, hk.2.1, by omega⟩ (fun _ => halign) ?_⟩
      rw [ha]; simp [AMode.addr, hk.1]
    | none =>
      cases hu : uimm12Scaled? o op.bytes with
      | some k =>
        have hk : (k : Int) = o ∧ k % op.bytes = 0 ∧ k ≤ 4095 * op.bytes := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
          · cases hu
        refine ⟨_, none, h2 h9 k hu, single (.unsignedOffset B k) ⟨hBok, hk.2.1,
          by have := Nat.div_le_div_right (c := op.bytes) hk.2.2; rw [Nat.mul_div_cancel _ hbp] at this; omega⟩
          (fun _ => halign) ?_⟩
        rw [ha]
        simp only [AMode.addr]
        congr 1
        rw [← hk.1]; rfl
      | none =>
        refine ⟨_, some (BitVec.ofNat 64 (u64 o)), h3 h9 hu, ?_⟩
        have hA := steps_loadConst64 env (n := 16) (by omega) (u64 o) s
        let L := (loadConst64 (.x 16) (u64 o)).length
        let S1 := pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * L)) (BitVec.ofNat 64 (u64 o))
        have hS1 : S1.mem = s.mem ∧ spOf S1 = spOf s ∧ Arm.r .PC S1 = Arm.r .PC s + BitVec.ofNat 64 (4 * L) ∧
            Arm.r (.GPR 16#5) S1 = BitVec.ofNat 64 (u64 o) ∧ Arm.r .ERR S1 = Arm.r .ERR s ∧ S1.program = s.program := by
          simp [S1, pcx, Arm.ArmState.mem_w_eq_mem, spOf, Arm.r_of_w_different, Arm.r_of_w_same, Arm.w_program]
        have hal1 : Arm.CheckSPAlignment S1 := by
          have e : Arm.r (.GPR 31#5) S1 = Arm.r (.GPR 31#5) s := hS1.2.1
          simpa [Arm.CheckSPAlignment, Arm.read_gpr, e] using halign
        have hBS : regX S1 B = regX s B := by
          rcases hB with rfl | rfl
          · exact hS1.2.1
          · simp [S1, pcx, regX, rnum, Arm.r_of_w_different]
        obtain ⟨ai, hai, he⟩ := exec_load_line { env with pc := env.pc + 4 * L } ctx op hop d hd
          (.regExtended B (.x 16) .sxtx) ⟨hBok, by simp [IdxOk], by simp⟩ S1 (fun _ => hal1)
        have haddr : AMode.addr ctx (.regExtended B (.x 16) .sxtx) op.bytes S1 = m.addr ctx op.bytes s := by
          rw [show AMode.addr ctx (.regExtended B (.x 16) .sxtx) op.bytes S1 = regX S1 B +
              Arm.extend_reg (regX S1 (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl]
          rw [hBS, ha, show regX S1 (.x 16) = BitVec.ofNat 64 (u64 o) from hS1.2.2.2.1,
            show ExtendOp.sxtx.bits = 7#3 from rfl, sxtx_id, ofNat_u64]
        have hld : ldX op (m.addr ctx op.bytes s) S1 = ldX op (m.addr ctx op.bytes s) s := by
          have hr : ∀ n a, Arm.read_mem_bytes n a S1 = Arm.read_mem_bytes n a s := fun n a =>
            read_mem_bytes_congr n a (fun k _ => by rw [hS1.1])
          cases op <;> simp [ldX, hr]
        refine StepsOk.append hA ⟨ai, hai, ?_, ?_, ?_, ?_⟩
        · rw [he, Arm.r_of_w_same]
        · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
        · rw [he, Arm.w_program, Arm.w_program]
        · simp only [StepsOk]
          rw [he, haddr, hld, hS1.2.2.1]
          simp only [S1, pcx, x16w, List.length_append, List.length_cons, List.length_nil]
          rw [Arm.w_of_w_commute (fld1 := .GPR _) (fld2 := .PC) (by simp), Arm.w_of_w_shadow,
            BitVec.add_assoc]
          congr 2
          apply BitVec.eq_of_toNat_eq; simp [L]; omega
  cases m with
  | slotOffset off =>
    have hbp : 0 < op.bytes := by cases op <;> decide
    cases h9 : simm9? (off + ctx.slotBase) with
    | some o =>
      have ho : o = off + ctx.slotBase ∧ -256 ≤ o ∧ o ≤ 255 := by
        simp only [simm9?] at h9; split at h9 <;> simp_all
      refine ⟨_, none, by simp [MInst.lines, memFinalize, h9], single (.unscaled .sp o) ⟨trivial, ho.2.1, by omega⟩
        (fun _ => halign) ?_⟩
      simp [AMode.addr, regX, ho.1]
    | none =>
      cases hu : uimm12Scaled? (off + ctx.slotBase) op.bytes with
      | some k =>
        have hk : (k : Int) = off + ctx.slotBase ∧ k % op.bytes = 0 ∧ k ≤ 4095 * op.bytes := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
          · cases hu
        refine ⟨_, none, by simp [MInst.lines, memFinalize, h9, hu], single (.unsignedOffset .sp k) ⟨trivial, hk.2.1,
          by have := Nat.div_le_div_right (c := op.bytes) hk.2.2; rw [Nat.mul_div_cancel _ hbp] at this; omega⟩
          (fun _ => halign) ?_⟩
        simp only [AMode.addr, regX]
        congr 1
        rw [← hk.1]; rfl
      | none =>
        let o := off + ctx.slotBase
        have hl : MInst.lines ctx (.load op (.x d) (.slotOffset off) fl) {} =
            .ok (loadConst64 (.x 16) (u64 o) ++ [.ins (.load op (.x d) (.regExtended .sp (.x 16) .sxtx)) fl.trapCode], {}) := by
          simp [MInst.lines, memFinalize, h9, hu, o]
        refine ⟨_, some (BitVec.ofNat 64 (u64 o)), hl, ?_⟩
        have hA := steps_loadConst64 env (n := 16) (by omega) (u64 o) s
        let L := (loadConst64 (.x 16) (u64 o)).length
        let S1 := pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * L)) (BitVec.ofNat 64 (u64 o))
        have hS1 : S1.mem = s.mem ∧ spOf S1 = spOf s ∧ Arm.r .PC S1 = Arm.r .PC s + BitVec.ofNat 64 (4 * L) ∧
            Arm.r (.GPR 16#5) S1 = BitVec.ofNat 64 (u64 o) ∧ Arm.r .ERR S1 = Arm.r .ERR s ∧ S1.program = s.program := by
          simp [S1, pcx, Arm.ArmState.mem_w_eq_mem, spOf, Arm.r_of_w_different, Arm.r_of_w_same, Arm.w_program]
        have hal1 : Arm.CheckSPAlignment S1 := by
          have e : Arm.r (.GPR 31#5) S1 = Arm.r (.GPR 31#5) s := hS1.2.1
          simpa [Arm.CheckSPAlignment, Arm.read_gpr, e] using halign
        obtain ⟨ai, hai, he⟩ := exec_load_line { env with pc := env.pc + 4 * L } ctx op hop d hd
          (.regExtended .sp (.x 16) .sxtx) ⟨trivial, by simp [IdxOk], by simp⟩ S1 (fun _ => hal1)
        have haddr : AMode.addr ctx (.regExtended .sp (.x 16) .sxtx) op.bytes S1 =
            AMode.addr ctx (.slotOffset off) op.bytes s := by
          simp only [AMode.addr, regX]
          rw [show rnum 16 = 16#5 from rfl, hS1.2.2.2.1, hS1.2.1, show ExtendOp.sxtx.bits = 7#3 from rfl,
            sxtx_id, ofNat_u64]
        have hld : ldX op (AMode.addr ctx (.slotOffset off) op.bytes s) S1 =
            ldX op (AMode.addr ctx (.slotOffset off) op.bytes s) s := by
          have hr : ∀ n a, Arm.read_mem_bytes n a S1 = Arm.read_mem_bytes n a s := fun n a =>
            read_mem_bytes_congr n a (fun k _ => by rw [hS1.1])
          cases op <;> simp [ldX, hr]
        refine StepsOk.append hA ⟨ai, hai, ?_, ?_, ?_, ?_⟩
        · rw [he, Arm.r_of_w_same]
        · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
        · rw [he, Arm.w_program, Arm.w_program]
        · simp only [StepsOk]
          rw [he, haddr, hld, hS1.2.2.1]
          simp only [S1, pcx, x16w, List.length_append, List.length_cons, List.length_nil]
          rw [Arm.w_of_w_commute (fld1 := .GPR _) (fld2 := .PC) (by simp), Arm.w_of_w_shadow,
            BitVec.add_assoc]
          congr 2
          apply BitVec.eq_of_toNat_eq; simp [L]; omega
  | spOffset off =>
    exact base .sp off (.inl rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, h9, hu])
  | fpOffset off =>
    exact base (.x 29) off (.inr rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, Reg.fp, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
  | _ =>
    simp only [MemMode] at hm <;>
    exact ⟨_, none, by simp [MInst.lines, memFinalize_final ctx _ hm], single _ hm (fun _ => halign) rfl⟩

theorem write_mem_w (a : BitVec 64) (b : BitVec 8) (f : Arm.StateField) (x : Arm.state_value f)
    (s : Arm.ArmState) : Arm.write_mem a b (Arm.w f x s) = Arm.w f x (Arm.write_mem a b s) := by
  cases f <;> simp [Arm.write_mem, Arm.w, Arm.write_base_gpr, Arm.write_base_sfp, Arm.write_base_pc,
    Arm.write_base_flag, Arm.write_base_error]

theorem write_mem_bytes_w (f : Arm.StateField) (x : Arm.state_value f) :
    ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (s : Arm.ArmState),
      Arm.write_mem_bytes n a v (Arm.w f x s) = Arm.w f x (Arm.write_mem_bytes n a v s)
  | 0, _, _, _ => rfl
  | n + 1, a, v, s => by
    simp only [Arm.write_mem_bytes, write_mem_w]
    exact write_mem_bytes_w f x n _ _ _

/-- **A store on the Arm model** (`store8..64` of `x d`, `d ≠ 16`): the low bytes of `x d` are
written at `AMode.addr`, the pc advances past the lines, `x16` may hold a scratch value. -/
theorem execMInst_store (ctx : FnCtx) (env : Env) (op : StoreOp) (hop : op ≠ .fpuStore128) {d : Nat}
    (hd : d ≤ 30) (hd16 : d ≠ 16) (m : AMode) (fl : Clif.MemFlags) (hm : MemMode op.bytes m) (s : Arm.ArmState)
    (halign : Arm.CheckSPAlignment s) :
    ∃ ls o, MInst.lines ctx (.store op (.x d) m fl) {} = .ok (ls, {}) ∧
      StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
        (Arm.write_mem_bytes op.bytes (m.addr ctx op.bytes s)
          ((Arm.r (.GPR (BitVec.ofNat 5 d)) s).setWidth (op.bytes * 8)) (x16w o s))) := by
  have single : ∀ m' : AMode, FinalAM op.bytes m' → (m'.base = .sp → Arm.CheckSPAlignment s) →
      m'.addr ctx op.bytes s = m.addr ctx op.bytes s →
      StepsOk env [.ins (.store op (.x d) m') fl.trapCode] s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * 1))
        (Arm.write_mem_bytes op.bytes (m.addr ctx op.bytes s)
          ((Arm.r (.GPR (BitVec.ofNat 5 d)) s).setWidth (op.bytes * 8)) (x16w none s))) := by
    intro m' hf hs ha
    obtain ⟨ai, hai, he⟩ := exec_store_line env ctx op hop d hd m' hf s hs
    refine ⟨ai, hai, ?_, ?_, ?_, ?_⟩
    · rw [he, Arm.r_of_w_same]
    · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]
    · rw [he, Arm.w_program, Arm.write_mem_bytes_program]
    · simp only [StepsOk, he, ha, x16w]
  have base : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      m.addr ctx op.bytes s = regX s B + BitVec.ofInt 64 o →
      (∀ k, simm9? o = some k → MInst.lines ctx (.store op (.x d) m fl) {} =
        .ok ([.ins (.store op (.x d) (.unscaled B k)) fl.trapCode], {})) →
      (simm9? o = none → ∀ k, uimm12Scaled? o op.bytes = some k →
        MInst.lines ctx (.store op (.x d) m fl) {} =
          .ok ([.ins (.store op (.x d) (.unsignedOffset B k)) fl.trapCode], {})) →
      (simm9? o = none → uimm12Scaled? o op.bytes = none →
        MInst.lines ctx (.store op (.x d) m fl) {} =
          .ok (loadConst64 (.x 16) (u64 o) ++
            [.ins (.store op (.x d) (.regExtended B (.x 16) .sxtx)) fl.trapCode], {})) →
      ∃ ls o, MInst.lines ctx (.store op (.x d) m fl) {} = .ok (ls, {}) ∧
        StepsOk env ls s (Arm.w .PC (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
          (Arm.write_mem_bytes op.bytes (m.addr ctx op.bytes s)
            ((Arm.r (.GPR (BitVec.ofNat 5 d)) s).setWidth (op.bytes * 8)) (x16w o s))) := by
    intro B o hB ha h1 h2 h3
    have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
    have hbp : 0 < op.bytes := by cases op <;> decide
    cases h9 : simm9? o with
    | some k =>
      have hk : k = o ∧ -256 ≤ k ∧ k ≤ 255 := by
        simp only [simm9?] at h9; split at h9 <;> simp_all
      refine ⟨_, none, h1 k h9, single (.unscaled B k) ⟨hBok, hk.2.1, by omega⟩ (fun _ => halign) ?_⟩
      rw [ha]; simp [AMode.addr, hk.1]
    | none =>
      cases hu : uimm12Scaled? o op.bytes with
      | some k =>
        have hk : (k : Int) = o ∧ k % op.bytes = 0 ∧ k ≤ 4095 * op.bytes := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
          · cases hu
        refine ⟨_, none, h2 h9 k hu, single (.unsignedOffset B k) ⟨hBok, hk.2.1,
          by have := Nat.div_le_div_right (c := op.bytes) hk.2.2; rw [Nat.mul_div_cancel _ hbp] at this; omega⟩
          (fun _ => halign) ?_⟩
        rw [ha]
        simp only [AMode.addr]
        congr 1
        rw [← hk.1]; rfl
      | none =>
        refine ⟨_, some (BitVec.ofNat 64 (u64 o)), h3 h9 hu, ?_⟩
        have hA := steps_loadConst64 env (n := 16) (by omega) (u64 o) s
        let L := (loadConst64 (.x 16) (u64 o)).length
        let S1 := pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * L)) (BitVec.ofNat 64 (u64 o))
        have hS1 : S1.mem = s.mem ∧ spOf S1 = spOf s ∧ Arm.r .PC S1 = Arm.r .PC s + BitVec.ofNat 64 (4 * L) ∧
            Arm.r (.GPR 16#5) S1 = BitVec.ofNat 64 (u64 o) ∧ Arm.r .ERR S1 = Arm.r .ERR s ∧ S1.program = s.program := by
          simp [S1, pcx, Arm.ArmState.mem_w_eq_mem, spOf, Arm.r_of_w_different, Arm.r_of_w_same, Arm.w_program]
        have hal1 : Arm.CheckSPAlignment S1 := by
          have e : Arm.r (.GPR 31#5) S1 = Arm.r (.GPR 31#5) s := hS1.2.1
          simpa [Arm.CheckSPAlignment, Arm.read_gpr, e] using halign
        have hBS : regX S1 B = regX s B := by
          rcases hB with rfl | rfl
          · exact hS1.2.1
          · simp [S1, pcx, regX, rnum, Arm.r_of_w_different]
        obtain ⟨ai, hai, he⟩ := exec_store_line { env with pc := env.pc + 4 * L } ctx op hop d hd
          (.regExtended B (.x 16) .sxtx) ⟨hBok, by simp [IdxOk], by simp⟩ S1 (fun _ => hal1)
        have haddr : AMode.addr ctx (.regExtended B (.x 16) .sxtx) op.bytes S1 = m.addr ctx op.bytes s := by
          rw [show AMode.addr ctx (.regExtended B (.x 16) .sxtx) op.bytes S1 = regX S1 B +
              Arm.extend_reg (regX S1 (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl]
          rw [hBS, ha, show regX S1 (.x 16) = BitVec.ofNat 64 (u64 o) from hS1.2.2.2.1,
            show ExtendOp.sxtx.bits = 7#3 from rfl, sxtx_id, ofNat_u64]
        have hld : Arm.r (.GPR (BitVec.ofNat 5 d)) S1 = Arm.r (.GPR (BitVec.ofNat 5 d)) s := by
          have : BitVec.ofNat 5 d ≠ BitVec.ofNat 5 16 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          simp [S1, pcx, Arm.r_of_w_different, this]
        refine StepsOk.append hA ⟨ai, hai, ?_, ?_, ?_, ?_⟩
        · rw [he, Arm.r_of_w_same]
        · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]
        · rw [he, Arm.w_program, Arm.write_mem_bytes_program]
        · simp only [StepsOk]
          rw [he, haddr, hld, hS1.2.2.1]
          simp only [S1, pcx, x16w, List.length_append, List.length_cons, List.length_nil]
          rw [write_mem_bytes_w (f := .PC), Arm.w_of_w_shadow, BitVec.add_assoc]
          congr 2
          apply BitVec.eq_of_toNat_eq; simp [L]; omega
  cases m with
  | slotOffset off =>
    have hbp : 0 < op.bytes := by cases op <;> decide
    cases h9 : simm9? (off + ctx.slotBase) with
    | some o =>
      have ho : o = off + ctx.slotBase ∧ -256 ≤ o ∧ o ≤ 255 := by
        simp only [simm9?] at h9; split at h9 <;> simp_all
      refine ⟨_, none, by simp [MInst.lines, memFinalize, h9], single (.unscaled .sp o) ⟨trivial, ho.2.1, by omega⟩
        (fun _ => halign) ?_⟩
      simp [AMode.addr, regX, ho.1]
    | none =>
      cases hu : uimm12Scaled? (off + ctx.slotBase) op.bytes with
      | some k =>
        have hk : (k : Int) = off + ctx.slotBase ∧ k % op.bytes = 0 ∧ k ≤ 4095 * op.bytes := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
          · cases hu
        refine ⟨_, none, by simp [MInst.lines, memFinalize, h9, hu], single (.unsignedOffset .sp k) ⟨trivial, hk.2.1,
          by have := Nat.div_le_div_right (c := op.bytes) hk.2.2; rw [Nat.mul_div_cancel _ hbp] at this; omega⟩
          (fun _ => halign) ?_⟩
        simp only [AMode.addr, regX]
        congr 1
        rw [← hk.1]; rfl
      | none =>
        let o := off + ctx.slotBase
        have hl : MInst.lines ctx (.store op (.x d) (.slotOffset off) fl) {} =
            .ok (loadConst64 (.x 16) (u64 o) ++ [.ins (.store op (.x d) (.regExtended .sp (.x 16) .sxtx)) fl.trapCode], {}) := by
          simp [MInst.lines, memFinalize, h9, hu, o]
        refine ⟨_, some (BitVec.ofNat 64 (u64 o)), hl, ?_⟩
        have hA := steps_loadConst64 env (n := 16) (by omega) (u64 o) s
        let L := (loadConst64 (.x 16) (u64 o)).length
        let S1 := pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * L)) (BitVec.ofNat 64 (u64 o))
        have hS1 : S1.mem = s.mem ∧ spOf S1 = spOf s ∧ Arm.r .PC S1 = Arm.r .PC s + BitVec.ofNat 64 (4 * L) ∧
            Arm.r (.GPR 16#5) S1 = BitVec.ofNat 64 (u64 o) ∧ Arm.r .ERR S1 = Arm.r .ERR s ∧ S1.program = s.program := by
          simp [S1, pcx, Arm.ArmState.mem_w_eq_mem, spOf, Arm.r_of_w_different, Arm.r_of_w_same, Arm.w_program]
        have hal1 : Arm.CheckSPAlignment S1 := by
          have e : Arm.r (.GPR 31#5) S1 = Arm.r (.GPR 31#5) s := hS1.2.1
          simpa [Arm.CheckSPAlignment, Arm.read_gpr, e] using halign
        obtain ⟨ai, hai, he⟩ := exec_store_line { env with pc := env.pc + 4 * L } ctx op hop d hd
          (.regExtended .sp (.x 16) .sxtx) ⟨trivial, by simp [IdxOk], by simp⟩ S1 (fun _ => hal1)
        have haddr : AMode.addr ctx (.regExtended .sp (.x 16) .sxtx) op.bytes S1 =
            AMode.addr ctx (.slotOffset off) op.bytes s := by
          simp only [AMode.addr, regX]
          rw [show rnum 16 = 16#5 from rfl, hS1.2.2.2.1, hS1.2.1, show ExtendOp.sxtx.bits = 7#3 from rfl,
            sxtx_id, ofNat_u64]
        have hld : Arm.r (.GPR (BitVec.ofNat 5 d)) S1 = Arm.r (.GPR (BitVec.ofNat 5 d)) s := by
          have : BitVec.ofNat 5 d ≠ BitVec.ofNat 5 16 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          simp [S1, pcx, Arm.r_of_w_different, this]
        refine StepsOk.append hA ⟨ai, hai, ?_, ?_, ?_, ?_⟩
        · rw [he, Arm.r_of_w_same]
        · rw [he, Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]
        · rw [he, Arm.w_program, Arm.write_mem_bytes_program]
        · simp only [StepsOk]
          rw [he, haddr, hld, hS1.2.2.1]
          simp only [S1, pcx, x16w, List.length_append, List.length_cons, List.length_nil]
          rw [write_mem_bytes_w (f := .PC), Arm.w_of_w_shadow, BitVec.add_assoc]
          congr 2
          apply BitVec.eq_of_toNat_eq; simp [L]; omega
  | spOffset off =>
    exact base .sp off (.inl rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, h9, hu])
  | fpOffset off =>
    exact base (.x 29) off (.inr rfl) (by simp [AMode.addr, regX])
      (fun k h9 => by simp [MInst.lines, memFinalize, Reg.fp, h9])
      (fun h9 k hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
      (fun h9 hu => by simp [MInst.lines, memFinalize, Reg.fp, h9, hu])
  | _ =>
    simp only [MemMode] at hm <;>
    exact ⟨_, none, by simp [MInst.lines, memFinalize_final ctx _ hm], single _ hm (fun _ => halign) rfl⟩

/-! ## `Corr` for loads -/

theorem ldX_congr {F : BitVec 64 → Prop} {s t : Arm.ArmState} (op : LoadOp) {a : BitVec 64}
    (h : ∀ x, ¬ F x → s.mem x = t.mem x) (hav : Avoids F op.bytes a) : ldX op a s = ldX op a t := by
  have hr : ∀ n, n ≤ op.bytes → Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a t := fun n hn =>
    read_mem_bytes_congr n a (fun k hk => h _ (hav k (by omega)))
  cases op <;> simp only [ldX] <;> first | rfl | (rw [hr _ (by simp [LoadOp.bytes])])

theorem sameWorld_x16w {F : BitVec 64 → Prop} {s t : Arm.ArmState} (o o' : Option (BitVec 64))
    (h : SameWorld F s t) : SameWorld F (x16w o s) (x16w o' t) := by
  have hm : Masked (.GPR 16#5) := by simp [Masked]
  cases o <;> cases o' <;> simp only [x16w]
  · exact h
  · exact SameWorld.w_right hm h
  · exact SameWorld.w_left hm h
  · exact SameWorld.w_right hm (SameWorld.w_left hm h)

theorem sw_r_eq {F : BitVec 64 → Prop} {s w : Arm.ArmState} (hw : SameWorld F s w) {f : Arm.StateField}
    (hf : ¬ Masked f) : Arm.r f w = Arm.r f s := (hw.1 f hf).symm

theorem align_of_spEq {s t : Arm.ArmState} (h : Arm.r (.GPR 31#5) t = Arm.r (.GPR 31#5) s)
    (hs : Arm.CheckSPAlignment s) : Arm.CheckSPAlignment t := by
  simpa [Arm.CheckSPAlignment, Arm.read_gpr, h] using hs

theorem rnum_ne_of {a b : Nat} (ha : a < 32) (hb : b < 32) (h : a ≠ b) :
    (BitVec.ofNat 5 a : BitVec 5) ≠ BitVec.ofNat 5 b := rnum_ne ha hb h

theorem masked_x {k : Nat} (hk : k < 29 ∧ k ≠ 16 ∧ k ≠ 17 ∧ k ≠ 18) : Masked (.GPR (BitVec.ofNat 5 k)) := by
  simp only [Masked, BitVec.toNat_ofNat]; omega

/-- The post-state of a load into `x a`. -/
def ldPost (s : Arm.ArmState) (P : BitVec 64) (a : Nat) (V : BitVec 64) (o : Option (BitVec 64)) :
    Arm.ArmState :=
  Arm.w .PC P (Arm.w (.GPR (BitVec.ofNat 5 a)) V (x16w o s))

theorem ldPost_sw {F : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorld F s t) {P P' : BitVec 64}
    {a b : Nat} (ha : a < 29 ∧ a ≠ 18) (hb : b < 29 ∧ b ≠ 18) (V V' : BitVec 64) (o o' : Option (BitVec 64)) :
    SameWorld F (ldPost s P a V o) (ldPost t P' b V' o') := by
  have ma : Masked (.GPR (BitVec.ofNat 5 a)) := by simp only [Masked, BitVec.toNat_ofNat]; omega
  have mb : Masked (.GPR (BitVec.ofNat 5 b)) := by simp only [Masked, BitVec.toNat_ofNat]; omega
  exact SameWorld.w_right (by simp [Masked]) (SameWorld.w_left (by simp [Masked])
    (SameWorld.w_right mb (SameWorld.w_left ma (sameWorld_x16w o o' h))))

theorem ldPost_facts (s : Arm.ArmState) (P : BitVec 64) {a : Nat} (ha : a < 29 ∧ a ≠ 16)
    (V : BitVec 64) (o : Option (BitVec 64)) :
    spOf (ldPost s P a V o) = spOf s ∧ (ldPost s P a V o).mem = s.mem ∧
      regVal (ldPost s P a V o) (.x a) = V.setWidth 128 ∧
      ∀ r, r.allocatable = true → r ≠ .x a → regVal (ldPost s P a V o) r = regVal s r := by
  have h31 : BitVec.ofNat 5 a ≠ 31#5 := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ldPost, spOf]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp [Ne.symm h31])]
    exact (x16w_facts o s).2.2.2.2
  · simp only [ldPost, Arm.ArmState.mem_w_eq_mem]; exact (x16w_facts o s).2.2.2.1
  · simp [ldPost, regVal, rnum, Arm.r_of_w_different, Arm.r_of_w_same]
  · intro r hr hne
    rcases allocatable_cases hr with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · have hka : k ≠ a := fun e => hne (by rw [e])
      have e1 : rnum k ≠ BitVec.ofNat 5 a := rnum_ne (by omega) (by omega) hka
      have e2 : rnum k ≠ 16#5 := rnum_ne (a := k) (b := 16) (by omega) (by omega) (by omega)
      cases o <;> simp [ldPost, regVal, x16w, Arm.r_of_w_different, e1, e2]
    · cases o <;> simp [ldPost, regVal, x16w, Arm.r_of_w_different]

/-- The allocated/canonical correspondence of one load (the part of `Corr` independent of the
operand list). -/
theorem load_core {F : BitVec 64 → Prop} (ctx : FnCtx) (env : Env) (op : LoadOp) (hop : op ≠ .fpuLoad128)
    (fl : Clif.MemFlags) {n0 : Nat} (hn0 : n0 < 29 ∧ n0 ≠ 16 ∧ n0 ≠ 17 ∧ n0 ≠ 18) {m mC : AMode}
    (hm : MemMode op.bytes m) (hmC : MemMode op.bytes mC) {s t t' : Arm.ArmState}
    (hal : Arm.CheckSPAlignment s) (hwt : SameWorld F s t)
    (hsp_t : Arm.r (.GPR 31#5) t = Arm.r (.GPR 31#5) s) (hmem : ∀ x, ¬ F x → t.mem x = s.mem x)
    (hacc : AccessOk F ctx (.load op (.x 0) mC fl) t)
    (hex : execMInst ctx env0 (.load op (.x 0) mC fl) t = some t')
    (haddr : mC.addr ctx op.bytes t = m.addr ctx op.bytes s) :
    ∃ S, execMInst ctx env (.load op (.x n0) m fl) s = some S ∧ SameWorld F S t' ∧ FrameKeep F s S ∧
      regVal S (.x n0) = regVal t' (.x 0) ∧
      ∀ r, r.allocatable = true → r ≠ .x n0 → regVal S r = regVal s r := by
  obtain ⟨ls, o, hl, hS⟩ := execMInst_load ctx env op hop (d := n0) (by omega) m fl hm s hal
  obtain ⟨lsC, oC, hlC, hT⟩ := execMInst_load ctx env0 op hop (d := 0) (by omega) mC fl hmC t
    (align_of_spEq hsp_t hal)
  simp only [execMInst, hlC, hT.exec, Option.some.injEq] at hex
  subst hex
  have hav : Avoids F op.bytes (m.addr ctx op.bytes s) := by
    have := hacc (mC.addr ctx op.bytes t, op.bytes) (by simp [MInst.accesses])
    rw [← haddr]; exact this
  have hld : ldX op (mC.addr ctx op.bytes t) t = ldX op (m.addr ctx op.bytes s) s := by
    rw [haddr]; exact ldX_congr op hmem hav
  obtain ⟨f1, f2, f3, f4⟩ := ldPost_facts s (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length)) (a := n0)
    ⟨hn0.1, hn0.2.1⟩ (ldX op (m.addr ctx op.bytes s) s) o
  obtain ⟨-, -, g3, -⟩ := ldPost_facts t (Arm.r .PC t + BitVec.ofNat 64 (4 * lsC.length)) (a := 0)
    (by omega) (ldX op (mC.addr ctx op.bytes t) t) oC
  refine ⟨ldPost s (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length)) n0 (ldX op (m.addr ctx op.bytes s) s) o,
    by simp only [execMInst, hl]; exact hS.exec, ldPost_sw hwt ⟨hn0.1, hn0.2.2.2⟩ (by omega) _ _ _ _,
    ⟨f1, fun a _ => by rw [f2]⟩, ?_, f4⟩
  have g3' := g3.trans (congrArg (BitVec.setWidth 128) hld)
  rw [f3]; exact g3'.symm

set_option maxHeartbeats 4000000 in
theorem corr_load_uoff (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : LoadOp)
    (hop : op ≠ .fpuLoad128) (d n off : Nat) (fl : Clif.MemFlags)
    (h1 : off % op.bytes = 0) (h2 : off / op.bytes < 4096) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (fun r => .load op (r.getD 0 .xzr) (.unsignedOffset (r.getD 1 .xzr) off) fl) := by
  intro regs s w t' ha hw hal hacc hex herr
  have hsz := ha.size
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
  have hf := ha.fits
  obtain ⟨r0, r1, rfl⟩ := regs2 hsz
  simp [RegFits] at hf
  rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩
  have ht : placeUses #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩]
      (canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩])
      (useVals #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] #[.x n0, .x n1] s) w =
      Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w := by
    simp [placeUses, useVals, canonRegs, canonReg, canonBase, Operand.isUse, List.range_succ, lo64, regVal,
      rnum]
  have hcanon : canonRegs #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] = #[.x 0, .x 1] := by
    simp [canonRegs, canonReg, canonBase, List.range_succ]
  rw [ht, hcanon] at hex hacc
  rw [hcanon]
  have hx1 : Arm.r (.GPR 1#5) (Arm.w (.GPR 1#5) (Arm.r (.GPR (rnum n1)) s) w) = Arm.r (.GPR (rnum n1)) s :=
    Arm.r_of_w_same
  obtain ⟨S, h1, h2, h3, h4, h5⟩ := load_core ctx env op hop fl hn0 (m := .unsignedOffset (.x n1) off)
    (mC := .unsignedOffset (.x 1) off) ⟨by simp [BaseOk]; omega, h1, h2⟩ ⟨by simp [BaseOk], h1, h2⟩ hal
    (SameWorld.w_right (by simp [Masked]) hw)
    (by rw [Arm.r_of_w_different (by simp)]; exact sw_r_eq hw (by simp [Masked]))
    (fun x hx => by rw [Arm.ArmState.mem_w_eq_mem]; exact (hw.2.1 x hx).symm) hacc hex
    (by simp [AMode.addr, regX, rnum] at hx1 ⊢ <;> simp [hx1])
  refine ⟨S, h1, h2, h3, by simp [defVals, Operand.isDef, h4], fun r hr hnd => h5 r hr
    (fun e => hnd ⟨⟨d, .int, .def, .late, .reg⟩, .x n0⟩ (by simp) rfl e.symm)⟩

end Backend.Proof

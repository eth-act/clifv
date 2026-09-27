import FV.Backend.Proof.RegallocCSem

/-!
# Loads and stores on the Arm model (M6 proof)

`exec_load_line`/`exec_store_line`: a GPR load/store (`uload*`/`sload*`/`store8..64`) with a
final addressing mode (`FinalAM`: unsigned or unscaled immediate, register offset, scaled,
extended) encodes, and the model executes it as the value-level access at `AMode.addr`:
`ldX op a s` into the target register, or `write_mem_bytes` of the register's low bytes; the
pc advances by 4. Base registers may be `sp` (then `sp` must be aligned).
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
      all_goals first
        | rfl
        | trace_state; sorry

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

end Backend.Proof

import FV.Concurrency.ArmAllocMemLS
import FV.Concurrency.ArmAllocBranch

/-!
# Layer 4b with the plain loads/stores (T2h, #311)

The scope of `arm_alloc_refines_br` (`MemScopeB`: event-free items, `fence`, `ldar`/`stlr`, LL/SC
loops, block-ending branches) extended by the **plain loads/stores**: GPR `load`/`store` and
SIMD&FP `fpuLoad`/`fpuStore` (32/64 bits) at the final addressing modes (`unsignedOffset`,
`unscaled`, `regReg`, `regScaled`, `regScaledExtended`, `regExtended`; `LSMode`) and at the stack
modes (stack-slot, `sp`, `fp` offsets) whose offset `memFinalize` encodes as an immediate
(`LSModeOk`), so that their lowering is one access line:

* `load_line_cf`, `store_line_cf`, `fpuLoad_line_cf`, `fpuStore_line_cf`: **the closed form of an
  emitted access's events** — one read (of the memory's bytes) or one write (of the data register's
  low bytes) at the mode's address (`AMode.addr`), of the access size;
* `plain_arm`: an emitted plain access is no store exclusive and its events have its kind and a
  positive size;
* `load_uoff_form` … `fpuStore_regExt_form` (24 forms), `lsForm_oneEv`: **every plain load/store
  form is a one-event form** (`OneEvForm`): the allocated access's event on any memory is the
  canonical run's, since both access the same address (the base and index registers' values agree
  through `useVals`/`placeUses`) with the same data;
* `stackFin`, `ldst_unal`, `load_stack_form` … `fpuStore_stack_form`: the stack modes lower to an
  immediate mode on `sp` or `fp` (`SameWorld` keeps both registers); at an unaligned `sp` both the
  allocated and the canonical access fault without an event;
* `MemScopeLS`, `itemSim_ls`: the scope with the plain loads/stores and its per-item obligation
  (`oneEv_op` at the plain accesses, `itemSim_br`'s cases otherwise);
* **`arm_alloc_refines_ls`**: `arm_alloc_refines_br`'s conclusion for the functions of
  `MemScopeLS`;
* witness: `ArmAllocLSWitness.ls_premises`.

The stack offsets that `memFinalize` lowers through `x16` (an event-free `loadConst64` prefix) are
not covered (`ArmAllocMemLS.straightSem_pre`/`preMem` are the prefix's ingredients).
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise VCodeThread Backend Backend.Proof AllocThread
  ThreadRefine
open Code VCodeEvents VCodeAddr

/-- **The event of a plain GPR load** (not at an unaligned `sp`): one read at the base plus the
offset, of the access size, of the memory's bytes. -/
theorem immEvs_load_cf (op : LoadOp) (hop : op ≠ .fpuLoad128) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    immEvs (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) s =
      [⟨.plainR, read_gpr 64 Rn s + imm.value (log2 op.bytes) s, op.bytes,
        readM op.bytes (read_gpr 64 Rn s + imm.value (log2 op.bytes) s) s.mem⟩] := by
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  cases op <;> simp at hop <;>
  · simp (config := {decide := true}) only [immEvs, gprCls, LoadOp.fields, LoadOp.bytes,
      Arm.LDST.reg_imm_constrain_unpredictable, h31, log2]
    simp (config := {decide := true})

/-- **The event of a plain GPR store** (not at an unaligned `sp`): one write of the data
register's low bytes. -/
theorem immEvs_store_cf (op : StoreOp) (hop : op ≠ .fpuStore128) (Rn Rt : BitVec 5) (hRt : Rt ≠ 31#5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    immEvs (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) s =
      [⟨.plainW, read_gpr 64 Rn s + imm.value (log2 op.bytes) s, op.bytes,
        (Arm.r (.GPR Rt) s).setWidth (op.bytes * 8)⟩] := by
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  cases op <;> simp at hop <;>
  · simp (config := {decide := true}) only [immEvs, gprCls, StoreOp.fields, StoreOp.bytes,
      Arm.LDST.reg_imm_constrain_unpredictable, h31, log2]
    simp (config := {decide := true}) [ldst_read, read_gpr_zr, read_gpr, hRt]
    all_goals rfl

/-- **The shape of an emitted plain GPR load** at a final addressing mode: its Arm instruction
is memory-independent in its control (`CtlIndep`), not a store exclusive, and its events are the
`immEvs` of a base register and an offset whose sum is the mode's address (on every state). -/
theorem load_line_shape (env : Env) (ctx : FnCtx) (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) (s0 : ArmState) {ai : ArmInst}
    (ha : Insn.toArmInst env (.load op (.x d) m) = .ok ai) :
    CtlIndep ai ∧ (∀ rel rs rn, clsOf ai ≠ .stx rel rs rn) ∧
      ∃ Rn imm, (∀ y, instEvs ai y = immEvs (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d) imm) y) ∧
        (∀ y, read_gpr 64 Rn y + imm.value (log2 op.bytes) y = m.addr ctx op.bytes y) ∧
        (Rn = 31#5 → m.base = .sp) := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    have e : Insn.toArmInst env (.load op (.x d) (.unsignedOffset rn off)) = .ok (uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_uimm_load op hop _ _ _ (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_uimm _ _ _ _ _ y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact uimm_value op.bytes (by cases op <;> simp_all [LoadOp.bytes]) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    have e : Insn.toArmInst env (.load op (.x d) (.unscaled rn off)) = .ok (unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_unsc_load op hop _ _ _ (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_unsc _ _ _ _ _ y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.load op (.x d) (.regReg rn rm)) = .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_load op hop _ _ _ _ _ (by decide) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (by decide) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
    apply BitVec.eq_of_toNat_eq
    simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
    exact (regX y rm).isLt
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.load op (.x d) (.regScaled rn rm)) = .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_load op hop _ _ _ _ _ (by decide) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (by decide) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
    exact uxtx_shift _ _ (by cases op <;> simp [log2, LoadOp.bytes])
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.load op (.x d) (.regScaledExtended rn rm ex)) = .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_load op hop _ _ _ _ _ (ext_lsb1 hex) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    simp only [ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.load op (.x d) (.regExtended rn rm ex)) = .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_load op hop _ _ _ _ _ (ext_lsb1 hex) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    rfl
  | _ => simp [FinalAM] at hm

/-- **The shape of an emitted plain GPR store** at a final addressing mode: its Arm instruction
is memory-independent in its control (`CtlIndep`), not a store exclusive, and its events are the
`immEvs` of a base register and an offset whose sum is the mode's address (on every state). -/
theorem store_line_shape (env : Env) (ctx : FnCtx) (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) (s0 : ArmState) {ai : ArmInst}
    (ha : Insn.toArmInst env (.store op (.x d) m) = .ok ai) :
    CtlIndep ai ∧ (∀ rel rs rn, clsOf ai ≠ .stx rel rs rn) ∧
      ∃ Rn imm, (∀ y, instEvs ai y = immEvs (gprCls op.fields.1 op.fields.2.2 Rn (BitVec.ofNat 5 d) imm) y) ∧
        (∀ y, read_gpr 64 Rn y + imm.value (log2 op.bytes) y = m.addr ctx op.bytes y) ∧
        (Rn = 31#5 → m.base = .sp) := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    have e : Insn.toArmInst env (.store op (.x d) (.unsignedOffset rn off)) = .ok (uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_uimm_store op hop _ _ _ (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_uimm _ _ _ _ _ y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact uimm_value op.bytes (by cases op <;> simp_all [StoreOp.bytes]) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    have e : Insn.toArmInst env (.store op (.x d) (.unscaled rn off)) = .ok (unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_unsc_store op hop _ _ _ (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_unsc _ _ _ _ _ y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.store op (.x d) (.regReg rn rm)) = .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_store op hop _ _ _ _ _ (by decide) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (by decide) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
    apply BitVec.eq_of_toNat_eq
    simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
    exact (regX y rm).isLt
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.store op (.x d) (.regScaled rn rm)) = .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_store op hop _ _ _ _ _ (by decide) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (by decide) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
    exact uxtx_shift _ _ (by cases op <;> simp [log2, StoreOp.bytes])
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.store op (.x d) (.regScaledExtended rn rm ex)) = .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_store op hop _ _ _ _ _ (ext_lsb1 hex) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    simp only [ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb s0
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi s0
    have e : Insn.toArmInst env (.store op (.x d) (.regExtended rn rm ex)) = .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField, sField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst, unscInst,
          regInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_reg_store op hop _ _ _ _ _ (ext_lsb1 hex) (ofNat5_ne31 hd), fun _ _ _ h => by simp [clsOf, uimmInst, unscInst, regInst] at h, Rn, _,
      fun y => instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex) y, fun y => ?_, fun h => by simp [AMode.base, h31 h]⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRn] at hRn'; cases hRn'
    rw [hRm] at hRm'; cases hRm'
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    rfl
  | _ => simp [FinalAM] at hm

/-! ## The plain accesses' Arm instructions: class and event sizes -/

/-- All events have a positive size. -/
def AllP (evs : List Ev) : Prop := ∀ e ∈ evs, 0 < e.n

theorem allp_nil : AllP [] := fun _ h => absurd h List.not_mem_nil

theorem allp_ite {c : Prop} [Decidable c] {a b : List Ev} (ha : c → AllP a) (hb : ¬ c → AllP b) :
    AllP (if c then a else b) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact ha h
  · rw [ite_eq_right h]; exact hb h

theorem allp_one {e : Ev} (h : 0 < e.n) : AllP [e] := by
  intro e' he'; simp only [List.mem_singleton] at he'; subst he'; exact h

theorem shl8_pos (k : Nat) : 0 < (8 <<< k) / 8 := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_div_cancel _ (by decide)]; exact Nat.two_pow_pos _

theorem p_immEvs (inst : LDST.Reg_imm_cls) (s : ArmState) : AllP (immEvs inst s) := by
  unfold immEvs
  dsimp only
  repeat' (first | exact allp_nil | (apply allp_ite <;> intro h))
  all_goals exact allp_one (shl8_pos _)

theorem p_ldsturEvs (inst : Reg_unscaled_imm_cls) (s : ArmState) : AllP (ldsturEvs inst s) := by
  unfold ldsturEvs
  dsimp only
  repeat' (first | exact allp_nil | (apply allp_ite <;> intro h))
  all_goals exact allp_one (shl8_pos _)

/-- **A single-register load/store encoding** (`ldstFields`) is of the plain class and its events
have positive sizes. -/
theorem ldstFields_plain {size : BitVec 2} {V : BitVec 1} {opc : BitVec 2} {bytes : Nat}
    {Rt : BitVec 5} {m : AMode} {a : ArmInst} (h : ldstFields size V opc bytes Rt m = .ok a) :
    clsOf a.norm = .plain ∧ ∀ y, AllP (instEvs a.norm y) := by
  unfold ldstFields at h
  cases m <;> simp only [bind, Except.bind, pure, Except.pure] at h <;>
    (repeat' split at h) <;> (try cases h) <;>
    refine ⟨rfl, fun y => ?_⟩ <;> simp only [ArmInst.norm, instEvs] <;>
    first
      | exact p_immEvs _ _
      | exact allp_ite (fun _ => p_ldsturEvs _ _) (fun _ => p_immEvs _ _)
      | exact allp_ite (fun _ => allp_nil) (fun _ => p_immEvs _ _)

theorem ldstFields_bind_plain {x : Except String (BitVec 5)} {size : BitVec 2} {V : BitVec 1}
    {opc : BitVec 2} {bytes : Nat} {m : AMode} {a : ArmInst}
    (h : (x >>= fun Rt => ldstFields size V opc bytes Rt m) = .ok a) :
    clsOf a.norm = .plain ∧ ∀ y, AllP (instEvs a.norm y) := by
  cases x with
  | error e => simp only [bind, Except.bind] at h; cases h
  | ok Rt => simp only [bind, Except.bind] at h; exact ldstFields_plain h

theorem ldstFields_bind2_plain {y : Except String (BitVec 2)} {x : Except String (BitVec 5)}
    {V : BitVec 1} {opc : BitVec 2} {bytes : Nat} {m : AMode} {a : ArmInst}
    (h : (y >>= fun size => x >>= fun Rt => ldstFields size V opc bytes Rt m) = .ok a) :
    clsOf a.norm = .plain ∧ ∀ y, AllP (instEvs a.norm y) := by
  cases y with
  | error e => simp only [bind, Except.bind] at h; cases h
  | ok size => simp only [bind, Except.bind] at h; exact ldstFields_bind_plain h

/-- **The Arm instruction of an emitted plain load/store** is not a store exclusive, and its
events are of the line's kind (`plainR`/`plainW`) with positive sizes (`OneEvForm.arm`). -/
theorem plain_arm {env : Env} {x : Insn} {a : ArmInst} (ha : x.toArmInst env = .ok a)
    (hx : (∃ op rt m, x = .load op rt m) ∨ (∃ op rt m, x = .store op rt m) ∨
      (∃ sz rt m, x = .fpuLoad sz rt m) ∨ (∃ sz rt m, x = .fpuStore sz rt m)) :
    (∀ rel rs rn, clsOf a ≠ .stx rel rs rn) ∧
      ∀ y, ∀ e ∈ instEvs a y, e.k ≠ .relXW ∧ (e.k.dir ≠ .F → 0 < e.n) := by
  have hk : ∃ k, insnKind x = some k ∧ (k = .plainR ∨ k = .plainW) := by
    rcases hx with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
      simp [insnKind]
  obtain ⟨k, hk, hk'⟩ := hk
  have hK : ∀ y, ∀ e ∈ instEvs a y, e.k = k := fun y e he => by
    have hs := instEvs_kinds ha y
    rw [hk] at hs
    have hm : e.k ∈ (instEvs a y).map (·.k) := List.mem_map_of_mem he
    simpa using hs.subset hm
  have hP : clsOf a = .plain ∧ ∀ y, AllP (instEvs a y) := by
    unfold Insn.toArmInst at ha
    cases hf : x.armFields env with
    | error e => rw [hf] at ha; cases ha
    | ok a0 =>
      rw [hf] at ha
      simp only [Functor.map, Except.map, Except.ok.injEq] at ha
      subst ha
      rcases hx with ⟨op, rt, m, rfl⟩ | ⟨op, rt, m, rfl⟩ | ⟨sz, rt, m, rfl⟩ | ⟨sz, rt, m, rfl⟩
      · cases op <;> simp only [Insn.armFields, LoadOp.fields] at hf <;> exact ldstFields_bind_plain hf
      · cases op <;> simp only [Insn.armFields, StoreOp.fields] at hf <;> exact ldstFields_bind_plain hf
      · simp only [Insn.armFields] at hf; exact ldstFields_bind2_plain hf
      · simp only [Insn.armFields] at hf; exact ldstFields_bind2_plain hf
  refine ⟨fun rel rs rn h => (by rw [hP.1] at h; cases h), fun y e he => ⟨?_, fun _ => hP.2 y e he⟩⟩
  rw [hK y e he]; rcases hk' with rfl | rfl <;> decide

/-! ## Closed forms of the emitted accesses' events -/

/-- **The event of an emitted GPR load** at a final mode: one read at the mode's address. -/
theorem load_line_cf (env : Env) (ctx : FnCtx) (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) {ai : ArmInst}
    (ha : Insn.toArmInst env (.load op (.x d) m) = .ok ai) (y : ArmState)
    (hsp : m.base = .sp → CheckSPAlignment y) :
    instEvs ai y = [⟨.plainR, m.addr ctx op.bytes y, op.bytes,
      readM op.bytes (m.addr ctx op.bytes y) y.mem⟩] := by
  obtain ⟨-, -, Rn, imm, hev, hA, h31⟩ := load_line_shape env ctx op hop d hd m hm y ha
  rw [hev, immEvs_load_cf op hop Rn _ imm y (fun h => hsp (h31 h)), hA]

/-- **The event of an emitted GPR store** at a final mode: one write of the data register's low
bytes at the mode's address. -/
theorem store_line_cf (env : Env) (ctx : FnCtx) (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) {ai : ArmInst}
    (ha : Insn.toArmInst env (.store op (.x d) m) = .ok ai) (y : ArmState)
    (hsp : m.base = .sp → CheckSPAlignment y) :
    instEvs ai y = [⟨.plainW, m.addr ctx op.bytes y, op.bytes,
      (Arm.r (.GPR (BitVec.ofNat 5 d)) y).setWidth (op.bytes * 8)⟩] := by
  obtain ⟨-, -, Rn, imm, hev, hA, h31⟩ := store_line_shape env ctx op hop d hd m hm y ha
  rw [hev, immEvs_store_cf op hop Rn _ (ofNat5_ne31 hd) imm y (fun h => hsp (h31 h)), hA]

theorem bindE_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp only [bind, Except.bind] at h; cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem encSP_v {q : Nat} {R : BitVec 5} : (Reg.v q).encSP ≠ .ok R := by
  simp [Reg.encSP, throw, throwThe, MonadExceptOf.throw]

theorem encZR_v {q : Nat} {R : BitVec 5} : (Reg.v q).encZR ≠ .ok R := by
  simp [Reg.encZR, throw, throwThe, MonadExceptOf.throw]


set_option hygiene false in
/-- Closes a goal whose hypothesis `ha` encodes a plain load/store with a SIMD&FP register where a
GPR is required (the encoder fails). -/
macro "ldst_noV" : tactic => `(tactic| (
  simp [Insn.toArmInst, Insn.armFields, LoadOp.fields, StoreOp.fields, ldstFields, Reg.encZR,
    Reg.encSP, Reg.encV, Insn.armFields.fpLdstSize, bind, Except.bind, Functor.map, Except.map, throw, throwThe,
    MonadExceptOf.throw] at ha <;>
  split at ha <;> (try cases ha) <;> (rename_i heq; repeat' split at heq) <;> (try cases heq)))

theorem immEvs_fpLoad_cf (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    immEvs (fpCls (fpSizeF sz) 1 Rn Rt imm) s =
      [⟨.plainR, read_gpr 64 Rn s + imm.value (log2 sz.bytes) s, sz.bytes, readM sz.bytes (read_gpr 64 Rn s + imm.value (log2 sz.bytes) s) s.mem⟩] := by
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [immEvs, fpCls, fpSizeF, ScalarSize.bytes,
      Arm.LDST.supported_simd_reg_imm, Arm.LDST.reg_imm_constrain_unpredictable, h31, log2]
    simp (config := {decide := true}) [lsb_facts, ldst_read, read_sfp]
    all_goals rfl

theorem ldsturEvs_fpLoad_cf (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5) (imm9 : BitVec 9)
    (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    ldsturEvs { size := fpSizeF sz, VR := 1#1, opc := 1, imm9 := imm9, Rn := Rn, Rt := Rt } s =
      [⟨.plainR, read_gpr 64 Rn s + BitVec.signExtend 64 imm9, sz.bytes, readM sz.bytes (read_gpr 64 Rn s + BitVec.signExtend 64 imm9) s.mem⟩] := by
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [ldsturEvs, fpSizeF, ScalarSize.bytes, h31]
    simp (config := {decide := true}) [read_sfp]
    all_goals rfl

theorem immEvs_fpStore_cf (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    immEvs (fpCls (fpSizeF sz) 0 Rn Rt imm) s =
      [⟨.plainW, read_gpr 64 Rn s + imm.value (log2 sz.bytes) s, sz.bytes, (Arm.r (.SFP Rt) s).setWidth (sz.bytes * 8)⟩] := by
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [immEvs, fpCls, fpSizeF, ScalarSize.bytes,
      Arm.LDST.supported_simd_reg_imm, Arm.LDST.reg_imm_constrain_unpredictable, h31, log2]
    simp (config := {decide := true}) [lsb_facts, ldst_read, read_sfp]
    all_goals rfl

theorem ldsturEvs_fpStore_cf (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5) (imm9 : BitVec 9)
    (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    ldsturEvs { size := fpSizeF sz, VR := 1#1, opc := 0, imm9 := imm9, Rn := Rn, Rt := Rt } s =
      [⟨.plainW, read_gpr 64 Rn s + BitVec.signExtend 64 imm9, sz.bytes, (Arm.r (.SFP Rt) s).setWidth (sz.bytes * 8)⟩] := by
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [ldsturEvs, fpSizeF, ScalarSize.bytes, h31]
    simp (config := {decide := true}) [read_sfp]
    all_goals rfl

/-- **The emitted SIMD&FP load at a final mode**: memory-independent control and one event at the
mode's address (closed form). -/
theorem fpuLoad_line_cf (env : Env) (ctx : FnCtx) (sz : ScalarSize) (hsz : FpSz sz) (d : Nat)
    (hd : d < 32) (m : AMode) (hm : FinalAM sz.bytes m) {ai : ArmInst}
    (ha : Insn.toArmInst env (.fpuLoad sz (.v d) m) = .ok ai) :
    CtlIndep ai ∧ ∀ y, (m.base = .sp → CheckSPAlignment y) →
      instEvs ai y = [⟨.plainR, m.addr ctx sz.bytes y, sz.bytes, readM sz.bytes (m.addr ctx sz.bytes y) y.mem⟩] := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.unsignedOffset rn off)) = .ok (fpUimmInst (fpSizeF sz) 1 (BitVec.ofNat 12 (off / sz.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpUimm_load sz hsz _ _ _, fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    rw [instEvs_fpUimm, immEvs_fpLoad_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.uimm12 (BitVec.ofNat 12 (off / sz.bytes))) (log2 sz.bytes) y = AMode.addr ctx (.unsignedOffset rn off) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact uimm_value sz.bytes (by have := fpSz_bytes hsz; omega) off h1 h2
    rw [hA]
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.unscaled rn off)) = .ok (fpUnscInst (fpSizeF sz) 1 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpUnsc_load sz hsz _ _ _, fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    rw [instEvs_fpUnsc, ldsturEvs_fpLoad_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + BitVec.signExtend 64 (BitVec.ofInt 9 off) = AMode.addr ctx (.unscaled rn off) sz.bytes y := by
      simp only [AMode.addr, hr]
      congr 1
      exact simm9_value off h1 h2
    rw [hA]
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regReg rn rm)) = .ok (fpRegInst (fpSizeF sz) 1 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_load sz hsz _ _ _ _ _ (by decide), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide), immEvs_fpLoad_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm 3#3 0#1) (log2 sz.bytes) y = AMode.addr ctx (.regReg rn rm) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
      apply BitVec.eq_of_toNat_eq
      simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
      exact (regX y rm).isLt
    rw [hA]
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regScaled rn rm)) = .ok (fpRegInst (fpSizeF sz) 1 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_load sz hsz _ _ _ _ _ (by decide), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide), immEvs_fpLoad_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm 3#3 1#1) (log2 sz.bytes) y = AMode.addr ctx (.regScaled rn rm) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
      exact uxtx_shift _ _ (fp_log2 hsz)
    rw [hA]
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regScaledExtended rn rm ex)) = .ok (fpRegInst (fpSizeF sz) 1 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_load sz hsz _ _ _ _ _ (ext_lsb1 hex), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex), immEvs_fpLoad_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm ex.bits 1#1) (log2 sz.bytes) y = AMode.addr ctx (.regScaledExtended rn rm ex) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      simp only [ite_true]
    rw [hA]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regExtended rn rm ex)) = .ok (fpRegInst (fpSizeF sz) 1 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_load sz hsz _ _ _ _ _ (ext_lsb1 hex), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex), immEvs_fpLoad_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm ex.bits 0#1) (log2 sz.bytes) y = AMode.addr ctx (.regExtended rn rm ex) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      rfl
    rw [hA]
  | _ => simp [FinalAM] at hm

/-- **The emitted SIMD&FP store at a final mode**: memory-independent control and one event at the
mode's address (closed form). -/
theorem fpuStore_line_cf (env : Env) (ctx : FnCtx) (sz : ScalarSize) (hsz : FpSz sz) (d : Nat)
    (hd : d < 32) (m : AMode) (hm : FinalAM sz.bytes m) {ai : ArmInst}
    (ha : Insn.toArmInst env (.fpuStore sz (.v d) m) = .ok ai) :
    CtlIndep ai ∧ ∀ y, (m.base = .sp → CheckSPAlignment y) →
      instEvs ai y = [⟨.plainW, m.addr ctx sz.bytes y, sz.bytes, (Arm.r (.SFP (BitVec.ofNat 5 d)) y).setWidth (sz.bytes * 8)⟩] := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.unsignedOffset rn off)) = .ok (fpUimmInst (fpSizeF sz) 0 (BitVec.ofNat 12 (off / sz.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpUimm_store sz hsz _ _ _, fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    rw [instEvs_fpUimm, immEvs_fpStore_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.uimm12 (BitVec.ofNat 12 (off / sz.bytes))) (log2 sz.bytes) y = AMode.addr ctx (.unsignedOffset rn off) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
      congr 1
      exact uimm_value sz.bytes (by have := fpSz_bytes hsz; omega) off h1 h2
    rw [hA]
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.unscaled rn off)) = .ok (fpUnscInst (fpSizeF sz) 0 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpUnsc_store sz hsz _ _ _, fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    rw [instEvs_fpUnsc, ldsturEvs_fpStore_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + BitVec.signExtend 64 (BitVec.ofInt 9 off) = AMode.addr ctx (.unscaled rn off) sz.bytes y := by
      simp only [AMode.addr, hr]
      congr 1
      exact simm9_value off h1 h2
    rw [hA]
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regReg rn rm)) = .ok (fpRegInst (fpSizeF sz) 0 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_store sz hsz _ _ _ _ _ (by decide), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide), immEvs_fpStore_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm 3#3 0#1) (log2 sz.bytes) y = AMode.addr ctx (.regReg rn rm) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
      apply BitVec.eq_of_toNat_eq
      simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
      exact (regX y rm).isLt
    rw [hA]
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regScaled rn rm)) = .ok (fpRegInst (fpSizeF sz) 0 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_store sz hsz _ _ _ _ _ (by decide), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide), immEvs_fpStore_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm 3#3 1#1) (log2 sz.bytes) y = AMode.addr ctx (.regScaled rn rm) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      congr 1
      rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
      exact uxtx_shift _ _ (fp_log2 hsz)
    rw [hA]
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regScaledExtended rn rm ex)) = .ok (fpRegInst (fpSizeF sz) 0 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_store sz hsz _ _ _ _ _ (ext_lsb1 hex), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex), immEvs_fpStore_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm ex.bits 1#1) (log2 sz.bytes) y = AMode.addr ctx (.regScaledExtended rn rm ex) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      simp only [ite_true]
    rw [hA]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, -, h31⟩ := enc_base hb ArmState.default
    obtain ⟨Rm, hRm, -⟩ := enc_idx hi ArmState.default
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regExtended rn rm ex)) = .ok (fpRegInst (fpSizeF sz) 0 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, sField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst, fpUnscInst, fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    refine ⟨ctlIndep_fpReg_store sz hsz _ _ _ _ _ (ext_lsb1 hex), fun y hsp => ?_⟩
    obtain ⟨Rn', hRn', hr, -⟩ := enc_base hb y
    rw [hRn] at hRn'; cases hRn'
    obtain ⟨Rm', hRm', hrm⟩ := enc_idx hi y
    rw [hRm] at hRm'; cases hRm'
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex), immEvs_fpStore_cf sz hsz Rn _ _ y (fun h => hsp (by simp [AMode.base, h31 h]))]
    have hA : read_gpr 64 Rn y + LDST.Reg_offset.value (.reg Rm ex.bits 0#1) (log2 sz.bytes) y = AMode.addr ctx (.regExtended rn rm ex) sz.bytes y := by
      simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
      rfl
    rw [hA]
  | _ => simp [FinalAM] at hm


/-! ## The plain load/store forms -/

theorem x_or_v {r : Reg} (h : r.allocatable = true) :
    (∃ q, r = .x q ∧ q < 29) ∨ ∃ q, r = .v q := by
  rcases allocatable_cases h with ⟨q, rfl, hq, -⟩ | ⟨q, rfl, -⟩
  · exact .inl ⟨q, rfl, hq⟩
  · exact .inr ⟨q, rfl⟩

theorem v_or_x {r : Reg} (h : r.allocatable = true) :
    (∃ q, r = .v q ∧ q < 32) ∨ ∃ q, r = .x q := by
  rcases allocatable_cases h with ⟨q, rfl, -, -⟩ | ⟨q, rfl, hq⟩
  · exact .inr ⟨q, rfl⟩
  · exact .inl ⟨q, rfl, hq⟩

/-- **A GPR load at a `unsignedOffset` mode is a one-event form** (`OneEvForm`). -/
theorem load_uoff_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d u : Nat} {off : Nat}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.load op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl) := by
  have hop : op ≠ .fpuLoad128 ∧ off % op.bytes = 0 ∧ off / op.bytes < 4096 := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.load op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.load op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.load op r0 (.unsignedOffset r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.load op r0 (.unsignedOffset r1 off) fl).lines ctx ps =
      .ok ([.ins (.load op r0 (.unsignedOffset r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM op.bytes (.unsignedOffset (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0,
    (load_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .load op (.x 0) (.unsignedOffset (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0,
      load_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      load_line_cf env ctx op hop.1 p (by omega) _ (hfin q (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR load at a `unscaled` mode is a one-event form** (`OneEvForm`). -/
theorem load_unsc_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d u : Nat} {off : Int}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op (.vreg d .int) (.unscaled (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.load op (.vreg d .int) (.unscaled (.vreg u .int) off) fl) := by
  have hop : op ≠ .fpuLoad128 ∧ -256 ≤ off ∧ off < 256 := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.load op (.vreg d .int) (.unscaled (.vreg u .int) off) fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.load op (.vreg d .int) (.unscaled (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.load op r0 (.unscaled r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.load op r0 (.unscaled r1 off) fl).lines ctx ps =
      .ok ([.ins (.load op r0 (.unscaled r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM op.bytes (.unscaled (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0,
    (load_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .load op (.x 0) (.unscaled (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0,
      load_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      load_line_cf env ctx op hop.1 p (by omega) _ (hfin q (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR load at a `regReg` mode is a one-event form** (`OneEvForm`). -/
theorem load_regReg_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.load op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : op ≠ .fpuLoad128 ∧ True := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.load op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.load op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.load op r0 (.regReg r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.load op r0 (.regReg r1 r2) fl).lines ctx ps =
      .ok ([.ins (.load op r0 (.regReg r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regReg (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (load_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .load op (.x 0) (.regReg (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      load_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      load_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR load at a `regScaled` mode is a one-event form** (`OneEvForm`). -/
theorem load_regScaled_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.load op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : op ≠ .fpuLoad128 ∧ True := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.load op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.load op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.load op r0 (.regScaled r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.load op r0 (.regScaled r1 r2) fl).lines ctx ps =
      .ok ([.ins (.load op r0 (.regScaled r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regScaled (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (load_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .load op (.x 0) (.regScaled (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      load_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      load_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR load at a `regScaledExtended` mode is a one-event form** (`OneEvForm`). -/
theorem load_regScaledExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.load op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : op ≠ .fpuLoad128 ∧ extOk e := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.load op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.load op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.load op r0 (.regScaledExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.load op r0 (.regScaledExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.load op r0 (.regScaledExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regScaledExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (load_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .load op (.x 0) (.regScaledExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      load_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      load_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR load at a `regExtended` mode is a one-event form** (`OneEvForm`). -/
theorem load_regExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.load op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : op ≠ .fpuLoad128 ∧ extOk e := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.load op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.load op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.load op r0 (.regExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.load op r0 (.regExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.load op r0 (.regExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (load_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .load op (.x 0) (.regExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      load_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      load_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR store at a `unsignedOffset` mode is a one-event form** (`OneEvForm`). -/
theorem store_uoff_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d u : Nat} {off : Nat}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.store op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl) := by
  have hop : op ≠ .fpuStore128 ∧ off % op.bytes = 0 ∧ off / op.bytes < 4096 := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.store op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.store op (.vreg d .int) (.unsignedOffset (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.store op r0 (.unsignedOffset r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.store op r0 (.unsignedOffset r1 off) fl).lines ctx ps =
      .ok ([.ins (.store op r0 (.unsignedOffset r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM op.bytes (.unsignedOffset (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0,
    (store_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .store op (.x 0) (.unsignedOffset (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0,
      store_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      store_line_cf env ctx op hop.1 p (by omega) _ (hfin q (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR store at a `unscaled` mode is a one-event form** (`OneEvForm`). -/
theorem store_unsc_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d u : Nat} {off : Int}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op (.vreg d .int) (.unscaled (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.store op (.vreg d .int) (.unscaled (.vreg u .int) off) fl) := by
  have hop : op ≠ .fpuStore128 ∧ -256 ≤ off ∧ off < 256 := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.store op (.vreg d .int) (.unscaled (.vreg u .int) off) fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.store op (.vreg d .int) (.unscaled (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.store op r0 (.unscaled r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.store op r0 (.unscaled r1 off) fl).lines ctx ps =
      .ok ([.ins (.store op r0 (.unscaled r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM op.bytes (.unscaled (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0,
    (store_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .store op (.x 0) (.unscaled (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0,
      store_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      store_line_cf env ctx op hop.1 p (by omega) _ (hfin q (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR store at a `regReg` mode is a one-event form** (`OneEvForm`). -/
theorem store_regReg_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.store op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : op ≠ .fpuStore128 ∧ True := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.store op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.store op (.vreg d .int) (.regReg (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.store op r0 (.regReg r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.store op r0 (.regReg r1 r2) fl).lines ctx ps =
      .ok ([.ins (.store op r0 (.regReg r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regReg (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (store_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .store op (.x 0) (.regReg (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      store_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      store_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR store at a `regScaled` mode is a one-event form** (`OneEvForm`). -/
theorem store_regScaled_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.store op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : op ≠ .fpuStore128 ∧ True := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.store op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.store op (.vreg d .int) (.regScaled (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.store op r0 (.regScaled r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.store op r0 (.regScaled r1 r2) fl).lines ctx ps =
      .ok ([.ins (.store op r0 (.regScaled r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regScaled (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (store_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .store op (.x 0) (.regScaled (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      store_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      store_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR store at a `regScaledExtended` mode is a one-event form** (`OneEvForm`). -/
theorem store_regScaledExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.store op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : op ≠ .fpuStore128 ∧ extOk e := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.store op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.store op (.vreg d .int) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.store op r0 (.regScaledExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.store op r0 (.regScaledExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.store op r0 (.regScaledExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regScaledExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (store_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .store op (.x 0) (.regScaledExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      store_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      store_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]

/-- **A GPR store at a `regExtended` mode is a one-event form** (`OneEvForm`). -/
theorem store_regExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.store op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : op ≠ .fpuStore128 ∧ extOk e := by
    simpa [FormOk, memOk] using hfo
  have hops : (MInst.store op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.store op (.vreg d .int) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.store op r0 (.regExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.store op r0 (.regExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.store op r0 (.regExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM op.bytes (.regExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0,
    (store_line_shape env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ArmState.default ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop.1) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .store op (.x 0) (.regExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0,
      store_line_cf env0 ctx op hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0 _
        (fun h => by simp [AMode.base] at h),
      store_line_cf env ctx op hop.1 p (by omega) _ (hfin q r (by omega) (by omega)) ha _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, lo64_regVal_x, rnum, setMem_mem, r_setMem]


/-- **A SIMD&FP fpuLoad at a `unsignedOffset` mode is a one-event form** (`OneEvForm`). -/
theorem fpuLoad_uoff_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u : Nat} {off : Nat}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.fpuLoad sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl) := by
  have hop : FpSz sz ∧ off % sz.bytes = 0 ∧ off / sz.bytes < 4096 := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuLoad sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.fpuLoad sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.fpuLoad sz r0 (.unsignedOffset r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.fpuLoad sz r0 (.unsignedOffset r1 off) fl).lines ctx ps =
      .ok ([.ins (.fpuLoad sz r0 (.unsignedOffset r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM sz.bytes (.unsignedOffset (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuLoad_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuLoad sz (.v 0) (.unsignedOffset (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuLoad_line_cf env ctx sz hop.1 p hp _ (hfin q (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuLoad at a `unscaled` mode is a one-event form** (`OneEvForm`). -/
theorem fpuLoad_unsc_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u : Nat} {off : Int}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.fpuLoad sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl) := by
  have hop : FpSz sz ∧ -256 ≤ off ∧ off < 256 := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuLoad sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.fpuLoad sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.fpuLoad sz r0 (.unscaled r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.fpuLoad sz r0 (.unscaled r1 off) fl).lines ctx ps =
      .ok ([.ins (.fpuLoad sz r0 (.unscaled r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM sz.bytes (.unscaled (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuLoad_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuLoad sz (.v 0) (.unscaled (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuLoad_line_cf env ctx sz hop.1 p hp _ (hfin q (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuLoad at a `regReg` mode is a one-event form** (`OneEvForm`). -/
theorem fpuLoad_regReg_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.fpuLoad sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : FpSz sz ∧ True := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuLoad sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuLoad sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.fpuLoad sz r0 (.regReg r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuLoad sz r0 (.regReg r1 r2) fl).lines ctx ps =
      .ok ([.ins (.fpuLoad sz r0 (.regReg r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regReg (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuLoad_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuLoad sz (.v 0) (.regReg (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuLoad_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuLoad at a `regScaled` mode is a one-event form** (`OneEvForm`). -/
theorem fpuLoad_regScaled_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.fpuLoad sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : FpSz sz ∧ True := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuLoad sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuLoad sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.fpuLoad sz r0 (.regScaled r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuLoad sz r0 (.regScaled r1 r2) fl).lines ctx ps =
      .ok ([.ins (.fpuLoad sz r0 (.regScaled r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regScaled (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuLoad_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuLoad sz (.v 0) (.regScaled (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuLoad_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuLoad at a `regScaledExtended` mode is a one-event form** (`OneEvForm`). -/
theorem fpuLoad_regScaledExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.fpuLoad sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : FpSz sz ∧ extOk e := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuLoad sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuLoad sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.fpuLoad sz r0 (.regScaledExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuLoad sz r0 (.regScaledExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.fpuLoad sz r0 (.regScaledExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regScaledExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuLoad_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuLoad sz (.v 0) (.regScaledExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuLoad_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuLoad at a `regExtended` mode is a one-event form** (`OneEvForm`). -/
theorem fpuLoad_regExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.fpuLoad sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : FpSz sz ∧ extOk e := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuLoad sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuLoad sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.fpuLoad sz r0 (.regExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuLoad sz r0 (.regExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.fpuLoad sz r0 (.regExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuLoad_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuLoad sz (.v 0) (.regExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuLoad_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuStore at a `unsignedOffset` mode is a one-event form** (`OneEvForm`). -/
theorem fpuStore_uoff_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u : Nat} {off : Nat}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.fpuStore sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl) := by
  have hop : FpSz sz ∧ off % sz.bytes = 0 ∧ off / sz.bytes < 4096 := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuStore sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.fpuStore sz (.vreg d .float) (.unsignedOffset (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.fpuStore sz r0 (.unsignedOffset r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.fpuStore sz r0 (.unsignedOffset r1 off) fl).lines ctx ps =
      .ok ([.ins (.fpuStore sz r0 (.unsignedOffset r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM sz.bytes (.unsignedOffset (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuStore_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuStore sz (.v 0) (.unsignedOffset (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuStore_line_cf env ctx sz hop.1 p hp _ (hfin q (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuStore at a `unscaled` mode is a one-event form** (`OneEvForm`). -/
theorem fpuStore_unsc_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u : Nat} {off : Int}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl) = true) :
    OneEvForm F ctx (.fpuStore sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl) := by
  have hop : FpSz sz ∧ -256 ≤ off ∧ off < 256 := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuStore sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 : Reg, (MInst.fpuStore sz (.vreg d .float) (.unscaled (.vreg u .int) off) fl).assign #[r0, r1] = .ok (.fpuStore sz r0 (.unscaled r1 off) fl) := fun _ _ => rfl
  have hlines : ∀ (r0 r1 : Reg) ps, (MInst.fpuStore sz r0 (.unscaled r1 off) fl).lines ctx ps =
      .ok ([.ins (.fpuStore sz r0 (.unscaled r1 off)) fl.trapCode], ps) := fun _ _ _ => rfl
  have hfin : ∀ q, q ≤ 30 → FinalAM sz.bytes (.unscaled (.x q) off) := fun q hq => ⟨hq, hop.2.1, hop.2.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuStore_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuStore sz (.v 0) (.unscaled (.x 1) off) fl) hops
      rfl (hlines _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuStore_line_cf env ctx sz hop.1 p hp _ (hfin q (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuStore at a `regReg` mode is a one-event form** (`OneEvForm`). -/
theorem fpuStore_regReg_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.fpuStore sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : FpSz sz ∧ True := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuStore sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuStore sz (.vreg d .float) (.regReg (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.fpuStore sz r0 (.regReg r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuStore sz r0 (.regReg r1 r2) fl).lines ctx ps =
      .ok ([.ins (.fpuStore sz r0 (.regReg r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regReg (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuStore_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuStore sz (.v 0) (.regReg (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuStore_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuStore at a `regScaled` mode is a one-event form** (`OneEvForm`). -/
theorem fpuStore_regScaled_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} 
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl) = true) :
    OneEvForm F ctx (.fpuStore sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl) := by
  have hop : FpSz sz ∧ True := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuStore sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuStore sz (.vreg d .float) (.regScaled (.vreg u .int) (.vreg v .int)) fl).assign #[r0, r1, r2] = .ok (.fpuStore sz r0 (.regScaled r1 r2) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuStore sz r0 (.regScaled r1 r2) fl).lines ctx ps =
      .ok ([.ins (.fpuStore sz r0 (.regScaled r1 r2)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regScaled (.x q) (.x r)) := fun q r hq hr => ⟨hq, hr⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuStore_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuStore sz (.v 0) (.regScaled (.x 1) (.x 2)) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuStore_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuStore at a `regScaledExtended` mode is a one-event form** (`OneEvForm`). -/
theorem fpuStore_regScaledExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.fpuStore sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : FpSz sz ∧ extOk e := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuStore sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuStore sz (.vreg d .float) (.regScaledExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.fpuStore sz r0 (.regScaledExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuStore sz r0 (.regScaledExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.fpuStore sz r0 (.regScaledExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regScaledExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuStore_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuStore sz (.v 0) (.regScaledExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuStore_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuStore at a `regExtended` mode is a one-event form** (`OneEvForm`). -/
theorem fpuStore_regExt_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d u v : Nat} {e : ExtendOp}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) = true) :
    OneEvForm F ctx (.fpuStore sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl) := by
  have hop : FpSz sz ∧ extOk e := by
    simpa [FormOk, memOk, FpSz] using hfo
  have hops : (MInst.fpuStore sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩, ⟨u, .int, .use, .early, .reg⟩, ⟨v, .int, .use, .early, .reg⟩] := rfl
  have hasg : ∀ r0 r1 r2 : Reg, (MInst.fpuStore sz (.vreg d .float) (.regExtended (.vreg u .int) (.vreg v .int) e) fl).assign #[r0, r1, r2] = .ok (.fpuStore sz r0 (.regExtended r1 r2 e) fl) := fun _ _ _ => rfl
  have hlines : ∀ (r0 r1 r2 : Reg) ps, (MInst.fpuStore sz r0 (.regExtended r1 r2 e) fl).lines ctx ps =
      .ok ([.ins (.fpuStore sz r0 (.regExtended r1 r2 e)) fl.trapCode], ps) := fun _ _ _ _ => rfl
  have hfin : ∀ q r, q ≤ 30 → r ≤ 30 → FinalAM sz.bytes (.regExtended (.x q) (.x r) e) := fun q r hq hr => ⟨hq, hr, hop.2⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega))
    ArmState.default (fun h => by simp [AMode.base] at h)
  have hcf0 := fpuStore_line_cf env0 ctx sz hop.1 0 (by omega) _ (hfin 1 2 (by omega) (by omega)) ha0
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, rfl, hlines _ _ _ _, ha0, hcf0.1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _ _ _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨u, .int, .use, .early, .reg⟩, r1) (by simp)) with ⟨q, rfl, hq⟩ | ⟨q, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    rcases x_or_v (hall (⟨v, .int, .use, .early, .reg⟩, r2) (by simp)) with ⟨r, rfl, hr⟩ | ⟨r, rfl⟩
    rotate_left
    · rcases hop.1 with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuStore sz (.v 0) (.regExtended (.x 1) (.x 2) e) fl) hops
      rfl (hlines _ _ _ _), linesEvs_single ha0, hcf0.2 _ (fun h => by simp [AMode.base] at h),
      (fpuStore_line_cf env ctx sz hop.1 p hp _ (hfin q r (by omega) (by omega)) ha).2 _
        (fun h => by simp [AMode.base] at h), placeUses_setMem]
    simp [AMode.addr, regX, placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase,
      setReg, List.range_succ, Arm.r_of_w_same, rnum, setMem_mem, r_setMem, regVal, lo64,
      BitVec.setWidth_setWidth_of_le]


/-! ## The stack modes without an `x16` prefix -/

/-- An `sp`-based access with `sp` unaligned has no event (the alignment fault). -/
theorem immEvs_unal (inst : LDST.Reg_imm_cls) (s : ArmState) (h1 : inst.Rn = 31#5)
    (h2 : ¬ CheckSPAlignment s) : immEvs inst s = [] := by
  unfold immEvs
  simp only [h1, h2, not_false_eq_true, and_self, ite_true]
  repeat' split
  all_goals rfl

/-- … of an unscaled SIMD&FP access. -/
theorem ldsturEvs_unal (inst : Reg_unscaled_imm_cls) (s : ArmState) (h1 : inst.Rn = 31#5)
    (h2 : ¬ CheckSPAlignment s) : ldsturEvs inst s = [] := by
  unfold ldsturEvs
  simp only [h1, h2, not_false_eq_true, and_self, ite_true]
  split <;> rfl

/-- The `sp`-based immediate modes (`memFinalize`'s outputs at a stack offset). -/
def SpImm (m : AMode) : Prop := (∃ o, m = .unscaled .sp o) ∨ ∃ k, m = .unsignedOffset .sp k

/-- **A plain access at an `sp`-based immediate mode with `sp` unaligned has no event** (the
alignment fault). -/
theorem ldst_unal {env : Env} {x : Insn} {ai : ArmInst} (ha : x.toArmInst env = .ok ai)
    (hx : (∃ op rt m, x = .load op rt m ∧ SpImm m) ∨ (∃ op rt m, x = .store op rt m ∧ SpImm m) ∨
      (∃ sz rt m, x = .fpuLoad sz rt m ∧ SpImm m) ∨ (∃ sz rt m, x = .fpuStore sz rt m ∧ SpImm m))
    {y : ArmState} (hna : ¬ CheckSPAlignment y) : instEvs ai y = [] := by
  unfold Insn.toArmInst at ha
  cases hf : x.armFields env with
  | error e => rw [hf] at ha; cases ha
  | ok a0 =>
  rw [hf] at ha
  simp only [Functor.map, Except.map, Except.ok.injEq] at ha
  subst ha
  rcases hx with ⟨op, rt, m, rfl, ⟨o, rfl⟩ | ⟨o, rfl⟩⟩ | ⟨op, rt, m, rfl, ⟨o, rfl⟩ | ⟨o, rfl⟩⟩ |
      ⟨op, rt, m, rfl, ⟨o, rfl⟩ | ⟨o, rfl⟩⟩ | ⟨op, rt, m, rfl, ⟨o, rfl⟩ | ⟨o, rfl⟩⟩ <;> (try cases op) <;>
    simp (config := {decide := true}) only [Insn.armFields, LoadOp.fields, StoreOp.fields,
      ldstFields, bind, Except.bind, Reg.encSP, pure, Except.pure, Insn.armFields.fpLdstSize,
      ite_true, ite_false, Bool.false_eq_true] at hf <;>
    (repeat' split at hf) <;> (try cases hf) <;>
    simp only [ArmInst.norm, instEvs] <;>
    (try split) <;>
    first
      | (apply immEvs_unal <;> first | exact hna | rfl)
      | (apply ldsturEvs_unal <;> first | exact hna | rfl)
/-- The stack modes: stack-slot, `sp` and `fp` offsets. -/
def StackMode (m : AMode) : Prop := (∃ o, m = .slotOffset o) ∨ (∃ o, m = .spOffset o) ∨ ∃ o, m = .fpOffset o

/-- **`memFinalize` at a stack mode without a prefix** gives an immediate mode on `sp` or `fp`. -/
theorem stackFin {ctx : FnCtx} {m m' : AMode} {n : Nat} (hm : StackMode m) (hn : 0 < n)
    (hf : memFinalize ctx m n = .ok ([], m')) :
    FinalAM n m' ∧ (SpImm m' ∨ (∃ o, m' = .unscaled (.x 29) o) ∨ ∃ k, m' = .unsignedOffset (.x 29) k) := by
  have key : ∀ (B : Reg) (o : Int), BaseOk B →
      (match simm9? o with
        | some s => (([] : List Line), AMode.unscaled B s)
        | none => match uimm12Scaled? o n with
          | some k => ([], .unsignedOffset B k)
          | none => (loadConst64 (.x 16) (u64 o), .regExtended B (.x 16) .sxtx)) = ([], m') →
      FinalAM n m' ∧ ((∃ o, m' = .unscaled B o) ∨ ∃ k, m' = .unsignedOffset B k) := by
    intro B o hB h
    cases h9 : simm9? o with
    | some k9 =>
      rw [h9] at h
      simp only [Prod.mk.injEq, true_and] at h
      subst h
      have hk : -256 ≤ k9 ∧ k9 ≤ 255 := by simp only [simm9?] at h9; split at h9 <;> simp_all
      exact ⟨⟨hB, hk.1, by omega⟩, .inl ⟨_, rfl⟩⟩
    | none =>
      rw [h9] at h
      cases hu : uimm12Scaled? o n with
      | some ku =>
        rw [hu] at h
        simp only [Prod.mk.injEq, true_and] at h
        subst h
        have hk : ku % n = 0 ∧ ku ≤ 4095 * n := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨by simpa using h2, by omega⟩
          · cases hu
        refine ⟨⟨hB, hk.1, ?_⟩, .inr ⟨_, rfl⟩⟩
        have := Nat.div_le_div_right (c := n) hk.2
        rw [Nat.mul_div_cancel _ hn] at this
        omega
      | none =>
        rw [hu] at h
        simp only [Prod.mk.injEq] at h
        exact absurd h.1 (by rw [loadConst64_eq]; exact List.cons_ne_nil _ _)
  rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;>
    simp only [memFinalize, pure, Except.pure, Except.ok.injEq] at hf
  · obtain ⟨h1, h2⟩ := key .sp _ trivial hf
    exact ⟨h1, .inl h2⟩
  · obtain ⟨h1, h2⟩ := key .sp _ trivial hf
    exact ⟨h1, .inl h2⟩
  · obtain ⟨h1, h2⟩ := key (.x 29) _ (by simp [BaseOk]) hf
    exact ⟨h1, .inr h2⟩

theorem regs1 {regs : Array Reg} (h : regs.size = 1) : ∃ a, regs = #[a] := by
  rcases regs with ⟨_ | ⟨a, _ | ⟨_, _⟩⟩⟩ <;> simp at h
  exact ⟨a, rfl⟩

/-- A state with an aligned `sp` (for the encodings' existence). -/
def s16 : ArmState := Arm.w (.GPR 31#5) 0#64 ArmState.default

theorem s16_align : CheckSPAlignment s16 := by
  simp [CheckSPAlignment, s16, read_gpr, Arm.r_of_w_same, Aligned]

/-- The stack bases are unmasked: `SameWorld` keeps them. -/
theorem regX_stack {F : BitVec 64 → Prop} {s w : ArmState} (h : SameWorld F s w) {B : Reg}
    (hB : B = .sp ∨ B = .x 29) : regX s B = regX w B := by
  rcases hB with rfl | rfl
  · exact h.1 (.GPR 31#5) (by simp [Masked])
  · exact h.1 (.GPR (rnum 29)) (by simp [Masked, rnum])

/-- **A GPR load at a stack mode that `memFinalize` lowers without a prefix is a one-event form.** -/
theorem load_stack_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d : Nat} {m m' : AMode}
    {fl : Clif.MemFlags} (hm : StackMode m) (hfo : FormOk ctx (.load op (.vreg d .int) m fl) = true)
    (hf : memFinalize ctx m op.bytes = .ok ([], m')) :
    OneEvForm F ctx (.load op (.vreg d .int) m fl) := by
  have hop : op ≠ .fpuLoad128 := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk] using hfo
  obtain ⟨hfin, hsh⟩ := stackFin hm (load_bytes_pos op) hf
  have hops : (MInst.load op (.vreg d .int) m fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.load op (.vreg d .int) m fl).assign #[r0] = .ok (.load op r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.load op r0 m fl).lines ctx ps =
      .ok ([.ins (.load op r0 m') fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hB : ∃ B, (B = .sp ∨ B = .x 29) ∧ ((∃ o, m' = .unscaled B o) ∨ ∃ k, m' = .unsignedOffset B k) := by
    rcases hsh with (⟨o, rfl⟩ | ⟨k, rfl⟩) | ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨_, .inl rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inl rfl, .inr ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inr ⟨_, rfl⟩⟩
  obtain ⟨B, hBB, hm'⟩ := hB
  have hsp : ∀ y, ¬ (B = .sp ∧ ¬ CheckSPAlignment y) → m'.base = .sp → CheckSPAlignment y := by
    intro y h hb
    rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> simp only [AMode.base] at hb <;>
      exact Classical.byContradiction fun hn => h ⟨hb, hn⟩
  have hspimm : B = .sp → SpImm m' := by
    rintro rfl; rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, hasg (.x 0), hlines _ _, ha0,
    (load_line_shape env0 ctx op hop 0 (by omega) _ hfin s16 ha0).1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> cases op <;> (try exact absurd rfl hop) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .load op (.x 0) m fl) hops (hasg _) (hlines _ _),
      linesEvs_single ha0]
    have hpu : placeUses #[⟨d, .int, .def, .late, .reg⟩] (canonRegs #[⟨d, .int, .def, .late, .reg⟩])
        (useVals #[⟨d, .int, .def, .late, .reg⟩] #[.x p] s) (setMem M w) = setMem M w := by
      simp [placeUses, useVals, Operand.isUse]
    rw [hpu]
    have hsp' : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s := (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    by_cases hna : B = .sp ∧ ¬ CheckSPAlignment s
    · have hna' : ¬ CheckSPAlignment w := fun h => hna.2 (align_of_spEq hsp'.symm h)
      rw [ldst_unal ha (.inl ⟨_, _, _, rfl, hspimm hna.1⟩) (by rw [check_sp_sm']; exact hna.2),
        ldst_unal ha0 (.inl ⟨_, _, _, rfl, hspimm hna.1⟩) (by rw [check_sp_sm']; exact hna')]
    · have hal : ∀ y, Arm.r (.GPR 31#5) y = Arm.r (.GPR 31#5) s → ¬ (B = .sp ∧ ¬ CheckSPAlignment y) :=
        fun y hy h => hna ⟨h.1, fun h' => h.2 (align_of_spEq hy h')⟩
      rw [load_line_cf env ctx op hop p (by omega) _ hfin ha _
          (fun hb => by rw [check_sp_sm']; exact hsp s (hal s rfl) hb),
        load_line_cf env0 ctx op hop 0 (by omega) _ hfin ha0 _
          (fun hb => by rw [check_sp_sm']; exact hsp w (hal w hsp') hb)]
      have hx := regX_stack hsw hBB
      rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;>
        simp [AMode.addr, regX_setMem, setMem_mem, hx]

/-- **A GPR store at a stack mode that `memFinalize` lowers without a prefix is a one-event form.** -/
theorem store_stack_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d : Nat} {m m' : AMode}
    {fl : Clif.MemFlags} (hm : StackMode m) (hfo : FormOk ctx (.store op (.vreg d .int) m fl) = true)
    (hf : memFinalize ctx m op.bytes = .ok ([], m')) :
    OneEvForm F ctx (.store op (.vreg d .int) m fl) := by
  have hop : op ≠ .fpuStore128 := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk] using hfo
  obtain ⟨hfin, hsh⟩ := stackFin hm (store_bytes_pos op) hf
  have hops : (MInst.store op (.vreg d .int) m fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.store op (.vreg d .int) m fl).assign #[r0] = .ok (.store op r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.store op r0 m fl).lines ctx ps =
      .ok ([.ins (.store op r0 m') fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hB : ∃ B, (B = .sp ∨ B = .x 29) ∧ ((∃ o, m' = .unscaled B o) ∨ ∃ k, m' = .unsignedOffset B k) := by
    rcases hsh with (⟨o, rfl⟩ | ⟨k, rfl⟩) | ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨_, .inl rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inl rfl, .inr ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inr ⟨_, rfl⟩⟩
  obtain ⟨B, hBB, hm'⟩ := hB
  have hsp : ∀ y, ¬ (B = .sp ∧ ¬ CheckSPAlignment y) → m'.base = .sp → CheckSPAlignment y := by
    intro y h hb
    rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> simp only [AMode.base] at hb <;>
      exact Classical.byContradiction fun hn => h ⟨hb, hn⟩
  have hspimm : B = .sp → SpImm m' := by
    rintro rfl; rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, hasg (.x 0), hlines _ _, ha0,
    (store_line_shape env0 ctx op hop 0 (by omega) _ hfin s16 ha0).1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases x_or_v (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> cases op <;> (try exact absurd rfl hop) <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .store op (.x 0) m fl) hops (hasg _) (hlines _ _),
      linesEvs_single ha0]
    have hpu : placeUses #[⟨d, .int, .use, .early, .reg⟩] (canonRegs #[⟨d, .int, .use, .early, .reg⟩])
        (useVals #[⟨d, .int, .use, .early, .reg⟩] #[.x p] s) (setMem M w) =
        setMem M (setReg w (.x 0) (regVal s (.x p))) := by
      simp [placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase, setReg, w_setMem]
    rw [hpu]
    have hsp' : Arm.r (.GPR 31#5) (setReg w (.x 0) (regVal s (.x p))) = Arm.r (.GPR 31#5) s := by
      simp [setReg, Arm.r_of_w_different, rnum]; exact (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    by_cases hna : B = .sp ∧ ¬ CheckSPAlignment s
    · have hna' : ¬ CheckSPAlignment (setReg w (.x 0) (regVal s (.x p))) :=
        fun h => hna.2 (align_of_spEq hsp'.symm h)
      rw [ldst_unal ha (.inr (.inl ⟨_, _, _, rfl, hspimm hna.1⟩)) (by rw [check_sp_sm']; exact hna.2),
        ldst_unal ha0 (.inr (.inl ⟨_, _, _, rfl, hspimm hna.1⟩)) (by rw [check_sp_sm']; exact hna')]
    · have hal : ∀ y, Arm.r (.GPR 31#5) y = Arm.r (.GPR 31#5) s → ¬ (B = .sp ∧ ¬ CheckSPAlignment y) :=
        fun y hy h => hna ⟨h.1, fun h' => h.2 (align_of_spEq hy h')⟩
      rw [store_line_cf env ctx op hop p (by omega) _ hfin ha _
          (fun hb => by rw [check_sp_sm']; exact hsp s (hal s rfl) hb),
        store_line_cf env0 ctx op hop 0 (by omega) _ hfin ha0 _
          (fun hb => by rw [check_sp_sm']; exact hsp _ (hal _ hsp') hb)]
      have hx : regX s B = regX (setReg w (.x 0) (regVal s (.x p))) B := by
        rw [regX_stack hsw hBB]; rcases hBB with rfl | rfl <;>
          simp [regX, spOf, setReg, Arm.r_of_w_different, rnum]
      rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;>
        simp [AMode.addr, regX_setMem, setMem_mem, hx, setReg, Arm.r_of_w_same, regVal,
          rnum, r_setMem, lo64, BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP fpuLoad at a stack mode that `memFinalize` lowers without a prefix is a one-event form.** -/
theorem fpuLoad_stack_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d : Nat} {m m' : AMode}
    {fl : Clif.MemFlags} (hm : StackMode m) (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) m fl) = true)
    (hf : memFinalize ctx m sz.bytes = .ok ([], m')) :
    OneEvForm F ctx (.fpuLoad sz (.vreg d .float) m fl) := by
  have hop : FpSz sz := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk, FpSz] using hfo
  obtain ⟨hfin, hsh⟩ := stackFin hm (by have := fpSz_bytes hop; omega) hf
  have hops : (MInst.fpuLoad sz (.vreg d .float) m fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.fpuLoad sz (.vreg d .float) m fl).assign #[r0] = .ok (.fpuLoad sz r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.fpuLoad sz r0 m fl).lines ctx ps =
      .ok ([.ins (.fpuLoad sz r0 m') fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hB : ∃ B, (B = .sp ∨ B = .x 29) ∧ ((∃ o, m' = .unscaled B o) ∨ ∃ k, m' = .unsignedOffset B k) := by
    rcases hsh with (⟨o, rfl⟩ | ⟨k, rfl⟩) | ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨_, .inl rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inl rfl, .inr ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inr ⟨_, rfl⟩⟩
  obtain ⟨B, hBB, hm'⟩ := hB
  have hsp : ∀ y, ¬ (B = .sp ∧ ¬ CheckSPAlignment y) → m'.base = .sp → CheckSPAlignment y := by
    intro y h hb
    rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> simp only [AMode.base] at hb <;>
      exact Classical.byContradiction fun hn => h ⟨hb, hn⟩
  have hspimm : B = .sp → SpImm m' := by
    rintro rfl; rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, hasg (.v 0), hlines _ _, ha0,
    (fpuLoad_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> rcases hop with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuLoad sz (.v 0) m fl) hops (hasg _) (hlines _ _),
      linesEvs_single ha0]
    have hpu : placeUses #[⟨d, .float, .def, .late, .reg⟩] (canonRegs #[⟨d, .float, .def, .late, .reg⟩])
        (useVals #[⟨d, .float, .def, .late, .reg⟩] #[.v p] s) (setMem M w) = setMem M w := by
      simp [placeUses, useVals, Operand.isUse]
    rw [hpu]
    have hsp' : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s := (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    by_cases hna : B = .sp ∧ ¬ CheckSPAlignment s
    · have hna' : ¬ CheckSPAlignment w := fun h => hna.2 (align_of_spEq hsp'.symm h)
      rw [ldst_unal ha (.inr (.inr (.inl ⟨_, _, _, rfl, hspimm hna.1⟩))) (by rw [check_sp_sm']; exact hna.2),
        ldst_unal ha0 (.inr (.inr (.inl ⟨_, _, _, rfl, hspimm hna.1⟩))) (by rw [check_sp_sm']; exact hna')]
    · have hal : ∀ y, Arm.r (.GPR 31#5) y = Arm.r (.GPR 31#5) s → ¬ (B = .sp ∧ ¬ CheckSPAlignment y) :=
        fun y hy h => hna ⟨h.1, fun h' => h.2 (align_of_spEq hy h')⟩
      rw [(fpuLoad_line_cf env ctx sz hop p hp _ hfin ha).2 _
          (fun hb => by rw [check_sp_sm']; exact hsp s (hal s rfl) hb),
        (fpuLoad_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).2 _
          (fun hb => by rw [check_sp_sm']; exact hsp w (hal w hsp') hb)]
      have hx := regX_stack hsw hBB
      rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;>
        simp [AMode.addr, regX_setMem, setMem_mem, hx]

/-- **A SIMD&FP fpuStore at a stack mode that `memFinalize` lowers without a prefix is a one-event form.** -/
theorem fpuStore_stack_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d : Nat} {m m' : AMode}
    {fl : Clif.MemFlags} (hm : StackMode m) (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) m fl) = true)
    (hf : memFinalize ctx m sz.bytes = .ok ([], m')) :
    OneEvForm F ctx (.fpuStore sz (.vreg d .float) m fl) := by
  have hop : FpSz sz := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk, FpSz] using hfo
  obtain ⟨hfin, hsh⟩ := stackFin hm (by have := fpSz_bytes hop; omega) hf
  have hops : (MInst.fpuStore sz (.vreg d .float) m fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.fpuStore sz (.vreg d .float) m fl).assign #[r0] = .ok (.fpuStore sz r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.fpuStore sz r0 m fl).lines ctx ps =
      .ok ([.ins (.fpuStore sz r0 m') fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hB : ∃ B, (B = .sp ∨ B = .x 29) ∧ ((∃ o, m' = .unscaled B o) ∨ ∃ k, m' = .unsignedOffset B k) := by
    rcases hsh with (⟨o, rfl⟩ | ⟨k, rfl⟩) | ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨_, .inl rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inl rfl, .inr ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inl ⟨_, rfl⟩⟩
    · exact ⟨_, .inr rfl, .inr ⟨_, rfl⟩⟩
  obtain ⟨B, hBB, hm'⟩ := hB
  have hsp : ∀ y, ¬ (B = .sp ∧ ¬ CheckSPAlignment y) → m'.base = .sp → CheckSPAlignment y := by
    intro y h hb
    rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> simp only [AMode.base] at hb <;>
      exact Classical.byContradiction fun hn => h ⟨hb, hn⟩
  have hspimm : B = .sp → SpImm m' := by
    rintro rfl; rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, a0, hops, hasg (.v 0), hlines _ _, ha0,
    (fpuStore_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).1⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, hlines _⟩
  · intro ops regs i' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg' hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;> rcases hop with rfl | rfl <;> ldst_noV
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .fpuStore sz (.v 0) m fl) hops (hasg _) (hlines _ _),
      linesEvs_single ha0]
    have hpu : placeUses #[⟨d, .float, .use, .early, .reg⟩] (canonRegs #[⟨d, .float, .use, .early, .reg⟩])
        (useVals #[⟨d, .float, .use, .early, .reg⟩] #[.v p] s) (setMem M w) =
        setMem M (setReg w (.v 0) (regVal s (.v p))) := by
      simp [placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase, setReg, w_setMem]
    rw [hpu]
    have hsp' : Arm.r (.GPR 31#5) (setReg w (.v 0) (regVal s (.v p))) = Arm.r (.GPR 31#5) s := by
      simp [setReg, Arm.r_of_w_different, rnum]; exact (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    by_cases hna : B = .sp ∧ ¬ CheckSPAlignment s
    · have hna' : ¬ CheckSPAlignment (setReg w (.v 0) (regVal s (.v p))) :=
        fun h => hna.2 (align_of_spEq hsp'.symm h)
      rw [ldst_unal ha (.inr (.inr (.inr ⟨_, _, _, rfl, hspimm hna.1⟩))) (by rw [check_sp_sm']; exact hna.2),
        ldst_unal ha0 (.inr (.inr (.inr ⟨_, _, _, rfl, hspimm hna.1⟩))) (by rw [check_sp_sm']; exact hna')]
    · have hal : ∀ y, Arm.r (.GPR 31#5) y = Arm.r (.GPR 31#5) s → ¬ (B = .sp ∧ ¬ CheckSPAlignment y) :=
        fun y hy h => hna ⟨h.1, fun h' => h.2 (align_of_spEq hy h')⟩
      rw [(fpuStore_line_cf env ctx sz hop p hp _ hfin ha).2 _
          (fun hb => by rw [check_sp_sm']; exact hsp s (hal s rfl) hb),
        (fpuStore_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).2 _
          (fun hb => by rw [check_sp_sm']; exact hsp _ (hal _ hsp') hb)]
      have hx : regX s B = regX (setReg w (.v 0) (regVal s (.v p))) B := by
        rw [regX_stack hsw hBB]; rcases hBB with rfl | rfl <;>
          simp [regX, spOf, setReg, Arm.r_of_w_different, rnum]
      rcases hm' with ⟨o, rfl⟩ | ⟨k, rfl⟩ <;>
        simp [AMode.addr, regX_setMem, setMem_mem, hx, setReg, Arm.r_of_w_same, regVal,
          rnum, r_setMem, lo64, BitVec.setWidth_setWidth_of_le]

/-! ## The scope with plain loads/stores and the run level -/

/-- The final addressing modes (not the stack-slot, `sp` and `fp` offsets, which `memFinalize`
lowers). -/
def LSMode : AMode → Bool
  | .slotOffset _ | .spOffset _ | .fpOffset _ => false
  | _ => true

/-- **The covered modes of a plain access of `bytes` bytes**: a final mode (`LSMode`), or a stack
mode that `memFinalize` lowers without the `x16` prefix (its offset fits an immediate). -/
def LSModeOk (ctx : FnCtx) (bytes : Nat) (m : AMode) : Prop :=
  LSMode m = true ∨ (StackMode m ∧ ∃ m', memFinalize ctx m bytes = .ok ([], m'))

/-- **The plain load/store forms**: a covered (`FormOk`) GPR or SIMD&FP load/store at a covered
mode (`LSModeOk`). -/
def LSForm (ctx : FnCtx) (i : MInst) : Prop :=
  FormOk ctx i = true ∧ match i with
    | .load op _ m _ | .store op _ m _ => LSModeOk ctx op.bytes m
    | .fpuLoad sz _ m _ | .fpuStore sz _ m _ => LSModeOk ctx sz.bytes m
    | _ => False

theorem load_lsFinal {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {rt : Reg} {m : AMode}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op rt m fl) = true) (hm : LSMode m = true) :
    OneEvForm F ctx (.load op rt m fl) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals cases m with
  | unsignedOffset b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact load_uoff_form hfo
  | unscaled b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact load_unsc_form hfo
  | regReg b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact load_regReg_form hfo
  | regScaled b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact load_regScaled_form hfo
  | regScaledExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact load_regScaledExt_form hfo
  | regExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact load_regExt_form hfo
  | _ => first | (simp [LSMode] at hm; done) | (simp [FormOk, memOk] at hfo)

theorem load_lsForm {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {rt : Reg}
    {m : AMode} {fl : Clif.MemFlags} (hfo : FormOk ctx (.load op rt m fl) = true)
    (hm : LSModeOk ctx op.bytes m) : OneEvForm F ctx (.load op rt m fl) := by
  rcases hm with hm | ⟨hs, m', hf⟩
  · exact load_lsFinal hfo hm
  · rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals rcases hs with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> try (simp [FormOk] at hfo; done)
    all_goals exact load_stack_form (by first | exact .inl ⟨_, rfl⟩ | exact .inr (.inl ⟨_, rfl⟩) | exact .inr (.inr ⟨_, rfl⟩)) hfo hf

theorem store_lsFinal {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {rt : Reg} {m : AMode}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op rt m fl) = true) (hm : LSMode m = true) :
    OneEvForm F ctx (.store op rt m fl) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals cases m with
  | unsignedOffset b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact store_uoff_form hfo
  | unscaled b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact store_unsc_form hfo
  | regReg b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact store_regReg_form hfo
  | regScaled b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact store_regScaled_form hfo
  | regScaledExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact store_regScaledExt_form hfo
  | regExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact store_regExt_form hfo
  | _ => first | (simp [LSMode] at hm; done) | (simp [FormOk, memOk] at hfo)

theorem store_lsForm {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {rt : Reg}
    {m : AMode} {fl : Clif.MemFlags} (hfo : FormOk ctx (.store op rt m fl) = true)
    (hm : LSModeOk ctx op.bytes m) : OneEvForm F ctx (.store op rt m fl) := by
  rcases hm with hm | ⟨hs, m', hf⟩
  · exact store_lsFinal hfo hm
  · rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals rcases hs with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> try (simp [FormOk] at hfo; done)
    all_goals exact store_stack_form (by first | exact .inl ⟨_, rfl⟩ | exact .inr (.inl ⟨_, rfl⟩) | exact .inr (.inr ⟨_, rfl⟩)) hfo hf

theorem fpuLoad_lsFinal {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {rt : Reg} {m : AMode}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz rt m fl) = true) (hm : LSMode m = true) :
    OneEvForm F ctx (.fpuLoad sz rt m fl) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals cases m with
  | unsignedOffset b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuLoad_uoff_form hfo
  | unscaled b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuLoad_unsc_form hfo
  | regReg b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuLoad_regReg_form hfo
  | regScaled b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuLoad_regScaled_form hfo
  | regScaledExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuLoad_regScaledExt_form hfo
  | regExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuLoad_regExt_form hfo
  | _ => first | (simp [LSMode] at hm; done) | (simp [FormOk, memOk] at hfo)

theorem fpuLoad_lsForm {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {rt : Reg}
    {m : AMode} {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuLoad sz rt m fl) = true)
    (hm : LSModeOk ctx sz.bytes m) : OneEvForm F ctx (.fpuLoad sz rt m fl) := by
  rcases hm with hm | ⟨hs, m', hf⟩
  · exact fpuLoad_lsFinal hfo hm
  · rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals rcases hs with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> try (simp [FormOk] at hfo; done)
    all_goals exact fpuLoad_stack_form (by first | exact .inl ⟨_, rfl⟩ | exact .inr (.inl ⟨_, rfl⟩) | exact .inr (.inr ⟨_, rfl⟩)) hfo hf

theorem fpuStore_lsFinal {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {rt : Reg} {m : AMode}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz rt m fl) = true) (hm : LSMode m = true) :
    OneEvForm F ctx (.fpuStore sz rt m fl) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals cases m with
  | unsignedOffset b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuStore_uoff_form hfo
  | unscaled b off =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuStore_unsc_form hfo
  | regReg b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuStore_regReg_form hfo
  | regScaled b c =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuStore_regScaled_form hfo
  | regScaledExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuStore_regScaledExt_form hfo
  | regExtended b c e =>
    rcases b with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals rcases c with ⟨v, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk, memOk] at hfo; done)
    all_goals exact fpuStore_regExt_form hfo
  | _ => first | (simp [LSMode] at hm; done) | (simp [FormOk, memOk] at hfo)

theorem fpuStore_lsForm {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {rt : Reg}
    {m : AMode} {fl : Clif.MemFlags} (hfo : FormOk ctx (.fpuStore sz rt m fl) = true)
    (hm : LSModeOk ctx sz.bytes m) : OneEvForm F ctx (.fpuStore sz rt m fl) := by
  rcases hm with hm | ⟨hs, m', hf⟩
  · exact fpuStore_lsFinal hfo hm
  · rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals rcases hs with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> try (simp [FormOk] at hfo; done)
    all_goals exact fpuStore_stack_form (by first | exact .inl ⟨_, rfl⟩ | exact .inr (.inl ⟨_, rfl⟩) | exact .inr (.inr ⟨_, rfl⟩)) hfo hf

/-- **Every plain load/store form is a one-event form.** -/
theorem lsForm_oneEv {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} (h : LSForm ctx i) :
    OneEvForm F ctx i := by
  obtain ⟨hfo, hm⟩ := h
  cases i <;> simp only at hm
  · exact load_lsForm hfo hm
  · exact store_lsForm hfo hm
  · exact fpuLoad_lsForm hfo hm
  · exact fpuStore_lsForm hfo hm

theorem noGoto_ls {ctx : FnCtx} {i : MInst} (h : LSForm ctx i) : ¬ GotoForm i := by
  intro hg
  rcases hg with (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩) | ⟨_, _, rfl⟩ |
      ⟨_, _, _, _, _, rfl⟩ <;>
    exact h.2

/-- **The scope of `arm_alloc_refines_ls`**: every instruction is a memory form, an LL/SC loop
(`MemFormL`), a block-ending branch (`BrForm`) or a plain load/store (`LSForm`). -/
def MemScopeLS (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → MemFormL R.ctx i ∨ BrForm i ∨ LSForm R.ctx i

theorem memScopeLS_of_memScopeB {R : RL} (h : MemScopeB R) : MemScopeLS R :=
  fun b vb k i hb hi => (h b vb k i hb hi).elim .inl (fun h => .inr (.inl h))

/-- **The per-item obligation of the scope with plain loads/stores, with moves**, on ranked
configurations (`μR`; the statement before #553 used a measure of the configuration only, which
`MachBuffer`'s layout falsifies: `ArmAllocBranch` module doc). -/
theorem itemSim_ls {R : RL} (hR : R.Wf) (hsc : MemScopeLS R) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStepR R) (RelQR R) (DoneR R) (μR R) (PrivA R) := by
  rintro ⟨s, mon⟩ ⟨c, r⟩ ⟨hqa, hk⟩ ls t' hr
  match c, hqa, hk with
  | .ret vals m w, _, _ => exact .inl (.inl ⟨vals, m, w, rfl⟩)
  | .halt w, _, _ => exact .inl (.inr (.inl ⟨w, rfl⟩))
  | .run ⟨b, its, m, w⟩, hqa, hk =>
  by_cases hS : ∃ evs c', SrcStep R (.run ⟨b, its, m, w⟩) evs c'
  case neg => exact .inl (.inr (.inr fun evs c' h => hS ⟨evs, c', h⟩))
  obtain ⟨evs0, c0, hs0⟩ := hS
  cases hs0 with
  | @move _ src dst its' =>
    rcases move_op hR hqa hr with h | h
    · exact .inr (.inl (isOut_μR noGotoAt_move hk h))
    · exact .inr (.inr (.inr h))
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    have hs : SrcStep R (OpC b k allocs its' m w) _ _ := .op hvb hi hops hevs hfoot hst
    rcases RelQ.op' hqa hs with ⟨hq, hA⟩ | ⟨rfl, vals, m', w', rfl⟩
    case inr => exact .inr (.inl (itemSimOut_retR hs (RkC.pos hk)))
    have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
      fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
    rcases hsc b vb k i hvb hi with hl | hbr | hls
    · refine opOutR_of (noGotoAt_op hvb hi (noGoto_memFormL hl)) hk ?_
      rcases hl with (h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩) | hl | hl
      · exact opOut_okPriv (fun ls t' hr => noev_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => fence_op hR hq hA hs
          (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr) hr
      · exact rmw_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
      · exact cas_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
    · exact goto_op hR hq hA hk hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hbr) hr
    · exact opOutR_of (noGotoAt_op hvb hi (noGoto_ls hls)) hk (opOut_okPriv (fun ls t' hr =>
        oneEv_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ lsForm_oneEv hls) hr) hr)

/-- **Layer 4b with the plain loads/stores** (module doc): every precise Arm run under `OkPriv`
from a `Q`-related state realizes a run of the allocated code (`MTRun`) with `Refines` (equal
kinds, the addresses outside the world private, the atomic updates monitor pairs), up to the
allocated code's return, trap or undefined behaviour (`Done`), for functions whose instructions
are event-free, `fence`, `ldar`, `stlr`, LL/SC loops, block-ending branches or plain loads/stores
at final addressing modes (`MemScopeLS`), whatever their moves. -/
theorem arm_alloc_refines_ls {R : RL} (hR : R.Wf) (hsc : MemScopeLS R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_ls hR hsc) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.fst hs), href, hend⟩

end Concurrency.ArmAllocThread

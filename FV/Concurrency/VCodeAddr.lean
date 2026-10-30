import FV.Concurrency.VCodeEvents
import FV.Backend.Proof.RegallocMemFP

/-!
# The addresses of the memory events of VCode (T2h, #311, layer 2a)

`VCodeThread.cEvs` gives the memory events of a VCode instruction under `csem` (the events of its
canonical run). This file shows **every event lies within the instruction's accesses**
(`MInst.accesses`, the byte ranges `csem`'s frame check `AccessOk` constrains), so a successful
`csem F` step's events avoid the frame set `F` (`docs/plans/atomics.md` §3e, finding 3):

* `linesEvs_steps`: a prefix of lines without memory kinds (`memFinalize`'s offset load
  `loadConst64`) has no events;
* `load_line_evs`/`store_line_evs`: the one event of an emitted single-register load/store is
  at the addressing mode's address (`AMode.addr`) with the access size;
* `load_lines_evs`/`store_lines_evs`: the same for an allocated load/store's lines (stack-slot,
  `sp` and `fp` offsets of any size, through `x16`).
-/

namespace Concurrency.VCodeAddr

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeEvents Code
open scoped List

/-! ## Lines without memory kinds -/

/-- The events of one line are its instruction's events. -/
theorem linesEvs_single {env : Env} {i : Insn} {t : Option Clif.TrapCode} {ai : ArmInst}
    (ha : i.toArmInst env = .ok ai) (s : ArmState) :
    linesEvs env [.ins i t] s = instEvs ai s := by
  simp only [linesEvs, ha]
  split <;> simp

/-- **A prefix without memory kinds has no events**: the events of `A ++ B` are those of `B`
from the prefix's end state. -/
theorem linesEvs_steps : ∀ {env : Env} {A : List Line} (B : List Line) {s s1 : ArmState},
    StepsOk env A s s1 → kinds A = [] →
    linesEvs env (A ++ B) s = linesEvs { env with pc := env.pc + 4 * A.length } B s1
  | env, [], B, s, s1, h, _ => by
    simp only [StepsOk] at h; subst h
    simp
  | env, .ins i t :: A, B, s, s1, h, hk => by
    obtain ⟨ai, ha, hpc, -, -, h⟩ := h
    have hk1 : insnKind i = none := by
      simp only [kinds, List.filterMap_cons, lineKind] at hk
      split at hk
      · assumption
      · cases hk
    have hkA : kinds A = [] := by
      simp only [kinds, List.filterMap_cons, lineKind, hk1] at hk
      exact hk
    have ih := linesEvs_steps (env := { env with pc := env.pc + 4 }) B h hkA
    simp only [List.cons_append, linesEvs, ha, hpc, ite_true, instEvs_none ha hk1, List.nil_append]
    rw [ih]
    simp only [List.length_cons]
    congr 1
    cases env; simp; omega
  | _, .label _ :: _, _, _, _, h, _ => h.elim
  | _, .word _ _ :: _, _, _, _, h, _ => h.elim

/-! ## Single-register loads and stores (GPR) -/

/-- The event property: kind `k`, address `a`, size `n`. -/
def At (k : AKind) (a : BitVec 64) (n : Nat) (evs : List Ev) : Prop :=
  ∀ e ∈ evs, e.k = k ∧ e.addr = a ∧ e.n = n

theorem immEvs_load (op : LoadOp) (hop : op ≠ .fpuLoad128) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    At .plainR (read_gpr 64 Rn s + imm.value (log2 op.bytes) s) op.bytes
      (immEvs (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) s) := by
  intro e he
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  cases op <;> simp at hop <;>
  · simp (config := {decide := true}) only [immEvs, gprCls, LoadOp.fields, LoadOp.bytes,
      Arm.LDST.reg_imm_constrain_unpredictable, h31, log2] at he ⊢
    simp (config := {decide := true}) at he
    subst he
    simp (config := {decide := true})

theorem immEvs_store (op : StoreOp) (hop : op ≠ .fpuStore128) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    At .plainW (read_gpr 64 Rn s + imm.value (log2 op.bytes) s) op.bytes
      (immEvs (gprCls op.fields.1 op.fields.2.2 Rn Rt imm) s) := by
  intro e he
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  cases op <;> simp at hop <;>
  · simp (config := {decide := true}) only [immEvs, gprCls, StoreOp.fields, StoreOp.bytes,
      Arm.LDST.reg_imm_constrain_unpredictable, h31, log2] at he ⊢
    simp (config := {decide := true}) at he
    subst he
    simp (config := {decide := true})

theorem At.addr_eq {k : AKind} {a a' : BitVec 64} {n : Nat} {evs : List Ev} (e : a = a')
    (h : At k a n evs) : At k a' n evs := e ▸ h

theorem instEvs_uimm (size opc : BitVec 2) (imm12 : BitVec 12) (Rn Rt : BitVec 5) (s : ArmState) :
    instEvs (uimmInst size opc imm12 Rn Rt) s = immEvs (gprCls size opc Rn Rt (.uimm12 imm12)) s := by
  simp (config := {decide := true}) [instEvs, uimmInst, gprCls]

theorem instEvs_unsc (size opc : BitVec 2) (imm9 : BitVec 9) (Rn Rt : BitVec 5) (s : ArmState) :
    instEvs (unscInst size opc imm9 Rn Rt) s = immEvs (gprCls size opc Rn Rt (.simm9 imm9)) s := by
  simp (config := {decide := true}) [instEvs, unscInst, gprCls]

theorem instEvs_reg (size opc : BitVec 2) (Rm : BitVec 5) (option : BitVec 3) (S : BitVec 1)
    (Rn Rt : BitVec 5) (ho : Arm.BitVec.lsb option 1 = 1#1) (s : ArmState) :
    instEvs (regInst size opc Rm option S Rn Rt) s =
      immEvs (gprCls size opc Rn Rt (.reg Rm option S)) s := by
  simp (config := {decide := true}) [instEvs, regInst, gprCls, ho]

theorem ext_lsb1 {ex : ExtendOp} (h : ex = .uxtw ∨ ex = .uxtx ∨ ex = .sxtw ∨ ex = .sxtx) :
    Arm.BitVec.lsb ex.bits 1 = 1#1 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- **The event of an emitted load** is at the addressing mode's address, of the access size. -/
theorem load_line_evs (env : Env) (ctx : FnCtx) (op : LoadOp) (hop : op ≠ .fpuLoad128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) (s : ArmState)
    (hsp : m.base = .sp → CheckSPAlignment s) {ai : ArmInst}
    (ha : Insn.toArmInst env (.load op (.x d) m) = .ok ai) :
    At .plainR (m.addr ctx op.bytes s) op.bytes (instEvs ai s) := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.load op (.x d) (.unsignedOffset rn off)) =
        .ok (uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, uField,
          Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_uimm]
    refine At.addr_eq ?_ (immEvs_load op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact uimm_value op.bytes (by cases op <;> simp_all [LoadOp.bytes]) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.load op (.x d) (.unscaled rn off)) =
        .ok (unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR, sField,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, unscInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_unsc]
    refine At.addr_eq ?_ (immEvs_load op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.load op (.x d) (.regReg rn rm)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_load op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
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
    have e : Insn.toArmInst env (.load op (.x d) (.regScaled rn rm)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_load op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
    exact uxtx_shift _ _ (by cases op <;> simp [log2, LoadOp.bytes])
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.load op (.x d) (.regScaledExtended rn rm ex)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_load op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.load op (.x d) (.regExtended rn rm ex)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_load op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    rfl
  | _ => simp [FinalAM] at hm

/-- **The event of an emitted store** is at the addressing mode's address, of the access size. -/
theorem store_line_evs (env : Env) (ctx : FnCtx) (op : StoreOp) (hop : op ≠ .fpuStore128) (d : Nat)
    (hd : d ≤ 30) (m : AMode) (hm : FinalAM op.bytes m) (s : ArmState)
    (hsp : m.base = .sp → CheckSPAlignment s) {ai : ArmInst}
    (ha : Insn.toArmInst env (.store op (.x d) m) = .ok ai) :
    At .plainW (m.addr ctx op.bytes s) op.bytes (instEvs ai s) := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.store op (.x d) (.unsignedOffset rn off)) =
        .ok (uimmInst op.fields.1 op.fields.2.2 (BitVec.ofNat 12 (off / op.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, uField,
          Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure, uimmInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_uimm]
    refine At.addr_eq ?_ (immEvs_store op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact uimm_value op.bytes (by cases op <;> simp_all [StoreOp.bytes]) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.store op (.x d) (.unscaled rn off)) =
        .ok (unscInst op.fields.1 op.fields.2.2 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR, sField,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, unscInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_unsc]
    refine At.addr_eq ?_ (immEvs_store op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.store op (.x d) (.regReg rn rm)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_store op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
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
    have e : Insn.toArmInst env (.store op (.x d) (.regScaled rn rm)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_store op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
    exact uxtx_shift _ _ (by cases op <;> simp [log2, StoreOp.bytes])
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.store op (.x d) (.regScaledExtended rn rm ex)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_store op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.store op (.x d) (.regExtended rn rm ex)) =
        .ok (regInst op.fields.1 op.fields.2.2 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> cases op <;> simp at hop <;>
        simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, Reg.encZR,
          Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure, regInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_reg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_store op hop Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    rfl
  | _ => simp [FinalAM] at hm


/-! ## Single-register loads and stores (SIMD&FP) -/

theorem immEvs_fpLoad (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    At .plainR (read_gpr 64 Rn s + imm.value (log2 sz.bytes) s) sz.bytes
      (immEvs (fpCls (fpSizeF sz) 1 Rn Rt imm) s) := by
  intro e he
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [immEvs, fpCls, fpSizeF, ScalarSize.bytes,
      Arm.LDST.supported_simd_reg_imm, Arm.LDST.reg_imm_constrain_unpredictable, h31, log2] at he ⊢
    simp (config := {decide := true}) at he
    subst he
    simp (config := {decide := true}) [lsb_facts]

theorem immEvs_fpStore (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5)
    (imm : Arm.LDST.Reg_offset) (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    At .plainW (read_gpr 64 Rn s + imm.value (log2 sz.bytes) s) sz.bytes
      (immEvs (fpCls (fpSizeF sz) 0 Rn Rt imm) s) := by
  intro e he
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [immEvs, fpCls, fpSizeF, ScalarSize.bytes,
      Arm.LDST.supported_simd_reg_imm, Arm.LDST.reg_imm_constrain_unpredictable, h31, log2] at he ⊢
    simp (config := {decide := true}) at he
    subst he
    simp (config := {decide := true})

theorem ldsturEvs_fpLoad (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5) (imm9 : BitVec 9)
    (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    At .plainR (read_gpr 64 Rn s + BitVec.signExtend 64 imm9) sz.bytes
      (ldsturEvs { size := fpSizeF sz, VR := 1#1, opc := 1#2, imm9 := imm9, Rn := Rn, Rt := Rt } s) := by
  intro e he
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [ldsturEvs, fpSizeF, ScalarSize.bytes, h31] at he ⊢
    simp (config := {decide := true}) at he
    subst he
    simp (config := {decide := true})

theorem ldsturEvs_fpStore (sz : ScalarSize) (hsz : FpSz sz) (Rn Rt : BitVec 5) (imm9 : BitVec 9)
    (s : ArmState) (hsp : Rn = 31#5 → CheckSPAlignment s) :
    At .plainW (read_gpr 64 Rn s + BitVec.signExtend 64 imm9) sz.bytes
      (ldsturEvs { size := fpSizeF sz, VR := 1#1, opc := 0#2, imm9 := imm9, Rn := Rn, Rt := Rt } s) := by
  intro e he
  have h31 : ¬ (Rn = 31#5 ∧ ¬ CheckSPAlignment s) := fun h => h.2 (hsp h.1)
  rcases hsz with rfl | rfl <;>
  · simp (config := {decide := true}) only [ldsturEvs, fpSizeF, ScalarSize.bytes, h31] at he ⊢
    simp (config := {decide := true}) at he
    subst he
    simp (config := {decide := true})

theorem instEvs_fpUimm (size opc : BitVec 2) (imm12 : BitVec 12) (Rn Rt : BitVec 5) (s : ArmState) :
    instEvs (fpUimmInst size opc imm12 Rn Rt) s = immEvs (fpCls size opc Rn Rt (.uimm12 imm12)) s := by
  simp (config := {decide := true}) [instEvs, fpUimmInst, fpCls]

theorem instEvs_fpUnsc (size opc : BitVec 2) (imm9 : BitVec 9) (Rn Rt : BitVec 5) (s : ArmState) :
    instEvs (fpUnscInst size opc imm9 Rn Rt) s =
      ldsturEvs { size := size, VR := 1#1, opc := opc, imm9 := imm9, Rn := Rn, Rt := Rt } s := by
  simp (config := {decide := true}) [instEvs, fpUnscInst]

theorem instEvs_fpReg (size opc : BitVec 2) (Rm : BitVec 5) (option : BitVec 3) (S : BitVec 1)
    (Rn Rt : BitVec 5) (ho : Arm.BitVec.lsb option 1 = 1#1) (s : ArmState) :
    instEvs (fpRegInst size opc Rm option S Rn Rt) s =
      immEvs (fpCls size opc Rn Rt (.reg Rm option S)) s := by
  simp (config := {decide := true}) [instEvs, fpRegInst, fpCls, ho]

/-- **The event of an emitted SIMD&FP load** is at the addressing mode's address, of the access size. -/
theorem fpuLoad_line_evs (env : Env) (ctx : FnCtx) (sz : ScalarSize) (hsz : FpSz sz) (d : Nat)
    (hd : d < 32) (m : AMode) (hm : FinalAM sz.bytes m) (s : ArmState)
    (hsp : m.base = .sp → CheckSPAlignment s) {ai : ArmInst}
    (ha : Insn.toArmInst env (.fpuLoad sz (.v d) m) = .ok ai) :
    At .plainR (m.addr ctx sz.bytes s) sz.bytes (instEvs ai s) := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.unsignedOffset rn off)) =
        .ok (fpUimmInst (fpSizeF sz) 1 (BitVec.ofNat 12 (off / sz.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpUimm]
    refine At.addr_eq ?_ (immEvs_fpLoad sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact uimm_value sz.bytes (by have := fpSz_bytes hsz; omega) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.unscaled rn off)) =
        .ok (fpUnscInst (fpSizeF sz) 1 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          sField, Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUnscInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpUnsc]
    refine At.addr_eq ?_ (ldsturEvs_fpLoad sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, hr]
    congr 1
    exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regReg rn rm)) =
        .ok (fpRegInst (fpSizeF sz) 1 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_fpLoad sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
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
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regScaled rn rm)) =
        .ok (fpRegInst (fpSizeF sz) 1 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_fpLoad sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
    exact uxtx_shift _ _ (fp_log2 hsz)
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regScaledExtended rn rm ex)) =
        .ok (fpRegInst (fpSizeF sz) 1 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_fpLoad sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.fpuLoad sz (.v d) (.regExtended rn rm ex)) =
        .ok (fpRegInst (fpSizeF sz) 1 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_fpLoad sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    rfl
  | _ => simp [FinalAM] at hm

/-- **The event of an emitted SIMD&FP store** is at the addressing mode's address, of the access size. -/
theorem fpuStore_line_evs (env : Env) (ctx : FnCtx) (sz : ScalarSize) (hsz : FpSz sz) (d : Nat)
    (hd : d < 32) (m : AMode) (hm : FinalAM sz.bytes m) (s : ArmState)
    (hsp : m.base = .sp → CheckSPAlignment s) {ai : ArmInst}
    (ha : Insn.toArmInst env (.fpuStore sz (.v d) m) = .ok ai) :
    At .plainW (m.addr ctx sz.bytes s) sz.bytes (instEvs ai s) := by
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.unsignedOffset rn off)) =
        .ok (fpUimmInst (fpSizeF sz) 0 (BitVec.ofNat 12 (off / sz.bytes)) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          uField, Arm.ArmInst.norm, ScalarSize.bytes, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUimmInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpUimm]
    refine At.addr_eq ?_ (immEvs_fpStore sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr]
    congr 1
    exact uimm_value sz.bytes (by have := fpSz_bytes hsz; omega) off h1 h2
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.unscaled rn off)) =
        .ok (fpUnscInst (fpSizeF sz) 0 (BitVec.ofInt 9 off) Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          sField, Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpUnscInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpUnsc]
    refine At.addr_eq ?_ (ldsturEvs_fpStore sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, hr]
    congr 1
    exact simm9_value off h1 h2
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regReg rn rm)) =
        .ok (fpRegInst (fpSizeF sz) 0 Rm 3#3 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_fpStore sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
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
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regScaled rn rm)) =
        .ok (fpRegInst (fpSizeF sz) 0 Rm 3#3 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (by decide)]
    refine At.addr_eq ?_ (immEvs_fpStore sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    congr 1
    rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl, ite_true]
    exact uxtx_shift _ _ (fp_log2 hsz)
  | regScaledExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regScaledExtended rn rm ex)) =
        .ok (fpRegInst (fpSizeF sz) 0 Rm ex.bits 1#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_fpStore sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm, ite_true]
  | regExtended rn rm ex =>
    obtain ⟨hb, hi, hex⟩ := hm
    obtain ⟨Rn, hRn, hr, h31⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have e : Insn.toArmInst env (.fpuStore sz (.v d) (.regExtended rn rm ex)) =
        .ok (fpRegInst (fpSizeF sz) 0 Rm ex.bits 0#1 Rn (BitVec.ofNat 5 d)) := by
      clear ha
      rcases hex with rfl | rfl | rfl | rfl <;> rcases hsz with rfl | rfl <;>
        simp_all [Insn.toArmInst, Insn.armFields, Insn.armFields.fpLdstSize, ldstFields, encV_v' hd,
          Arm.ArmInst.norm, fpSizeF, bind, Except.bind, pure, Except.pure,
          fpRegInst] <;> rfl
    rw [e] at ha; cases ha
    rw [instEvs_fpReg _ _ _ _ _ _ _ (ext_lsb1 hex)]
    refine At.addr_eq ?_ (immEvs_fpStore sz hsz Rn _ _ s (fun h => hsp (by simp [AMode.base, h31 h])))
    simp only [AMode.addr, Arm.LDST.Reg_offset.value, hr, hrm]
    rfl
  | _ => simp [FinalAM] at hm


theorem store_bytes_pos (op : StoreOp) : 0 < op.bytes := by cases op <;> decide

/-- `At` of a single line, from its instruction's events (an instruction that does not encode
has none). -/
theorem at_single {env : Env} {i : Insn} {tc : Option Clif.TrapCode} {k : AKind} {a : BitVec 64}
    {n : Nat} {s : ArmState} (h : ∀ ai, i.toArmInst env = .ok ai → At k a n (instEvs ai s)) :
    At k a n (linesEvs env [.ins i tc] s) := by
  cases ha : i.toArmInst env with
  | error _ => simp only [linesEvs, ha]; exact fun _ h => nomatch h
  | ok ai => rw [linesEvs_single ha]; exact h ai ha

/-- **The events of a memory instruction's lines** (`memFinalize`'s prefix, then the access
`mk m'` at the final addressing mode), when every encoding of `mk` at a final mode has its one
event at the mode's address: at most one event, at `m.addr` (stack-slot, `sp` and `fp` offsets
of any size, through `x16`). -/
theorem memFinalize_evs (ctx : FnCtx) (env : Env) {n : Nat} (hn : 0 < n) (mk : AMode → Insn)
    (tc : Option Clif.TrapCode) (k : AKind)
    (H : ∀ (env' : Env) (t : ArmState) (m' : AMode), FinalAM n m' →
      (m'.base = .sp → CheckSPAlignment t) → ∀ ai, (mk m').toArmInst env' = .ok ai →
      At k (m'.addr ctx n t) n (instEvs ai t))
    {m : AMode} (hm : MemMode n m) (s : ArmState) (halign : CheckSPAlignment s)
    {pre : List Line} {m' : AMode} (hf : memFinalize ctx m n = .ok (pre, m')) :
    At k (m.addr ctx n s) n (linesEvs env (pre ++ [.ins (mk m') tc]) s) := by
  have single : ∀ (env' : Env) (t : ArmState) (m'' : AMode), FinalAM n m'' →
      (m''.base = .sp → CheckSPAlignment t) → m''.addr ctx n t = m.addr ctx n s →
      At k (m.addr ctx n s) n (linesEvs env' [.ins (mk m'') tc] t) :=
    fun env' t m'' hf' hs ha => at_single fun ai hai => At.addr_eq ha (H env' t m'' hf' hs ai hai)
  have base : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      m.addr ctx n s = regX s B + BitVec.ofInt 64 o →
      memFinalize ctx m n = .ok (match simm9? o with
        | some s => (([] : List Line), AMode.unscaled B s)
        | none => match uimm12Scaled? o n with
          | some k => ([], .unsignedOffset B k)
          | none => (loadConst64 (.x 16) (u64 o), .regExtended B (.x 16) .sxtx)) →
      At k (m.addr ctx n s) n (linesEvs env (pre ++ [.ins (mk m') tc]) s) := by
    intro B o hB ha hfin
    rw [hf] at hfin
    have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
    cases h9 : simm9? o with
    | some k9 =>
      rw [h9] at hfin
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
      obtain ⟨rfl, rfl⟩ := hfin
      have hk : k9 = o ∧ -256 ≤ k9 ∧ k9 ≤ 255 := by
        simp only [simm9?] at h9; split at h9 <;> simp_all
      refine single env s (.unscaled B k9) ⟨hBok, hk.2.1, by omega⟩ (fun _ => halign) ?_
      rw [ha]; simp [AMode.addr, hk.1]
    | none =>
      rw [h9] at hfin
      cases hu : uimm12Scaled? o n with
      | some ku =>
        rw [hu] at hfin
        simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
        obtain ⟨rfl, rfl⟩ := hfin
        have hk : (ku : Int) = o ∧ ku % n = 0 ∧ ku ≤ 4095 * n := by
          simp only [uimm12Scaled?] at hu
          split at hu
          · rename_i hc
            simp only [Option.some.injEq] at hu
            subst hu
            obtain ⟨h0, h1, h2⟩ := hc
            exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
          · cases hu
        refine single env s (.unsignedOffset B ku) ⟨hBok, hk.2.1,
          by have := Nat.div_le_div_right (c := n) hk.2.2; rw [Nat.mul_div_cancel _ hn] at this; omega⟩
          (fun _ => halign) ?_
        rw [ha]
        simp only [AMode.addr]
        congr 1
        rw [← hk.1]; rfl
      | none =>
        rw [hu] at hfin
        simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
        obtain ⟨rfl, rfl⟩ := hfin
        have hA := steps_loadConst64 env (n := 16) (by omega) (u64 o) s
        let L := (loadConst64 (.x 16) (u64 o)).length
        let S1 := pcx s 16 (Arm.r .PC s + BitVec.ofNat 64 (4 * L)) (BitVec.ofNat 64 (u64 o))
        have hS1 : spOf S1 = spOf s ∧ Arm.r (.GPR 16#5) S1 = BitVec.ofNat 64 (u64 o) := by
          simp [S1, pcx, spOf, Arm.r_of_w_different, Arm.r_of_w_same]
        have hal1 : CheckSPAlignment S1 := by
          have e : Arm.r (.GPR 31#5) S1 = Arm.r (.GPR 31#5) s := hS1.1
          simpa [CheckSPAlignment, Arm.read_gpr, e] using halign
        have hBS : regX S1 B = regX s B := by
          rcases hB with rfl | rfl
          · exact hS1.1
          · simp [S1, pcx, regX, rnum, Arm.r_of_w_different]
        rw [linesEvs_steps _ hA (kinds_loadConst64 _ _)]
        refine single _ S1 (.regExtended B (.x 16) .sxtx) ⟨hBok, by simp [IdxOk], by simp⟩
          (fun _ => hal1) ?_
        rw [show AMode.addr ctx (.regExtended B (.x 16) .sxtx) n S1 = regX S1 B +
            Arm.extend_reg (regX S1 (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl]
        rw [hBS, ha, show regX S1 (.x 16) = BitVec.ofNat 64 (u64 o) from hS1.2,
          show ExtendOp.sxtx.bits = 7#3 from rfl, sxtx_id, ofNat_u64]
  cases m with
  | slotOffset off =>
    exact base .sp (off + ctx.slotBase) (.inl rfl) (by simp [AMode.addr, regX]) rfl
  | spOffset off => exact base .sp off (.inl rfl) (by simp [AMode.addr, regX]) rfl
  | fpOffset off => exact base (.x 29) off (.inr rfl) (by simp [AMode.addr, regX]) rfl
  | _ =>
    simp only [MemMode] at hm <;>
    · rw [memFinalize_final ctx _ hm] at hf
      simp only [Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact single env s _ hm (fun _ => halign) rfl

/-- **The events of an allocated load's lines**: at most one, at `AMode.addr`, of the access
size. -/
theorem load_lines_evs (ctx : FnCtx) (env : Env) (op : LoadOp) (hop : op ≠ .fpuLoad128) {d : Nat}
    (hd : d ≤ 30) {m : AMode} (fl : Clif.MemFlags) (hm : MemMode op.bytes m) (s : ArmState)
    (halign : CheckSPAlignment s) {ls : List Line} {ps : Backend.PState}
    (hl : MInst.lines ctx (.load op (.x d) m fl) {} = .ok (ls, ps)) :
    At .plainR (m.addr ctx op.bytes s) op.bytes (linesEvs env ls s) := by
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  · rename_i v hf
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    exact memFinalize_evs ctx env (load_bytes_pos op) (fun m' => .load op (.x d) m') _ .plainR
      (fun env' t m' hf' hs ai hai => load_line_evs env' ctx op hop d hd m' hf' t hs hai)
      hm s halign hf

/-- **The events of an allocated store's lines**: at most one, at `AMode.addr`, of the access
size. -/
theorem store_lines_evs (ctx : FnCtx) (env : Env) (op : StoreOp) (hop : op ≠ .fpuStore128) {d : Nat}
    (hd : d ≤ 30) {m : AMode} (fl : Clif.MemFlags) (hm : MemMode op.bytes m) (s : ArmState)
    (halign : CheckSPAlignment s) {ls : List Line} {ps : Backend.PState}
    (hl : MInst.lines ctx (.store op (.x d) m fl) {} = .ok (ls, ps)) :
    At .plainW (m.addr ctx op.bytes s) op.bytes (linesEvs env ls s) := by
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  · rename_i v hf
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    exact memFinalize_evs ctx env (store_bytes_pos op) (fun m' => .store op (.x d) m') _ .plainW
      (fun env' t m' hf' hs ai hai => store_line_evs env' ctx op hop d hd m' hf' t hs hai)
      hm s halign hf

/-- **The events of an allocated SIMD&FP load's lines**: at most one, at `AMode.addr`. -/
theorem fpuLoad_lines_evs (ctx : FnCtx) (env : Env) (sz : ScalarSize) (hsz : FpSz sz) {d : Nat}
    (hd : d < 32) {m : AMode} (fl : Clif.MemFlags) (hm : MemMode sz.bytes m) (s : ArmState)
    (halign : CheckSPAlignment s) {ls : List Line} {ps : Backend.PState}
    (hl : MInst.lines ctx (.fpuLoad sz (.v d) m fl) {} = .ok (ls, ps)) :
    At .plainR (m.addr ctx sz.bytes s) sz.bytes (linesEvs env ls s) := by
  -- `MemMode` excludes the literal-pool form `.const` (#565), so the generic arm applies.
  have hnc : ∀ cst, m ≠ .const cst := by rintro cst rfl; exact hm
  have hlin : (MInst.fpuLoad sz (.v d) m fl).lines ctx {} = (do
      let (pre, mem) ← memFinalize ctx m sz.bytes
      pure (pre ++ [.ins (.fpuLoad sz (.v d) mem) fl.trapCode], ({} : Backend.PState))) := by
    cases m <;> first | exact absurd rfl (hnc _) | rfl
  rw [hlin] at hl
  simp only [bind, Except.bind] at hl
  split at hl
  · cases hl
  · rename_i v hf
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    exact memFinalize_evs ctx env (by have := fpSz_bytes hsz; omega) (fun m' => .fpuLoad sz (.v d) m') _
      .plainR (fun env' t m' hf' hs ai hai => fpuLoad_line_evs env' ctx sz hsz d hd m' hf' t hs hai)
      hm s halign hf

/-- **The events of an allocated SIMD&FP store's lines**: at most one, at `AMode.addr`. -/
theorem fpuStore_lines_evs (ctx : FnCtx) (env : Env) (sz : ScalarSize) (hsz : FpSz sz) {d : Nat}
    (hd : d < 32) {m : AMode} (fl : Clif.MemFlags) (hm : MemMode sz.bytes m) (s : ArmState)
    (halign : CheckSPAlignment s) {ls : List Line} {ps : Backend.PState}
    (hl : MInst.lines ctx (.fpuStore sz (.v d) m fl) {} = .ok (ls, ps)) :
    At .plainW (m.addr ctx sz.bytes s) sz.bytes (linesEvs env ls s) := by
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  · rename_i v hf
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    exact memFinalize_evs ctx env (by have := fpSz_bytes hsz; omega) (fun m' => .fpuStore sz (.v d) m') _
      .plainW (fun env' t m' hf' hs ai hai => fpuStore_line_evs env' ctx sz hsz d hd m' hf' t hs hai)
      hm s halign hf

end Concurrency.VCodeAddr

import FV.E2E.ExecFrame
import FV.Backend.Proof.RegallocMem

/-! # The memory reads of the backend's instructions (L3 (c), D2)

`MemReads` (`FV/E2E/ExecFrame.lean`) of the instruction an `Insn` encodes:

* `Insn.memReads_nil`: empty for every `Insn` other than the loads (`Insn.loads`): stores,
  `stp`, `stlr`/`stlxr` included;
* `memReads_load`: a single-register load with a final addressing mode reads `op.bytes` bytes at
  `AMode.addr`;
* `memReads_ldp_fplr`: the epilogue's `ldp x29, x30, [sp], #16` reads 16 bytes at `sp`;
* `memReads_excl`: `ldar`/`ldaxr` read `bits / 8` bytes at the base register.
-/

set_option linter.unusedSimpArgs false

namespace Backend.Proof

open Backend E2E.ExecBytes E2E.ExecFrame

/-- The loads among the backend's instructions. -/
def _root_.Backend.Insn.loads : Insn → Bool
  | .load .. | .ldp .. | .ldar .. | .ldaxr .. | .ldrGotLo12 .. | .ldrTlsDescLo12 .. => true
  -- the model's register-offset class reads for these encodings (`RegImm.ofRegOffset`)
  | .store .fpuStore128 _ (.regReg ..) | .store .fpuStore128 _ (.regScaled ..)
  | .store .fpuStore128 _ (.regScaledExtended ..) | .store .fpuStore128 _ (.regExtended ..) => true
  | _ => false

/-- `ArmInst.norm` changes no field `MemReads` reads. -/
theorem memReads_norm (a : Arm.ArmInst) (s : Arm.ArmState) : MemReads a.norm s = MemReads a s := by
  cases a <;> rename_i x <;> cases x <;> rfl

theorem ldstFields_store_reads {size : BitVec 2} {V : BitVec 1} {opc : BitVec 2} {bytes : Nat}
    {Rt : BitVec 5} {m : AMode} {a : Arm.ArmInst} (h : ldstFields size V opc bytes Rt m = .ok a)
    (hopc : (opc = 0 ∧ V = 0) ∨ (opc = 2 ∧ V = 1 ∧ ∀ rn rm, m ≠ .regReg rn rm ∧ m ≠ .regScaled rn rm ∧
      ∀ e, m ≠ .regScaledExtended rn rm e ∧ m ≠ .regExtended rn rm e))
    (s : Arm.ArmState) : MemReads a s = [] := by
  rcases hopc with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hm⟩ <;>
  · cases m <;> (try simp at hm) <;> simp only [ldstFields, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h <;> (repeat' split at h) <;>
      (try simp only [reduceCtorEq, Except.ok.injEq] at h) <;> (try subst h) <;>
      (try contradiction) <;> (try cases h) <;>
      simp (config := {decide := true}) [MemReads, RegImm.reads, RegImm.memop, RegImm.ofUnsigned,
        RegImm.ofUnscaled, RegImm.ofPost, RegImm.ofPre, RegImm.ofRegOffset, ldsturReads,
        Arm.BitVec.lsb]

/-- **The instructions other than the loads read no memory.** -/
theorem Insn.memReads_nil {x : Insn} (hx : x.loads = false) {env : Env} {a : Arm.ArmInst}
    (h : x.toArmInst env = .ok a) (s : Arm.ArmState) : MemReads a s = [] := by
  simp only [Insn.toArmInst, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i a0 h0
  simp only [Except.ok.injEq] at h
  subst h
  rw [memReads_norm]
  cases x <;> simp only [Insn.loads, reduceCtorEq] at hx
  case store op rt m =>
    simp only [Insn.armFields, bind, Except.bind] at h0
    repeat' split at h0
    all_goals first
      | cases h0
      | (refine ldstFields_store_reads h0 ?_ s
         cases op <;> simp only [StoreOp.fields] at h0 ⊢ <;> simp only [true_and, and_true]
         all_goals first
           | (left; decide)
           | (refine .inr fun rn rm => ⟨?_, ?_, fun e => ⟨?_, ?_⟩⟩ <;> rintro rfl <;>
               simp at hx))
  all_goals (simp only [Insn.armFields, Insn.armFields.exclFields, bind, Except.bind, pure,
    Except.pure, throw, throwThe, MonadExceptOf.throw] at h0)
  all_goals (repeat' split at h0) <;> (try simp only [reduceCtorEq, Except.ok.injEq] at h0) <;>
    (try subst h0) <;> (try cases h0) <;> (try rfl)

theorem extend_reg_uxtx0 (x : BitVec 64) : Arm.extend_reg x (Arm.decode_reg_extend 3#3) 0 = x := by
  rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
  apply BitVec.eq_of_toNat_eq
  simp [Arm.extend_reg, Arm.ExtendType.unsigned_len]
  exact x.isLt

theorem extend_reg_uxtx (x : BitVec 64) (k : Nat) (hk : k < 64) :
    Arm.extend_reg x (Arm.decode_reg_extend 3#3) k = x <<< k := by
  rw [show Arm.decode_reg_extend 3#3 = .UXTX from rfl]
  exact uxtx_shift x k hk

theorem load_armFields {op : LoadOp} {rt : Reg} {m : AMode} {env : Env} {a0 : Arm.ArmInst}
    (h : Insn.armFields env (.load op rt m) = .ok a0) :
    ∃ Rt, ldstFields op.fields.1 op.fields.2.1 op.fields.2.2 op.bytes Rt m = .ok a0 := by
  simp only [Insn.armFields, bind, Except.bind] at h
  repeat' split at h
  all_goals first | cases h | exact ⟨_, h⟩

/-- **A single-register load with a final addressing mode reads `op.bytes` bytes at its
address** (the 128-bit SIMD&FP load only at an immediate offset). -/
theorem memReads_load (ctx : FnCtx) {op : LoadOp} {rt : Reg} {m : AMode}
    (hm : FinalAM op.bytes m) (hop : op = .fpuLoad128 → (∃ rn off, m = .unsignedOffset rn off) ∨ ∃ rn off, m = .unscaled rn off)
    {env : Env} {a : Arm.ArmInst} (h : (Insn.load op rt m).toArmInst env = .ok a)
    (s : Arm.ArmState) : MemReads a s = [(m.addr ctx op.bytes s, op.bytes)] := by
  simp only [Insn.toArmInst, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i a0 h0
  simp only [Except.ok.injEq] at h
  subst h
  rw [memReads_norm]
  obtain ⟨Rt, h0⟩ := load_armFields h0
  cases m with
  | unsignedOffset rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    simp only [ldstFields, h1, uField, h2, hRn, bne_iff_ne, ne_eq, not_true_eq_false, ite_false,
      ite_true, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    have hv : BitVec.setWidth 64 (BitVec.ofNat 12 (off / op.bytes)) <<< log2 op.bytes =
        BitVec.ofNat 64 off := by
      apply BitVec.eq_of_toNat_eq
      cases op <;> simp [LoadOp.bytes] at h1 h2 <;>
        simp [log2, LoadOp.bytes, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt h2, Nat.shiftLeft_eq] <;>
        omega
    cases op <;> simp (config := {decide := true}) [MemReads, RegImm.reads, RegImm.memop,
      RegImm.ofUnsigned, RegImm.addr, RegImm.scale, LoadOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, LoadOp.bytes, log2] at h1 h2 hv ⊢
    all_goals exact hv
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    simp only [ldstFields, sField, hRn, show -(2 ^ (9 - 1) : Int) ≤ off ∧ off < 2 ^ (9 - 1) by omega,
      and_self, ite_true, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    have hv := simm9_value off h1 h2
    cases op <;> simp (config := {decide := true}) [MemReads, RegImm.reads, RegImm.memop,
      RegImm.ofUnscaled, ldsturReads, RegImm.addr, RegImm.scale, LoadOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, LoadOp.bytes, log2, hv]
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuLoad128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemReads, RegImm.reads, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, LoadOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, LoadOp.bytes, log2, hrm, extend_reg_uxtx0]
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuLoad128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemReads, RegImm.reads, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, LoadOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, LoadOp.bytes, log2, hrm, extend_reg_uxtx]
  | regScaledExtended rn rm e =>
    obtain ⟨hb, hi, he⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuLoad128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    rcases he with rfl | rfl | rfl | rfl <;>
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0 <;>
    (simp (config := {decide := true}) only [ite_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_or, Bool.or_true, beq_self_eq_true, pure, Except.pure, Except.ok.injEq] at h0) <;>
    subst h0 <;>
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemReads, RegImm.reads, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, LoadOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, LoadOp.bytes, log2, hrm, ExtendOp.bits]
    all_goals done
  | regExtended rn rm e =>
    obtain ⟨hb, hi, he⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuLoad128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    rcases he with rfl | rfl | rfl | rfl <;>
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0 <;>
    (simp (config := {decide := true}) only [ite_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_or, Bool.or_true, beq_self_eq_true, pure, Except.pure, Except.ok.injEq] at h0) <;>
    subst h0 <;>
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemReads, RegImm.reads, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, LoadOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, LoadOp.bytes, log2, hrm, ExtendOp.bits]
    all_goals done
  | _ => simp [FinalAM] at hm

/-- The epilogue's `ldp x29, x30, [sp], #16` reads the 16 bytes at `sp`. -/
theorem memReads_ldp_fplr {env : Env} {a : Arm.ArmInst}
    (h : (Insn.ldp Reg.fp Reg.lr (.spPostIndexed 16)).toArmInst env = .ok a) (s : Arm.ArmState) :
    MemReads a s = [(spOf s, 16)] := by
  have e : (Insn.ldp Reg.fp Reg.lr (.spPostIndexed 16)).toArmInst env = .ok
      (.LDST (.Reg_pair_post_indexed { opc := 2, V := 0, L := 1, imm7 := 2, Rt2 := 30, Rn := 31, Rt := 29 })) := by
    simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl
  rw [e, Except.ok.injEq] at h
  subst h
  simp (config := {decide := true}) [MemReads, RegPair.reads, RegPair.mk, RegPair.addr,
    RegPair.scale, Arm.BitVec.lsb, spOf, Arm.read_gpr]

theorem exclFields_ok {bits o2 L : Nat} {Rs : BitVec 5} {rt rn : Reg} {a : Arm.ArmInst}
    {Rn : BitVec 5} (hRn : rn.encSP = .ok Rn)
    (h : Insn.armFields.exclFields bits o2 L Rs rt rn = .ok a) :
    ∃ size Rt, a = .LDST (.Reg_exclusive
      { size := size, ord := BitVec.ofNat 1 o2, L := BitVec.ofNat 1 L, Rs := Rs, o0 := 1#1, Rn := Rn, Rt := Rt }) ∧
      (8 <<< size.toNat) / 8 = bits / 8 := by
  unfold Insn.armFields.exclFields at h
  have : bits = 8 ∨ bits = 16 ∨ bits = 32 ∨ bits = 64 ∨
      (bits ≠ 8 ∧ bits ≠ 16 ∧ bits ≠ 32 ∧ bits ≠ 64) := by omega
  rcases this with rfl | rfl | rfl | rfl | ⟨h1, h2, h3, h4⟩
  all_goals simp only [bind, Except.bind, hRn, pure, Except.pure] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; exact ⟨_, _, rfl, by decide⟩)
    | (cases h; done)
    | (exfalso; simp_all [throw, throwThe, MonadExceptOf.throw])
    | (simp [throw, throwThe, MonadExceptOf.throw] at h)
    | omega

/-- `ldar`/`ldaxr` read `bits / 8` bytes at the base register. -/
theorem memReads_excl {bits : Nat} {rt rn : Reg} (hrn : BaseOk rn) {env : Env} {a : Arm.ArmInst}
    (h : (Insn.ldar bits rt rn).toArmInst env = .ok a ∨ (Insn.ldaxr bits rt rn).toArmInst env = .ok a)
    (s : Arm.ArmState) : MemReads a s = [(regX s rn, bits / 8)] := by
  obtain ⟨Rn, hRn, hr, -⟩ := enc_base hrn s
  rcases h with h | h <;>
  · simp only [Insn.toArmInst, Functor.map, Except.map] at h
    split at h
    · cases h
    rename_i a0 h0
    simp only [Except.ok.injEq] at h
    subst h
    rw [memReads_norm]
    simp only [Insn.armFields] at h0
    obtain ⟨size, Rt, rfl, hb⟩ := exclFields_ok hRn h0
    simp (config := {decide := true}) [MemReads, exclReads, hr, hb]

/-! ## The reads of straight-line lines -/

/-- The memory reads of straight-line lines `ls` run from `s` (each line's instruction at the
state `execLines` reaches before it) satisfy `P`. -/
def LinesReads (env : Env) (ls : List Line) (s : Arm.ArmState) (P : BitVec 64 → Prop) : Prop :=
  ∀ k x t, ls[k]? = some (.ins x t) → ∀ s1, execLines env (ls.take k) s = some s1 →
    ∀ env' a, x.toArmInst env' = .ok a → ∀ p ∈ E2E.ExecBytes.MemReads a s1, ∀ i < p.2,
      P (p.1 + BitVec.ofNat 64 i)

theorem LinesReads.mono {env : Env} {ls : List Line} {s : Arm.ArmState} {P Q : BitVec 64 → Prop}
    (h : LinesReads env ls s P) (hPQ : ∀ a, P a → Q a) : LinesReads env ls s Q :=
  fun k x t hk s1 hs1 env' a ha p hp i hi => hPQ _ (h k x t hk s1 hs1 env' a ha p hp i hi)

/-- Lines without loads read nothing. -/
theorem linesReads_noLoads {env : Env} {ls : List Line} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (h : ∀ x t, Line.ins x t ∈ ls → x.loads = false) : LinesReads env ls s P :=
  fun _ x t hk _ _ _ a ha p hp => by
    rw [Insn.memReads_nil (h x t (List.mem_of_getElem? hk)) ha] at hp; cases hp

/-- The lines `ls ++ [x]` whose `ls` hold no load: only the reads of `x` after `ls` count. -/
theorem linesReads_append_last {env : Env} {ls : List Line} {x : Insn} {t : Option Clif.TrapCode}
    {s : Arm.ArmState} {P : BitVec 64 → Prop} (hpre : ∀ y t', Line.ins y t' ∈ ls → y.loads = false)
    (hlast : ∀ s1, execLines env ls s = some s1 → ∀ env' a, x.toArmInst env' = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemReads a s1, ∀ i < p.2, P (p.1 + BitVec.ofNat 64 i)) :
    LinesReads env (ls ++ [.ins x t]) s P := by
  intro k y t' hk s1 hs1 env' a ha p hp i hi
  rcases Nat.lt_or_ge k ls.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    rw [Insn.memReads_nil (hpre y t' (List.mem_of_getElem? hk)) ha] at hp
    cases hp
  · rw [List.getElem?_append_right hge] at hk
    have hk0 : k - ls.length = 0 := by
      rcases h : k - ls.length with _ | n
      · rfl
      · rw [h] at hk; simp at hk
    rw [hk0] at hk
    simp only [List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hk
    obtain ⟨rfl, -⟩ := hk
    have hkl : k = ls.length := by omega
    subst hkl
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hs1
    exact hlast s1 hs1 env' a ha p hp i hi

/-- The lines `x :: ls` whose `ls` hold no load: only the reads of `x` at the start count. -/
theorem linesReads_cons {env : Env} {x : Insn} {t : Option Clif.TrapCode} {ls : List Line}
    {s : Arm.ArmState} {P : BitVec 64 → Prop} (hrest : ∀ y t', Line.ins y t' ∈ ls → y.loads = false)
    (hfirst : ∀ env' a, x.toArmInst env' = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemReads a s, ∀ i < p.2, P (p.1 + BitVec.ofNat 64 i)) :
    LinesReads env (.ins x t :: ls) s P := by
  intro k y t' hk s1 hs1 env' a ha p hp i hi
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hk
    obtain ⟨rfl, -⟩ := hk
    simp only [List.take_zero, execLines, Option.some.injEq] at hs1
    subst hs1
    exact hfirst env' a ha p hp i hi
  | succ k =>
    simp only [List.getElem?_cons_succ] at hk
    rw [Insn.memReads_nil (hrest y t' (List.mem_of_getElem? hk)) ha] at hp
    cases hp

theorem loadConst64_noLoads (rd : Reg) (v : Nat) :
    ∀ x t, Line.ins x t ∈ loadConst64 rd v → x.loads = false := by
  intro x t h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with h | ⟨j, _, hj⟩
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  · split at hj
    · simp only [Option.some.injEq, Line.ins.injEq] at hj; obtain ⟨rfl, -⟩ := hj; rfl
    · cases hj

/-! ## The reads of a load's lines -/

/-- `memFinalize`'s offset form `fin B o` (base `sp` or `x29`): no load before the access, a
final mode, and the address of the original mode in the state after the extra lines. -/
theorem memFinalize_fin (ctx : FnCtx) {b : Nat} (hb : 0 < b) {B : Reg} (hB : B = .sp ∨ B = .x 29)
    (o : Int) {pre : List Line} {m' : AMode}
    (hr : (match simm9? o with
      | some k => ([], AMode.unscaled B k)
      | none => match uimm12Scaled? o b with
        | some k => ([], .unsignedOffset B k)
        | none => (loadConst64 (.x 16) (u64 o), .regExtended B (.x 16) .sxtx)) = (pre, m'))
    (env : Env) (s : Arm.ArmState) :
    (∀ x t, Line.ins x t ∈ pre → x.loads = false) ∧ FinalAM b m' ∧
      ∀ s1, execLines env pre s = some s1 → m'.addr ctx b s1 = regX s B + BitVec.ofInt 64 o := by
  have hBok : BaseOk B := by rcases hB with rfl | rfl <;> simp [BaseOk]
  cases h9 : simm9? o with
  | some k =>
    have hk : k = o ∧ -256 ≤ k ∧ k ≤ 255 := by
      simp only [simm9?] at h9; split at h9 <;> simp_all
    simp only [h9, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨by simp, ⟨hBok, hk.2.1, by omega⟩, fun s1 h1 => ?_⟩
    simp only [execLines, Option.some.injEq] at h1
    subst h1
    simp [AMode.addr, hk.1]
  | none =>
    cases hu : uimm12Scaled? o b with
    | some k =>
      have hk : (k : Int) = o ∧ k % b = 0 ∧ k ≤ 4095 * b := by
        simp only [uimm12Scaled?] at hu
        split at hu
        · rename_i hc
          simp only [Option.some.injEq] at hu
          subst hu
          obtain ⟨h0, h1, h2⟩ := hc
          exact ⟨Int.toNat_of_nonneg h0, by simpa using h2, by omega⟩
        · cases hu
      simp only [h9, hu, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨by simp, ⟨hBok, hk.2.1, ?_⟩, fun s1 h1 => ?_⟩
      · have := Nat.div_le_div_right (c := b) hk.2.2
        rw [Nat.mul_div_cancel _ hb] at this; omega
      · simp only [execLines, Option.some.injEq] at h1
        subst h1
        simp only [AMode.addr]
        congr 1
        rw [← hk.1]; rfl
    | none =>
      simp only [h9, hu, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨loadConst64_noLoads _ _, ⟨hBok, by simp [IdxOk], by simp⟩, fun s1 h1 => ?_⟩
      rw [(steps_loadConst64 env (n := 16) (by omega) (u64 o) s).exec, Option.some.injEq] at h1
      subst h1
      have hBS : ∀ P X, regX (pcx s 16 P X) B = regX s B := by
        intro P X
        rcases hB with rfl | rfl
        · simp [pcx, regX, spOf, Arm.r_of_w_different]
        · simp [pcx, regX, rnum, Arm.r_of_w_different]
      have h16 : ∀ P X, regX (pcx s 16 P X) (.x 16) = X := by
        intro P X; simp [pcx, regX, rnum, Arm.r_of_w_different, Arm.r_of_w_same]
      show regX _ B + Arm.extend_reg (regX _ (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 = _
      rw [hBS, h16, show ExtendOp.sxtx.bits = 7#3 from rfl, sxtx_id, ofNat_u64]

/-- **`memFinalize` of a load/store mode**: no load among the extra lines, a final mode, at the
original mode's address in the state after them. -/
theorem memFinalize_addr (ctx : FnCtx) {b : Nat} (hb : 0 < b) {m : AMode} (hm : MemMode b m)
    {pre : List Line} {m' : AMode} (hf : memFinalize ctx m b = .ok (pre, m')) (env : Env)
    (s : Arm.ArmState) :
    (∀ x t, Line.ins x t ∈ pre → x.loads = false) ∧ FinalAM b m' ∧
      ∀ s1, execLines env pre s = some s1 → m'.addr ctx b s1 = m.addr ctx b s := by
  cases m with
  | slotOffset off =>
    simp only [memFinalize, pure, Except.pure, Except.ok.injEq] at hf
    obtain ⟨h1, h2, h4⟩ := memFinalize_fin ctx hb (B := .sp) (.inl rfl) _ hf env s
    exact ⟨h1, h2, fun s1 hs1 => by rw [h4 s1 hs1]; simp [AMode.addr, regX]⟩
  | spOffset off =>
    simp only [memFinalize, pure, Except.pure, Except.ok.injEq] at hf
    obtain ⟨h1, h2, h4⟩ := memFinalize_fin ctx hb (B := .sp) (.inl rfl) _ hf env s
    exact ⟨h1, h2, fun s1 hs1 => by rw [h4 s1 hs1]; simp [AMode.addr, regX]⟩
  | fpOffset off =>
    simp only [memFinalize, pure, Except.pure, Except.ok.injEq, Reg.fp] at hf
    obtain ⟨h1, h2, h4⟩ := memFinalize_fin ctx hb (B := .x 29) (.inr rfl) _ hf env s
    exact ⟨h1, h2, fun s1 hs1 => by rw [h4 s1 hs1]; simp [AMode.addr]⟩
  | _ =>
    simp only [MemMode] at hm <;>
    · rw [memFinalize_final ctx _ hm, Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      refine ⟨by simp, hm, fun s1 hs1 => ?_⟩
      simp only [execLines, Option.some.injEq] at hs1
      subst hs1; rfl

/-- **The reads of a load's lines**: only the access itself, `op.bytes` bytes at the load's
address in the state where its lines start. -/
theorem mload_reads (ctx : FnCtx) {op : LoadOp} {rt : Reg} {m : AMode} {fl : Clif.MemFlags}
    (hm : MemMode op.bytes m)
    (hop : op = .fpuLoad128 → ∀ pre m', memFinalize ctx m op.bytes = .ok (pre, m') →
      (∃ rn off, m' = .unsignedOffset rn off) ∨ ∃ rn off, m' = .unscaled rn off)
    {ps : PState} {ls : List Line} {ps' : PState}
    (hl : (MInst.load op rt m fl).lines ctx ps = .ok (ls, ps')) (env : Env) (s : Arm.ArmState) :
    LinesReads env ls s (fun a => ∃ k < op.bytes, a = m.addr ctx op.bytes s + BitVec.ofNat 64 k) := by
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i r hr
  obtain ⟨pre, m'⟩ := r
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  obtain ⟨h1, h2, h3⟩ := memFinalize_addr ctx (load_bytes_pos op) hm hr env s
  refine linesReads_append_last h1 fun s1 hs1 env' a ha p hp i hi => ?_
  rw [memReads_load ctx h2 (fun e => hop e _ _ hr) ha, List.mem_singleton] at hp
  subst hp
  exact ⟨i, hi, by rw [h3 s1 hs1]⟩

/-! ## The allocated instructions without loads -/

/-- The allocated instructions whose lines may hold a load (or a register-offset SIMD&FP store,
which the model's register-offset class reads as a load). -/
def _root_.Backend.MInst.memRd : MInst → Bool
  | .load .. | .loadAcquire .. | .jtSequence .. | .atomicRmwLoop .. | .atomicCasLoop ..
  | .loadExtNameGot .. | .elfTlsGetAddr .. | .store .fpuStore128 .. => true
  | _ => false

/-- A line without a load. -/
def _root_.Backend.Line.loadFree : Line → Bool
  | .ins i _ => !i.loads
  | _ => true

theorem memFinalize_loadFree {c : FnCtx} {mm : AMode} {b : Nat} {v : List Line × AMode}
    (h : memFinalize c mm b = .ok v) : ∀ ln ∈ v.1, ln.loadFree = true := by
  intro ln hln
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, throw, throwThe,
    MonadExceptOf.throw, reduceCtorEq] at h <;> subst h
  all_goals first
    | (simp at hln; done)
    | (split at hln
       · simp at hln
       · split at hln
         · simp at hln
         · obtain ⟨x, t, rfl⟩ : ∃ x t, ln = .ins x t := by
             simp only [loadConst64, List.mem_cons, List.mem_filterMap] at hln
             rcases hln with rfl | ⟨j, _, hj⟩
             · exact ⟨_, _, rfl⟩
             · split at hj
               · simp only [Option.some.injEq] at hj; exact ⟨_, _, hj.symm⟩
               · cases hj
           simp [Line.loadFree, loadConst64_noLoads _ _ x t hln])

theorem store_loads {op : StoreOp} {rd : Reg} {m : AMode} (h : op ≠ .fpuStore128) :
    (Insn.store op rd m).loads = false := by
  cases op <;> cases m <;> simp_all [Insn.loads]

/-- **The lines of an allocated instruction other than `memRd` hold no load.** -/
theorem lines_noLoads {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) (hm : m.memRd = false) :
    ∀ i t, Line.ins i t ∈ ls → i.loads = false := by
  suffices hs : ∀ ln ∈ ls, ln.loadFree = true by
    intro i t hi
    have := hs _ hi
    simpa [Line.loadFree] using this
  have hmf' : ∀ mm b v, memFinalize c mm b = .ok v → ∀ ln ∈ v.1, ln.loadFree = true :=
    fun _ _ _ hv => memFinalize_loadFree hv
  have hk : ∀ (k : CondBrKind) l, (k.insn l).loads = false := fun k l => by cases k <;> rfl
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals (try (simp [MInst.memRd] at hm; done))
  all_goals intro ln hln
  all_goals simp [MInst.lines.addOff] at hln
  all_goals (repeat' (split at hln)) <;> (try simp at hln)
  all_goals first
    | exact hmf' _ _ _ (by assumption) _ hln
    | (rename_i heq; simp [throw, throwThe, MonadExceptOf.throw] at heq; done)
    | (rcases hln with h | h | h | h | h | h | h | h | h <;>
        first
          | exact hmf' _ _ _ (by assumption) _ h
          | rfl
          | (simp only [Line.loadFree, hk, Bool.not_false]; done)
          | (rename_i hx; obtain ⟨-, rfl⟩ := hx; rfl)
          | (subst h; rfl)
          | (subst h; simp only [Line.loadFree, hk, Bool.not_false]; done)
          | (subst h; simp_all [Line.loadFree, Insn.loads, MInst.memRd]; done)
          | (obtain ⟨a, ha, rfl⟩ := h; rfl)
          | (split at h <;> (try split at h) <;> simp at h <;> subst h <;> rfl))
    | (subst hln; simp_all [Line.loadFree, Insn.loads, MInst.memRd]; done)
    | (rcases hln with h | h
       · exact hmf' _ _ _ (by assumption) _ h
       · subst h
         simp only [Line.loadFree, Bool.not_eq_eq_eq_not, Bool.not_true]
         exact store_loads (fun e => by subst e; simp [MInst.memRd] at hm))

end Backend.Proof

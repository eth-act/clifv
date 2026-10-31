import FV.E2E.ExecReads
import FV.ArmFault.Step

/-! # The memory writes of the backend's instructions (A3, #412, slice F8b)

`MemWrites a s` (the byte ranges `(address, length)` the instruction `a` writes at `s`) mirrors
`E2E.ExecBytes.MemReads`: the stores of every single-register addressing mode, `stp`, the
release / exclusive stores; empty for every other instruction. With `MemReads` it covers the
precise footprint of the instruction (`Concurrency.ArmInstFoot.instEvs`):

* `instEvs_cover`: every read event of `instEvs a s` is a range of `MemReads a s`, every write
  event one of `MemWrites a s`;
* `evsOk_of`: an instruction whose read bytes a memory map allows for reading and whose written
  bytes it allows for writing does not fault (`ArmFault.evsOk`);
* `Insn.memWrites_nil`: the backend's instructions other than the stores (`Insn.stores`) write
  nothing;
* `LinesWrites env ls s P`: the writes of straight-line lines satisfy `P` (as `LinesReads`), with
  `linesWrites_noStores`, `linesWrites_append_last`, `linesWrites_cons`.
-/

set_option linter.unusedSimpArgs false

namespace E2E.ExecFrame

open Arm

namespace RegImm

/-- The bytes a single-register store writes. -/
def writes (i : LDST.Reg_imm_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if memop i = 0#1 then [(addr i s, (8 <<< scale i) / 8)] else []

end RegImm

namespace RegPair

/-- The bytes an `stp` writes. -/
def writes (i : LDST.Reg_pair_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if i.L? then [] else [(addr i s, 2 * ((8 <<< scale i) / 8))]

end RegPair

/-- The bytes a SIMD&FP `stur` writes (`exec_ldstur`). -/
def ldsturWrites (i : Reg_unscaled_imm_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if BitVec.getLsbD i.opc 0 then []
  else [(read_gpr 64 i.Rn s + BitVec.signExtend 64 i.imm9,
      (8 <<< (BitVec.extractLsb' 1 1 i.opc ++ i.size).toNat) / 8)]

/-- The bytes a release / exclusive store writes (`exec_reg_exclusive`; the model's store
exclusive always succeeds). -/
def exclWrites (i : Reg_exclusive_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if i.L = 1#1 then [] else [(read_gpr 64 i.Rn s, (8 <<< i.size.toNat) / 8)]

end E2E.ExecFrame

namespace E2E.ExecBytes

open Arm E2E.ExecFrame

/-- **The byte ranges `(address, length)` the instruction `a` writes at `s`**: the stores' (every
single-register addressing mode, `stp`, the release / exclusive stores); empty for every other
instruction. -/
def MemWrites : ArmInst → ArmState → List (BitVec 64 × Nat)
  | .LDST (.Reg_imm_post_indexed i), s => RegImm.writes (RegImm.ofPost i) s
  | .LDST (.Reg_unsigned_imm i), s => RegImm.writes (RegImm.ofUnsigned i) s
  | .LDST (.Reg_unscaled_imm i), s =>
    if i.VR = 0b1#1 then ldsturWrites i s else RegImm.writes (RegImm.ofUnscaled i) s
  | .LDST (.Reg_pair_pre_indexed i), s =>
    RegPair.writes (RegPair.mk true false i.opc i.V i.L i.imm7 i.Rt2 i.Rn i.Rt) s
  | .LDST (.Reg_pair_post_indexed i), s =>
    RegPair.writes (RegPair.mk true true i.opc i.V i.L i.imm7 i.Rt2 i.Rn i.Rt) s
  | .LDST (.Reg_pair_signed_offset i), s =>
    RegPair.writes (RegPair.mk false false i.opc i.V i.L i.imm7 i.Rt2 i.Rn i.Rt) s
  | .LDST (.Reg_imm_pre_indexed i), s => RegImm.writes (RegImm.ofPre i) s
  | .LDST (.Reg_reg_offset i), s => RegImm.writes (RegImm.ofRegOffset i) s
  | .LDST (.Reg_exclusive i), s => exclWrites i s
  | _, _ => []

open Concurrency Concurrency.ArmThread Concurrency.ArmInstFoot

/-- The events of a single-register load/store are its `RegImm.reads`/`RegImm.writes`. -/
theorem immEvs_cover {inst : LDST.Reg_imm_cls} {s : ArmState} {e : Ev} (he : e ∈ immEvs inst s) :
    (e.k.dir = .R → (e.addr, e.n) ∈ RegImm.reads inst s) ∧
      (e.k.dir = .W → (e.addr, e.n) ∈ RegImm.writes inst s) := by
  unfold immEvs at he
  simp only at he
  repeat' (split at he)
  all_goals (try (simp at he; done))
  all_goals
    simp only [List.mem_singleton] at he
    subst he
    constructor <;> intro h <;>
      simp_all [RegImm.writes, RegImm.reads, RegImm.memop, RegImm.addr, RegImm.scale, AKind.dir]

theorem pairEvs_cover {inst : LDST.Reg_pair_cls} {s : ArmState} {e : Ev} (he : e ∈ pairEvs inst s) :
    (e.k.dir = .R → (e.addr, e.n) ∈ RegPair.reads inst s) ∧
      (e.k.dir = .W → (e.addr, e.n) ∈ RegPair.writes inst s) := by
  unfold pairEvs at he
  simp only at he
  repeat' (split at he)
  all_goals (try (simp at he; done))
  all_goals
    simp only [List.mem_singleton] at he
    subst he
    constructor <;> intro h <;>
      simp_all [RegPair.writes, RegPair.reads, RegPair.addr, RegPair.scale, AKind.dir]

/-- **The footprint is covered**: a read event of `instEvs a s` is a range of `MemReads a s`, a
write event one of `MemWrites a s`. -/
theorem instEvs_cover {a : ArmInst} {s : ArmState} {e : Ev} (he : e ∈ instEvs a s) :
    (e.k.dir = .R → (e.addr, e.n) ∈ MemReads a s) ∧ (e.k.dir = .W → (e.addr, e.n) ∈ MemWrites a s) := by
  cases a with
  | LDST i =>
    cases i with
    | Reg_imm_post_indexed i => exact immEvs_cover he
    | Reg_unsigned_imm i => exact immEvs_cover he
    | Reg_unscaled_imm i =>
      simp only [instEvs] at he
      simp only [MemReads, MemWrites]
      by_cases hV : i.VR = 0b1#1
      · simp only [hV, ite_true] at he ⊢
        unfold ldsturEvs at he
        simp only at he
        repeat' (split at he)
        all_goals (try (simp at he; done))
        all_goals
          simp only [List.mem_singleton] at he
          subst he
          constructor <;> intro h <;> simp_all [ldsturReads, ldsturWrites, AKind.dir]
      · simp only [hV, ite_false] at he ⊢
        exact immEvs_cover he
    | Reg_pair_pre_indexed i => exact pairEvs_cover he
    | Reg_pair_post_indexed i => exact pairEvs_cover he
    | Reg_pair_signed_offset i => exact pairEvs_cover he
    | Reg_imm_pre_indexed i => exact immEvs_cover he
    | Reg_reg_offset i =>
      simp only [instEvs] at he
      split at he
      · simp at he
      · exact immEvs_cover he
    | Reg_exclusive i =>
      simp only [instEvs] at he
      unfold exclEvs at he
      repeat' (split at he)
      all_goals (try (simp at he; done))
      all_goals
        simp only [List.mem_singleton] at he
        subst he
      · rename_i hL
        exact ⟨fun _ => by simp [MemReads, exclReads, hL], fun h => by
          simp [exclKind_R hL] at h⟩
      · rename_i hL
        exact ⟨fun h => by simp [exclKind_W hL] at h, fun _ => by
          simp [MemWrites, exclWrites, hL]⟩
    | Reg_literal i =>
      simp only [instEvs] at he
      unfold literalEvs litEv at he
      repeat' (split at he)
      all_goals (try (simp at he; done))
      all_goals
        simp only [List.mem_singleton] at he
        subst he
        constructor <;> intro h <;> simp_all [MemReads, literalReads, AKind.dir]
      all_goals (split <;> simp)
  | BR i =>
    cases i <;> simp only [instEvs] at he <;> (try (simp at he; done))
    split at he
    · simp only [List.mem_singleton] at he
      subst he
      exact ⟨fun h => by simp [dmbEv, AKind.dir] at h, fun h => by simp [dmbEv, AKind.dir] at h⟩
    · simp at he
  | _ => simp [instEvs] at he

/-- **No fault**: the bytes the instruction reads are readable and the bytes it writes are
writable under `mp`. -/
theorem evsOk_of {mp : ArmFault.MemMap} {a : ArmInst} {s : ArmState}
    (hR : ∀ p ∈ MemReads a s, ∀ k < p.2, (mp (p.1 + BitVec.ofNat 64 k)).allows .R = true)
    (hW : ∀ p ∈ MemWrites a s, ∀ k < p.2, (mp (p.1 + BitVec.ofNat 64 k)).allows .W = true) :
    ArmFault.evsOk mp (instEvs a s) = true := by
  simp only [ArmFault.evsOk, ArmFault.evOk, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro e he i hi
  obtain ⟨h1, h2⟩ := instEvs_cover he
  cases hd : e.k.dir with
  | R => exact hR _ (h1 hd) i hi
  | W => exact hW _ (h2 hd) i hi
  | F => cases mp (e.addr + BitVec.ofNat 64 i) <;> rfl

end E2E.ExecBytes

namespace Backend.Proof

open Backend E2E.ExecBytes E2E.ExecFrame

/-- The stores among the backend's instructions. -/
def _root_.Backend.Insn.stores : Insn → Bool
  | .store .. | .stp .. | .stlr .. | .stlxr .. | .fpuStore .. | .fpuStoreP .. => true
  | _ => false

/-- `ArmInst.norm` changes no field `MemWrites` reads. -/
theorem memWrites_norm (a : Arm.ArmInst) (s : Arm.ArmState) :
    MemWrites a.norm s = MemWrites a s := by
  cases a <;> rename_i x <;> cases x <;> rfl

theorem shiftLeft8_div_pos (k : Nat) : 0 < (8 <<< k) / 8 := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_div_assoc _ (by decide : 8 ∣ 8)]
  exact Nat.mul_pos (Nat.two_pow_pos k) (by decide)

/-- **Every written range is non-empty.** -/
theorem memWrites_pos (a : Arm.ArmInst) (s : Arm.ArmState) : ∀ p ∈ MemWrites a s, 0 < p.2 := by
  intro p hp
  cases a <;> try (simp [MemWrites] at hp)
  rename_i i
  cases i <;> simp only [MemWrites, RegImm.writes, RegPair.writes, ldsturWrites, exclWrites] at hp <;>
    (repeat' split at hp) <;> simp only [List.mem_singleton, List.not_mem_nil] at hp <;>
    (try subst hp) <;> first | exact hp.elim | (simp only; first
      | exact shiftLeft8_div_pos _
      | exact Nat.mul_pos (by decide) (shiftLeft8_div_pos _))

/-- A single-register load (`V = 0`, `opc ≠ 0`, or `V = 1`, `opc<0> = 1`) writes no memory, in
every addressing mode. -/
theorem ldstFields_load_writes {size : BitVec 2} {V : BitVec 1} {opc : BitVec 2} {bytes : Nat}
    {Rt : BitVec 5} {m : AMode} {a : Arm.ArmInst} (h : ldstFields size V opc bytes Rt m = .ok a)
    (hopc : (V = 0 ∧ (opc = 1 ∨ opc = 2)) ∨ (V = 1 ∧ (opc = 1 ∨ opc = 3)))
    (s : Arm.ArmState) : MemWrites a s = [] := by
  rcases hopc with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
  · cases m <;> simp only [ldstFields, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h <;> (repeat' split at h) <;>
      (try simp only [reduceCtorEq, Except.ok.injEq] at h) <;> (try subst h) <;>
      (try contradiction) <;> (try cases h) <;>
      simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop, RegImm.ofUnsigned,
        RegImm.ofUnscaled, RegImm.ofPost, RegImm.ofPre, RegImm.ofRegOffset, ldsturWrites,
        Arm.BitVec.lsb]

/-- **The instructions other than the stores write no memory.** -/
theorem Insn.memWrites_nil {x : Insn} (hx : x.stores = false) {env : Env} {a : Arm.ArmInst}
    (h : x.toArmInst env = .ok a) (s : Arm.ArmState) : MemWrites a s = [] := by
  simp only [Insn.toArmInst, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i a0 h0
  simp only [Except.ok.injEq] at h
  subst h
  rw [memWrites_norm]
  cases x <;> simp only [Insn.stores, reduceCtorEq] at hx
  case load op rt m =>
    obtain ⟨Rt, h0⟩ := load_armFields h0
    refine ldstFields_load_writes h0 ?_ s
    cases op <;> simp (config := {decide := true}) [LoadOp.fields]
  case fpuLoad sz rt m =>
    simp only [Insn.armFields, bind, Except.bind] at h0
    repeat' split at h0
    all_goals first
      | cases h0
      | exact ldstFields_load_writes h0 (.inr ⟨rfl, .inl rfl⟩) s
      | skip
  all_goals (simp only [Insn.armFields, Insn.armFields.exclFields, bind, Except.bind, pure,
    Except.pure, throw, throwThe, MonadExceptOf.throw] at h0)
  all_goals (repeat' split at h0) <;> (try simp only [reduceCtorEq, Except.ok.injEq] at h0) <;>
    (try subst h0) <;> (try cases h0) <;> (try rfl)
  all_goals simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop,
    RegImm.ofUnsigned, Arm.BitVec.lsb]

theorem store_armFields {op : StoreOp} {rt : Reg} {m : AMode} {env : Env} {a0 : Arm.ArmInst}
    (h : Insn.armFields env (.store op rt m) = .ok a0) :
    ∃ Rt, ldstFields op.fields.1 op.fields.2.1 op.fields.2.2 op.bytes Rt m = .ok a0 := by
  simp only [Insn.armFields, bind, Except.bind] at h
  repeat' split at h
  all_goals first | cases h | exact ⟨_, h⟩

/-- **A single-register store with a final addressing mode writes `op.bytes` bytes at its
address** (the 128-bit SIMD&FP store only at an immediate offset). -/
theorem memWrites_store (ctx : FnCtx) {op : StoreOp} {rt : Reg} {m : AMode}
    (hm : FinalAM op.bytes m) (hop : op = .fpuStore128 → (∃ rn off, m = .unsignedOffset rn off) ∨ ∃ rn off, m = .unscaled rn off)
    {env : Env} {a : Arm.ArmInst} (h : (Insn.store op rt m).toArmInst env = .ok a)
    (s : Arm.ArmState) : MemWrites a s = [(m.addr ctx op.bytes s, op.bytes)] := by
  simp only [Insn.toArmInst, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i a0 h0
  simp only [Except.ok.injEq] at h
  subst h
  rw [memWrites_norm]
  obtain ⟨Rt, h0⟩ := store_armFields h0
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
      cases op <;> simp [StoreOp.bytes] at h1 h2 <;>
        simp [log2, StoreOp.bytes, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt h2, Nat.shiftLeft_eq] <;>
        omega
    cases op <;> simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop,
      RegImm.ofUnsigned, RegImm.addr, RegImm.scale, StoreOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, StoreOp.bytes, log2] at h1 h2 hv ⊢
    all_goals exact hv
  | unscaled rn off =>
    obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    simp only [ldstFields, sField, hRn, show -(2 ^ (9 - 1) : Int) ≤ off ∧ off < 2 ^ (9 - 1) by omega,
      and_self, ite_true, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    have hv := simm9_value off h1 h2
    cases op <;> simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop,
      RegImm.ofUnscaled, ldsturWrites, RegImm.addr, RegImm.scale, StoreOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, StoreOp.bytes, log2, hv]
  | regReg rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuStore128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, StoreOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, StoreOp.bytes, log2, hrm, extend_reg_uxtx0]
  | regScaled rn rm =>
    obtain ⟨hb, hi⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuStore128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0
    subst h0
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, StoreOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, StoreOp.bytes, log2, hrm, extend_reg_uxtx]
  | regScaledExtended rn rm e =>
    obtain ⟨hb, hi, he⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuStore128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    rcases he with rfl | rfl | rfl | rfl <;>
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0 <;>
    (simp (config := {decide := true}) only [ite_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_or, Bool.or_true, beq_self_eq_true, pure, Except.pure, Except.ok.injEq] at h0) <;>
    subst h0 <;>
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, StoreOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, StoreOp.bytes, log2, hrm, ExtendOp.bits]
    all_goals done
  | regExtended rn rm e =>
    obtain ⟨hb, hi, he⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb s
    obtain ⟨Rm, hRm, hrm⟩ := enc_idx hi s
    have hf : op ≠ .fpuStore128 := fun e => by
      rcases hop e with ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> cases e'
    rcases he with rfl | rfl | rfl | rfl <;>
    simp only [ldstFields, hRn, hRm, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h0 <;>
    (simp (config := {decide := true}) only [ite_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_or, Bool.or_true, beq_self_eq_true, pure, Except.pure, Except.ok.injEq] at h0) <;>
    subst h0 <;>
    cases op <;> simp at hf <;> simp (config := {decide := true}) [MemWrites, RegImm.writes, RegImm.memop,
      RegImm.ofRegOffset, RegImm.addr, RegImm.scale, StoreOp.fields, Arm.BitVec.lsb, hr, AMode.addr,
      Arm.LDST.Reg_offset.value, StoreOp.bytes, log2, hrm, ExtendOp.bits]
    all_goals done
  | _ => simp [FinalAM] at hm


/-- `stlr`/`stlxr` write `bits / 8` bytes at the base register. -/
theorem memWrites_excl {bits : Nat} {rs rt rn : Reg} (hrn : BaseOk rn) {env : Env} {a : Arm.ArmInst}
    (h : (Insn.stlr bits rt rn).toArmInst env = .ok a ∨ (Insn.stlxr bits rs rt rn).toArmInst env = .ok a)
    (s : Arm.ArmState) : MemWrites a s = [(regX s rn, bits / 8)] := by
  obtain ⟨Rn, hRn, hr, -⟩ := enc_base hrn s
  rcases h with h | h <;>
  · simp only [Insn.toArmInst, Functor.map, Except.map] at h
    split at h
    · cases h
    rename_i a0 h0
    simp only [Except.ok.injEq] at h
    subst h
    rw [memWrites_norm]
    simp only [Insn.armFields, bind, Except.bind] at h0
    try (split at h0; · cases h0)
    obtain ⟨size, Rt, rfl, hb⟩ := exclFields_ok hRn h0
    simp (config := {decide := true}) [MemWrites, exclWrites, hr, hb]

/-! ## The writes of straight-line lines -/

/-- The memory writes of straight-line lines `ls` run from `s` (each line's instruction at the
state `execLines` reaches before it) satisfy `P`. -/
def LinesWrites (env : Env) (ls : List Line) (s : Arm.ArmState) (P : BitVec 64 → Prop) : Prop :=
  ∀ k x t, ls[k]? = some (.ins x t) → ∀ s1, execLines env (ls.take k) s = some s1 →
    ∀ env' a, x.toArmInst env' = .ok a → ∀ p ∈ E2E.ExecBytes.MemWrites a s1, ∀ i < p.2,
      P (p.1 + BitVec.ofNat 64 i)

theorem LinesWrites.mono {env : Env} {ls : List Line} {s : Arm.ArmState} {P Q : BitVec 64 → Prop}
    (h : LinesWrites env ls s P) (hPQ : ∀ a, P a → Q a) : LinesWrites env ls s Q :=
  fun k x t hk s1 hs1 env' a ha p hp i hi => hPQ _ (h k x t hk s1 hs1 env' a ha p hp i hi)

/-- Lines without stores write nothing. -/
theorem linesWrites_noStores {env : Env} {ls : List Line} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (h : ∀ x t, Line.ins x t ∈ ls → x.stores = false) : LinesWrites env ls s P :=
  fun _ x t hk _ _ _ a ha p hp => by
    rw [Insn.memWrites_nil (h x t (List.mem_of_getElem? hk)) ha] at hp; cases hp

/-- The lines `ls ++ [x]` whose `ls` hold no store: only the writes of `x` after `ls` count. -/
theorem linesWrites_append_last {env : Env} {ls : List Line} {x : Insn} {t : Option Clif.TrapCode}
    {s : Arm.ArmState} {P : BitVec 64 → Prop} (hpre : ∀ y t', Line.ins y t' ∈ ls → y.stores = false)
    (hlast : ∀ s1, execLines env ls s = some s1 → ∀ env' a, x.toArmInst env' = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemWrites a s1, ∀ i < p.2, P (p.1 + BitVec.ofNat 64 i)) :
    LinesWrites env (ls ++ [.ins x t]) s P := by
  intro k y t' hk s1 hs1 env' a ha p hp i hi
  rcases Nat.lt_or_ge k ls.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    rw [Insn.memWrites_nil (hpre y t' (List.mem_of_getElem? hk)) ha] at hp
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

/-- The lines `x :: ls` whose `ls` hold no store: only the writes of `x` at the start count. -/
theorem linesWrites_cons {env : Env} {x : Insn} {t : Option Clif.TrapCode} {ls : List Line}
    {s : Arm.ArmState} {P : BitVec 64 → Prop} (hrest : ∀ y t', Line.ins y t' ∈ ls → y.stores = false)
    (hfirst : ∀ env' a, x.toArmInst env' = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemWrites a s, ∀ i < p.2, P (p.1 + BitVec.ofNat 64 i)) :
    LinesWrites env (.ins x t :: ls) s P := by
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
    rw [Insn.memWrites_nil (hrest y t' (List.mem_of_getElem? hk)) ha] at hp
    cases hp


theorem loadConst64_noStores (rd : Reg) (v : Nat) :
    ∀ x t, Line.ins x t ∈ loadConst64 rd v → x.stores = false := by
  intro x t h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with h | ⟨j, _, hj⟩
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  · split at hj
    · simp only [Option.some.injEq, Line.ins.injEq] at hj; obtain ⟨rfl, -⟩ := hj; rfl
    · cases hj

/-! ## The allocated instructions without stores -/

/-- The allocated instructions whose lines may hold a store. -/
def _root_.Backend.MInst.memWr : MInst → Bool
  | .store .. | .storeRelease .. | .atomicRmwLoop .. | .atomicCasLoop .. | .fpuStore .. => true
  | _ => false

/-- A line without a store. -/
def _root_.Backend.Line.storeFree : Line → Bool
  | .ins i _ => !i.stores
  | _ => true

theorem memFinalize_storeFree {c : FnCtx} {mm : AMode} {b : Nat} {v : List Line × AMode}
    (h : memFinalize c mm b = .ok v) : ∀ ln ∈ v.1, ln.storeFree = true := by
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
           simp [Line.storeFree, loadConst64_noStores _ _ x t hln])


theorem store_bytes_pos (op : StoreOp) : 0 < op.bytes := by cases op <;> decide

/-- `memFinalize`'s extra lines hold no store. -/
theorem memFinalize_noStores {c : FnCtx} {mm : AMode} {b : Nat} {v : List Line × AMode}
    (h : memFinalize c mm b = .ok v) : ∀ x t, Line.ins x t ∈ v.1 → x.stores = false := by
  intro x t hx
  have := memFinalize_storeFree h _ hx
  simpa [Line.storeFree] using this

/-- **The writes of a store's lines**: only the access itself, `op.bytes` bytes at the store's
address in the state where its lines start. -/
theorem mstore_writes (ctx : FnCtx) {op : StoreOp} {rt : Reg} {m : AMode} {fl : Clif.MemFlags}
    (hm : MemMode op.bytes m)
    (hop : op = .fpuStore128 → ∀ pre m', memFinalize ctx m op.bytes = .ok (pre, m') →
      (∃ rn off, m' = .unsignedOffset rn off) ∨ ∃ rn off, m' = .unscaled rn off)
    {ps : PState} {ls : List Line} {ps' : PState}
    (hl : (MInst.store op rt m fl).lines ctx ps = .ok (ls, ps')) (env : Env) (s : Arm.ArmState) :
    LinesWrites env ls s (fun a => ∃ k < op.bytes, a = m.addr ctx op.bytes s + BitVec.ofNat 64 k) := by
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i r hr
  obtain ⟨pre, m'⟩ := r
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  obtain ⟨-, h2, h3⟩ := memFinalize_addr ctx (store_bytes_pos op) hm hr env s
  refine linesWrites_append_last (memFinalize_noStores hr) fun s1 hs1 env' a ha p hp i hi => ?_
  rw [memWrites_store ctx h2 (fun e => hop e _ _ hr) ha, List.mem_singleton] at hp
  subst hp
  exact ⟨i, hi, by rw [h3 s1 hs1]⟩

/-- **The lines of an allocated instruction other than `memWr` hold no store.** -/
theorem lines_noStores {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) (hm : m.memWr = false) :
    ∀ i t, Line.ins i t ∈ ls → i.stores = false := by
  suffices hs : ∀ ln ∈ ls, ln.storeFree = true by
    intro i t hi
    have := hs _ hi
    simpa [Line.storeFree] using this
  have hmf' : ∀ mm b v, memFinalize c mm b = .ok v → ∀ ln ∈ v.1, ln.storeFree = true :=
    fun _ _ _ hv => memFinalize_storeFree hv
  have hk : ∀ (k : CondBrKind) l, (k.insn l).stores = false := fun k l => by cases k <;> rfl
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals (try (simp [MInst.memWr] at hm; done))
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
          | (simp only [Line.storeFree, hk, Bool.not_false]; done)
          | (rename_i hx; obtain ⟨-, rfl⟩ := hx; rfl)
          | (subst h; rfl)
          | (subst h; simp only [Line.storeFree, hk, Bool.not_false]; done)
          | (subst h; simp_all [Line.storeFree, Insn.stores, MInst.memWr]; done)
          | (obtain ⟨a, ha, rfl⟩ := h; rfl)
          | (split at h <;> (try split at h) <;> simp at h <;> subst h <;> rfl))
    | (subst hln; simp_all [Line.storeFree, Insn.stores, MInst.memWr]; done)
    | (rcases hln with h | h
       · exact hmf' _ _ _ (by assumption) _ h
       · subst h
         simp only [Line.storeFree, Bool.not_eq_eq_eq_not, Bool.not_true]
         exact store_loads (fun e => by subst e; simp [MInst.memWr] at hm))


end Backend.Proof

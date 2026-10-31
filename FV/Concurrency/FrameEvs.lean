import FV.Concurrency.MoveEvs
import FV.E2E.RegLevelFrame

/-!
# The events of Cranelift's frame lines (#549)

The prologue stores fp/lr and pushes the saved registers (pre-indexed `stp`/`str`, plain writes)
and the epilogue pops them and loads fp/lr (post-indexed `ldp`/`ldr`, plain reads): every event
of these lines is in the `16 + clobberBytes` bytes below the entry `sp` (fp/lr and the clobber
area), but for the prologue's stack probes (#581: `stur wzr`, plain writes at the probed bytes
`probeHitN`, 4096 bytes and more below fp/lr), and none of their instructions is an exclusive.

* `isExcl_plain`, `noExcl_of_kinds`: an instruction of a plain kind is no exclusive, so neither
  is any instruction of lines whose kinds are plain;
* `stp_fplr_evs`, `ldp_fplr_evs`: fp/lr's `stp`/`ldp` access `sp - 16`/`sp`;
* `push1_evs`, `push2_evs`, `pop1_evs`, `pop2_evs`: a push writes at `sp - 16`, a pop reads at
  `sp`;
* `linesEvs_append_steps`: the events of `A ++ B`;
* `pushLines_evs`, `popLines_evs`: the pushes/pops of one register class access
  `[B, B + pushBytes)` (`EvsIn`);
* `stur_wzr_evs`, `probeSteps_evs`, `probeLines_evs`: the stack probes write at the probed bytes;
* **`prologue_evsIn`**: the prologue accesses `[sp₀ - 16 - clobberBytes, sp₀)` and the probed
  bytes; **`epilogue_evsIn`**: the epilogue accesses `[sp₀ - 16 - clobberBytes, sp₀)`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof E2E Code VCodeEvents

/-! ## No exclusive -/

/-- An instruction of a plain kind is no exclusive. -/
theorem isExcl_plain {env : Env} {x : Insn} {ai : Arm.ArmInst} (h : x.toArmInst env = .ok ai)
    (hk : insnKind x = some .plainR ∨ insnKind x = some .plainW) : isExcl ai = false := by
  unfold Insn.toArmInst at h
  cases ha : x.armFields env with
  | error e => rw [ha] at h; cases h
  | ok a0 =>
    rw [ha] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    rw [isExcl_norm]
    cases x <;> simp only [insnKind, reduceCtorEq, Option.some.injEq, or_self] at hk <;>
      simp only [Insn.armFields, bind, Except.bind, pure, Except.pure] at ha <;>
      (repeat' split at ha) <;> (try cases ha) <;> first | exact ldstFields_notExcl ha | rfl

/-- **No instruction of lines with plain kinds only is an exclusive.** -/
theorem noExcl_of_kinds {ls : List Line} (hk : ∀ k ∈ kinds ls, k = .plainR ∨ k = .plainW)
    {x : Insn} {t : Option Clif.TrapCode} (hx : Line.ins x t ∈ ls) {env : Env} {a : ArmInst}
    (ha : x.toArmInst env = .ok a) : isExcl a = false := by
  cases hkx : insnKind x with
  | none => exact isExcl_none ha hkx
  | some k =>
    have hm : k ∈ kinds ls := List.mem_filterMap.2 ⟨_, hx, by simp [lineKind, hkx]⟩
    rcases hk k hm with rfl | rfl
    · exact isExcl_plain ha (.inl hkx)
    · exact isExcl_plain ha (.inr hkx)

/-! ## One frame instruction -/

/-- **The prologue's `stp x29, x30, [sp, #-16]!`**: one plain write at `sp - 16`, no
exclusive. -/
theorem stp_fplr_evs (env : Env) (s : ArmState) (hal : CheckSPAlignment s) :
    ∃ a, (Insn.stp Reg.fp Reg.lr (.spPreIndexed (-16))).toArmInst env = .ok a ∧ isExcl a = false ∧
      ∀ e ∈ instEvs a s, e.addr = spOf s - 16#64 ∧ e.k = .plainW := by
  refine ⟨_, by simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl, rfl, ?_⟩
  have hal' := spAligned hal
  intro e he
  simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
  subst he
  refine ⟨?_, rfl⟩
  simp only [read_gpr, spOf]
  bv_omega

/-- **The epilogue's `ldp x29, x30, [sp], #16`**: one plain read at `sp`, no exclusive. -/
theorem ldp_fplr_evs (env : Env) (s : ArmState) (hal : CheckSPAlignment s) :
    ∃ a, (Insn.ldp Reg.fp Reg.lr (.spPostIndexed 16)).toArmInst env = .ok a ∧ isExcl a = false ∧
      ∀ e ∈ instEvs a s, e.addr = spOf s ∧ e.k = .plainR := by
  refine ⟨_, by simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl, rfl, ?_⟩
  have hal' := spAligned hal
  intro e he
  simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
  subst he
  refine ⟨?_, rfl⟩
  simp only [read_gpr, spOf]
  bv_omega

theorem push_x_evs (env : Env) {n : Nat} (hn : n < 29) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.store .store64 (.x n) (.spPreIndexed (-16))).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s - 16#64 := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.store .store64 (.x n) (.spPreIndexed (-16))).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s - 16#64 := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
        Reg.encZR, show n ≤ 30 by omega, rnum, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, immEvs, LDST.reg_imm_constrain_unpredictable, LDST.Reg_offset.value, hal,
      Arm.BitVec.lsb] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp [read_gpr, spOf, add_neg16p]
  rw [hi] at h1; cases h1; exact h2

theorem push_d_evs (env : Env) {n : Nat} (hn : n < 32) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.fpuStore .size64 (.v n) (.spPreIndexed (-16))).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s - 16#64 := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.fpuStore .size64 (.v n) (.spPreIndexed (-16))).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s - 16#64 := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpLdstSize,
        Reg.encV, show n ≤ 31 by omega, rnum, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, immEvs, LDST.reg_imm_constrain_unpredictable, LDST.Reg_offset.value, hal,
      Arm.BitVec.lsb, show Arm.LDST.supported_simd_reg_imm 3#2 0#2 = true by decide] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp [read_gpr, spOf, add_neg16p]
  rw [hi] at h1; cases h1; exact h2

theorem push_xx_evs (env : Env) {a b : Nat} (ha : a < 29) (hb : b < 29) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.stp (.x a) (.x b) (.spPreIndexed (-16))).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s - 16#64 := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.stp (.x a) (.x b) (.spPreIndexed (-16))).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s - 16#64 := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields,
        Reg.encZR, show a ≤ 30 by omega, show b ≤ 30 by omega, rnum, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp only [read_gpr, spOf]
    bv_omega
  rw [hi] at h1; cases h1; exact h2

theorem push_dd_evs (env : Env) {a b : Nat} (ha : a < 32) (hb : b < 32) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.fpuStoreP .size64 (.v a) (.v b) (.spPreIndexed (-16))).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s - 16#64 := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.fpuStoreP .size64 (.v a) (.v b) (.spPreIndexed (-16))).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s - 16#64 := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpOpc,
        ScalarSize.bytes, Reg.encV, show a ≤ 31 by omega, show b ≤ 31 by omega, rnum, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp only [read_gpr, spOf]
    bv_omega
  rw [hi] at h1; cases h1; exact h2

theorem pop_x_evs (env : Env) {n : Nat} (hn : n < 29) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.load .uload64 (.x n) (.spPostIndexed 16)).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.load .uload64 (.x n) (.spPostIndexed 16)).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
        Reg.encZR, show n ≤ 30 by omega, rnum, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, immEvs, LDST.reg_imm_constrain_unpredictable, LDST.Reg_offset.value, hal,
      Arm.BitVec.lsb] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp [read_gpr, spOf]
  rw [hi] at h1; cases h1; exact h2

theorem pop_d_evs (env : Env) {n : Nat} (hn : n < 32) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.fpuLoad .size64 (.v n) (.spPostIndexed 16)).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.fpuLoad .size64 (.v n) (.spPostIndexed 16)).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, ldstFields, Insn.armFields.fpLdstSize,
        Reg.encV, show n ≤ 31 by omega, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, immEvs, LDST.reg_imm_constrain_unpredictable, LDST.Reg_offset.value, hal,
      Arm.BitVec.lsb, show Arm.LDST.supported_simd_reg_imm 3#2 1#2 = true by decide] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp [read_gpr, spOf]
  rw [hi] at h1; cases h1; exact h2

theorem pop_xx_evs (env : Env) {a b : Nat} (ha : a < 29) (hb : b < 29) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.ldp (.x a) (.x b) (.spPostIndexed 16)).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.ldp (.x a) (.x b) (.spPostIndexed 16)).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm,
        Reg.encZR, show a ≤ 30 by omega, show b ≤ 30 by omega, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp [read_gpr, spOf]
  rw [hi] at h1; cases h1; exact h2

theorem pop_dd_evs (env : Env) {a b : Nat} (ha : a < 32) (hb : b < 32) (s : ArmState)
    (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.fpuLoadP .size64 (.v a) (.v b) (.spPostIndexed 16)).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s := by
  obtain ⟨i', h1, h2⟩ : ∃ i', (Insn.fpuLoadP .size64 (.v a) (.v b) (.spPostIndexed 16)).toArmInst env = .ok i' ∧
      ∀ e ∈ instEvs i' s, e.addr = spOf s := by
    refine ⟨_, by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Insn.armFields.fpOpc,
        ScalarSize.bytes, Reg.encV, show a ≤ 31 by omega, show b ≤ 31 by omega, sField]; rfl, ?_⟩
    have hal' := spAligned hal
    intro e he
    simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
    first | subst he | obtain ⟨-, rfl⟩ := he
    simp [read_gpr, spOf]
  rw [hi] at h1; cases h1; exact h2

/-- The push of one register writes at `sp - 16`. -/
theorem push1_evs (env : Env) {int : Bool} {r : Reg} (hr : PushReg int r) (s : ArmState)
    (hal : CheckSPAlignment s) {a : ArmInst}
    (h : (if int then Insn.store .store64 r (.spPreIndexed (-16))
        else Insn.fpuStore .size64 r (.spPreIndexed (-16))).toArmInst env = .ok a) :
    ∀ e ∈ instEvs a s, e.addr = spOf s - 16#64 := by
  cases r with
  | x n => obtain ⟨rfl, hn⟩ := hr; exact push_x_evs env hn s hal h
  | v n => obtain ⟨rfl, hn⟩ := hr; exact push_d_evs env hn s hal h
  | _ => exact hr.elim

/-- The push of a pair writes at `sp - 16`. -/
theorem push2_evs (env : Env) {int : Bool} {a b : Reg} (ha : PushReg int a) (hb : PushReg int b)
    (s : ArmState) (hal : CheckSPAlignment s) {i : ArmInst}
    (h : (if int then Insn.stp a b (.spPreIndexed (-16))
        else Insn.fpuStoreP .size64 a b (.spPreIndexed (-16))).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s - 16#64 := by
  cases a with
  | x n =>
    cases b with
    | x m => obtain ⟨rfl, hn⟩ := ha; exact push_xx_evs env hn hb.2 s hal h
    | v m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | _ => exact hb.elim
  | v n =>
    cases b with
    | x m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | v m => obtain ⟨rfl, hn⟩ := ha; exact push_dd_evs env hn hb.2 s hal h
    | _ => exact hb.elim
  | _ => exact ha.elim

/-- The pop of one register reads at `sp`. -/
theorem pop1_evs (env : Env) {int : Bool} {r : Reg} (hr : PushReg int r) (s : ArmState)
    (hal : CheckSPAlignment s) {a : ArmInst}
    (h : (if int then Insn.load .uload64 r (.spPostIndexed 16)
        else Insn.fpuLoad .size64 r (.spPostIndexed 16)).toArmInst env = .ok a) :
    ∀ e ∈ instEvs a s, e.addr = spOf s := by
  cases r with
  | x n => obtain ⟨rfl, hn⟩ := hr; exact pop_x_evs env hn s hal h
  | v n => obtain ⟨rfl, hn⟩ := hr; exact pop_d_evs env hn s hal h
  | _ => exact hr.elim

/-- The pop of a pair reads at `sp`. -/
theorem pop2_evs (env : Env) {int : Bool} {a b : Reg} (ha : PushReg int a) (hb : PushReg int b)
    (s : ArmState) (hal : CheckSPAlignment s) {i : ArmInst}
    (h : (if int then Insn.ldp a b (.spPostIndexed 16)
        else Insn.fpuLoadP .size64 a b (.spPostIndexed 16)).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s := by
  cases a with
  | x n =>
    cases b with
    | x m => obtain ⟨rfl, hn⟩ := ha; exact pop_xx_evs env hn hb.2 s hal h
    | v m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | _ => exact hb.elim
  | v n =>
    cases b with
    | x m => obtain ⟨rfl, -⟩ := ha; exact absurd hb.1 (by simp)
    | v m => obtain ⟨rfl, hn⟩ := ha; exact pop_dd_evs env hn hb.2 s hal h
    | _ => exact hb.elim
  | _ => exact ha.elim

/-! ## Lines -/

/-- The events of `A ++ B`: those of `A`, then those of `B` from `A`'s end state. -/
theorem linesEvs_append_steps : ∀ {env : Env} {A : List Line} (B : List Line) {s s1 : ArmState},
    StepsOk env A s s1 →
    linesEvs env (A ++ B) s =
      linesEvs env A s ++ linesEvs { env with pc := env.pc + 4 * A.length } B s1
  | env, [], B, s, s1, h => by
    simp only [StepsOk] at h; subst h
    simp [linesEvs]
  | env, .ins i t :: A, B, s, s1, h => by
    obtain ⟨ai, ha, hpc, -, -, h⟩ := h
    have ih := linesEvs_append_steps (env := { env with pc := env.pc + 4 }) B h
    simp only [List.cons_append, linesEvs, ha, hpc, ite_true]
    rw [ih, List.append_assoc]
    simp only [List.length_cons]
    congr 3
    cases env; simp; omega
  | _, .label _ :: _, _, _, _, h => h.elim
  | _, .word _ _ :: _, _, _, _, h => h.elim

/-- The first line's events, then the rest's. -/
theorem linesEvs_cons_of {env : Env} {x : Insn} {t : Option Clif.TrapCode} {ls : List Line}
    {s : ArmState} {a : ArmInst} (ha : x.toArmInst env = .ok a)
    (hpc : Arm.r .PC (Arm.exec_inst a s) = Arm.r .PC s + 4#64) :
    linesEvs env (.ins x t :: ls) s =
      instEvs a s ++ linesEvs { env with pc := env.pc + 4 } ls (Arm.exec_inst a s) := by
  simp only [linesEvs, ha, hpc, ite_true]

/-- Every event of lines `ls` run from `s` is at an address `B + k`, `k < n`. -/
def EvsIn (env : Env) (ls : List Line) (s : ArmState) (B : BitVec 64) (n : Nat) : Prop :=
  ∀ e ∈ linesEvs env ls s, ∃ k < n, e.addr = B + BitVec.ofNat 64 k

/-- **The pair pushes** from `sp = B + 16 len` write in `[B, B + 16 len)`. -/
theorem pushPairs_evs (env : Env) (int : Bool) : ∀ (ps : List (Reg × Reg)) (s : ArmState)
    (B : BitVec 64), (∀ p ∈ ps, PushReg int p.1 ∧ PushReg int p.2) → 16 * ps.length < 2 ^ 64 →
    B.toNat % 16 = 0 → spOf s = B + BitVec.ofNat 64 (16 * ps.length) →
    EvsIn env (ps.reverse.map (pushLine2 int)) s B (16 * ps.length)
  | [], s, B, _, _, _, _ => fun e he => by simp [linesEvs] at he
  | p :: ps, s, B, hps, hlen, hB, hsp => by
    simp only [List.length_cons] at hlen hsp ⊢
    have hsp' : spOf s = (B + 16#64) + BitVec.ofNat 64 (16 * ps.length) := by
      rw [hsp, show 16 * (ps.length + 1) = 16 + 16 * ps.length by omega, BitVec.ofNat_add,
        BitVec.add_assoc]
    have hps' : ∀ q ∈ ps, PushReg int q.1 ∧ PushReg int q.2 :=
      fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have hB1 : (B + 16#64).toNat % 16 = 0 := by simpa using aligned_add hB 1
    obtain ⟨s1, h1, hsp1, -⟩ := pushPairs_ok env int ps s (B + 16#64) hps' (by omega) hB1 hsp'
    have ih := pushPairs_evs env int ps s (B + 16#64) hps' (by omega) hB1 hsp'
    have hal1 : CheckSPAlignment s1 := checkSP_of (by rw [hsp1]; exact hB1)
    obtain ⟨i, hi, -⟩ := exec_push2 { env with pc := env.pc + 4 * (ps.reverse.map (pushLine2 int)).length }
      (hps p (by simp)).1 (hps p (by simp)).2 s1 hal1
    intro e he
    rw [List.reverse_cons, List.map_append, linesEvs_append_steps _ h1, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨k, hk, hk'⟩ := ih e he
      refine ⟨16 + k, by omega, ?_⟩
      rw [hk', show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]
    · simp only [List.map_cons, List.map_nil, pushLine2] at he
      rw [VCodeAddr.linesEvs_single hi] at he
      refine ⟨0, by omega, ?_⟩
      rw [push2_evs _ (hps p (by simp)).1 (hps p (by simp)).2 s1 hal1 hi e he, hsp1]
      simp [BitVec.add_sub_cancel]

/-- **The pushes of one register class** from `sp = B + pushBytes` write in
`[B, B + pushBytes)`. -/
theorem pushLines_evs (env : Env) (int : Bool) (rs : List Reg) (s : ArmState) (B : BitVec 64)
    (hrs : ∀ r ∈ rs, PushReg int r) (hlen : rs.length ≤ 64) (hB : B.toNat % 16 = 0)
    (hsp : spOf s = B + BitVec.ofNat 64 (pushBytes rs.length)) :
    EvsIn env (pushLines int rs) s B (pushBytes rs.length) := by
  have hl := pairsOf_len rs
  have hpb := pushBytes_eq rs
  obtain ⟨hmP, hmO⟩ := pairsOf_mem rs
  have hpv : ∀ p ∈ (pairsOf rs).1, PushReg int p.1 ∧ PushReg int p.2 :=
    fun p hp => ⟨hrs _ (hmP p hp).1, hrs _ (hmP p hp).2⟩
  have hPl : 16 * (pairsOf rs).1.length < 2 ^ 64 := by split at hl <;> omega
  rw [pushLines_eq]
  rcases ho : (pairsOf rs).2 with _ | r0
  · simp only [ho, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hpb
    rw [hpb] at hsp ⊢
    intro e he
    simp only [List.nil_append] at he
    exact pushPairs_evs env int _ s B hpv hPl hB hsp e he
  · simp only [ho, Option.isSome_some, ite_true] at hpb
    rw [hpb] at hsp ⊢
    have hr0 : PushReg int r0 := hrs _ (hmO r0 ho)
    have hal : CheckSPAlignment s := checkSP_of (by
      rw [hsp, show 16 * (pairsOf rs).1.length + 16 = 16 * ((pairsOf rs).1.length + 1) by omega]
      exact aligned_add hB _)
    obtain ⟨i0, hi0, he0⟩ := exec_push1 env hr0 s hal
    obtain ⟨f1, f2, f3, f4, -⟩ := pushSt_facts s 8 (slotVal s r0)
    have hsp1 : spOf (Arm.exec_inst i0 s) = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length) := by
      rw [he0, f4, hsp, show 16 * (pairsOf rs).1.length + 16 = 16 * ((pairsOf rs).1.length + 1) by omega]
      exact add16_sub _ _
    have hT : spOf s - 16#64 = B + BitVec.ofNat 64 (16 * (pairsOf rs).1.length) := by
      rw [← hsp1, he0, f4]
    have h1 : StepsOk env [.ins (if int then .store .store64 r0 (.spPreIndexed (-16))
        else .fpuStore .size64 r0 (.spPreIndexed (-16))) none] s (Arm.exec_inst i0 s) :=
      steps_cons hi0 (by rw [he0]; exact f1) (by rw [he0]; exact f2) (by rw [he0]; exact f3) rfl
    intro e he
    rw [linesEvs_append_steps _ h1, List.mem_append] at he
    rcases he with he | he
    · rw [VCodeAddr.linesEvs_single hi0] at he
      refine ⟨16 * (pairsOf rs).1.length, by omega, ?_⟩
      rw [push1_evs env hr0 s hal hi0 e he, hT]
    · obtain ⟨k, hk, hk'⟩ := pushPairs_evs _ int _ _ B hpv hPl hB hsp1 e he
      exact ⟨k, by omega, hk'⟩

/-- **The pair pops** from `sp = B` read in `[B, B + 16 len)`. -/
theorem popPairs_evs (env : Env) (int : Bool) : ∀ (ps : List (Reg × Reg)) (s : ArmState)
    (B : BitVec 64), (∀ p ∈ ps, PushReg int p.1 ∧ PushReg int p.2) →
    (ps.flatMap fun p => [p.1, p.2]).Nodup → B.toNat % 16 = 0 → spOf s = B →
    EvsIn env (ps.map (popLine2 int)) s B (16 * ps.length)
  | [], s, B, _, _, _, _ => fun e he => by simp [linesEvs] at he
  | p :: ps, s, B, hps, hnd, hB, hsp => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    obtain ⟨⟨hne, -⟩, -, hnd⟩ := hnd
    have hp := hps p (by simp)
    have hal : CheckSPAlignment s := checkSP_of (by rw [hsp]; exact hB)
    obtain ⟨i, hi, f1, f2, f3, f4, -⟩ := exec_pop2 env hp.1 hp.2 hne s hal
    have ih := popPairs_evs { env with pc := env.pc + 4 } int ps (Arm.exec_inst i s) (B + 16#64)
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hnd (by simpa using aligned_add hB 1)
      (by rw [f4, hsp])
    have h1 : StepsOk env [popLine2 int p] s (Arm.exec_inst i s) := steps_cons hi f1 f2 f3 rfl
    intro e he
    rw [List.map_cons, show popLine2 int p :: ps.map (popLine2 int) =
      [popLine2 int p] ++ ps.map (popLine2 int) from rfl, linesEvs_append_steps _ h1,
      List.mem_append] at he
    simp only [List.length_cons, List.length_nil] at he ⊢
    rcases he with he | he
    · simp only [popLine2] at he
      rw [VCodeAddr.linesEvs_single hi] at he
      refine ⟨0, by omega, ?_⟩
      rw [pop2_evs env hp.1 hp.2 s hal hi e he, hsp]
      simp
    · obtain ⟨k, hk, hk'⟩ := ih e (by simpa using he)
      refine ⟨16 + k, by omega, ?_⟩
      rw [hk', show (16#64) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]

/-- **The pops of one register class** from `sp = B` read in `[B, B + pushBytes)`. -/
theorem popLines_evs (env : Env) (int : Bool) (rs : List Reg) (s : ArmState) (B : BitVec 64)
    (hrs : ∀ r ∈ rs, PushReg int r) (hnd : rs.Nodup) (hB : B.toNat % 16 = 0) (hsp : spOf s = B) :
    EvsIn env (popLines int rs) s B (pushBytes rs.length) := by
  have hl := pairsOf_len rs
  have hpb := pushBytes_eq rs
  have hfl := pairsOf_flat rs
  obtain ⟨hmP, hmO⟩ := pairsOf_mem rs
  have hpv : ∀ p ∈ (pairsOf rs).1, PushReg int p.1 ∧ PushReg int p.2 :=
    fun p hp => ⟨hrs _ (hmP p hp).1, hrs _ (hmP p hp).2⟩
  have hndP : ((pairsOf rs).1.flatMap fun p => [p.1, p.2]).Nodup := by
    rw [← hfl] at hnd; exact (List.nodup_append.1 hnd).1
  obtain ⟨s1, h1, h2, -⟩ := popPairs_ok env int _ s B hpv hndP hB hsp
  have hP := popPairs_evs env int _ s B hpv hndP hB hsp
  rw [popLines_eq]
  intro e he
  rw [linesEvs_append_steps _ h1, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨k, hk, hk'⟩ := hP e he
    exact ⟨k, by split at hpb <;> omega, hk'⟩
  · rcases ho : (pairsOf rs).2 with _ | r0
    · simp only [ho] at he; simp [linesEvs] at he
    · simp only [ho] at he
      simp only [ho, Option.isSome_some, ite_true] at hpb
      have hr0 : PushReg int r0 := hrs _ (hmO r0 ho)
      have hal1 : CheckSPAlignment s1 := checkSP_of (by rw [h2]; exact aligned_add hB _)
      obtain ⟨i0, hi0, -⟩ :=
        exec_pop1 { env with pc := env.pc + 4 * ((pairsOf rs).1.map (popLine2 int)).length } hr0 s1 hal1
      rw [VCodeAddr.linesEvs_single hi0] at he
      refine ⟨16 * (pairsOf rs).1.length, by omega, ?_⟩
      rw [pop1_evs _ hr0 s1 hal1 hi0 e he, h2]

/-! ## The stack probes (#581) -/

/-- **A stack probe's `stur wzr, [sp]`**: one plain write at `sp`. -/
theorem stur_wzr_evs (env : Env) (s : ArmState) (hal : CheckSPAlignment s) {i : ArmInst}
    (hi : (Insn.store .store32 .xzr (.unscaled .sp 0)).toArmInst env = .ok i) :
    ∀ e ∈ instEvs i s, e.addr = spOf s := by
  have e : (Insn.store .store32 .xzr (.unscaled .sp 0)).toArmInst env = .ok
      (.LDST (.Reg_unscaled_imm
        { size := 2#2, VR := 0#1, opc := 0#2, imm9 := 0#9, Rn := 31#5, Rt := 31#5 })) := by
    simp [csimp_rules, pure, Except.pure]; rfl
  have e2 : (.LDST (.Reg_unscaled_imm
      { size := 2#2, VR := 0#1, opc := 0#2, imm9 := 0#9, Rn := 31#5, Rt := 31#5 }) : ArmInst) =
      unscInst 2#2 0#2 0#9 31#5 31#5 := rfl
  rw [e, e2, Except.ok.injEq] at hi
  subst hi
  rw [VCodeAddr.instEvs_unsc]
  intro ev hev
  rw [(VCodeAddr.immEvs_store .store32 (by decide) 31#5 31#5 _ s (fun _ => hal) ev hev).2.1]
  simp [Arm.LDST.Reg_offset.value, read_gpr, spOf]

/-- **`k` unrolled probes** from an aligned `sp` write at the probed bytes (`probeHitB`). -/
theorem probeSteps_evs : ∀ (k : Nat) (env : Env) (s : ArmState), (spOf s).toNat % 16 = 0 →
    ∀ e ∈ linesEvs env (probeSteps k) s, probeHitB k (spOf s) e.addr = true
  | 0, _, _, _ => fun e he => by simp [probeSteps, linesEvs] at he
  | k + 1, env, s, hal => by
    obtain ⟨a1, ha1, he1⟩ := exec_sub_sp_imm env ⟨1, true⟩ (by decide) s
    have hpc1 : Arm.r .PC (Arm.exec_inst a1 s) = Arm.r .PC s + 4#64 := by
      rw [he1]; simp [Arm.r_of_w_same, Arm.r_of_w_different]
    have hsp1 : spOf (Arm.exec_inst a1 s) = spOf s - 4096#64 := by
      rw [he1]; simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different, Imm12.value]
    have hal1 : (spOf (Arm.exec_inst a1 s)).toNat % 16 = 0 := by
      rw [hsp1]; exact aligned_sub hal (n := 4096) (by decide) (by decide)
    obtain ⟨a2, ha2, he2⟩ := exec_stur_wzr_sp { env with pc := env.pc + 4 } (Arm.exec_inst a1 s)
      (checkSP_of hal1)
    have hpc2 : Arm.r .PC (Arm.exec_inst a2 (Arm.exec_inst a1 s)) =
        Arm.r .PC (Arm.exec_inst a1 s) + 4#64 := by
      rw [he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different, Arm.r_of_write_mem_bytes]
    have hsp2 : spOf (Arm.exec_inst a2 (Arm.exec_inst a1 s)) = spOf s - 4096#64 := by
      rw [he2, ← hsp1]; simp [spOf, Arm.r_of_w_different, Arm.r_of_write_mem_bytes]
    have hal2 : (spOf (Arm.exec_inst a2 (Arm.exec_inst a1 s))).toNat % 16 = 0 := by
      rw [hsp2, ← hsp1]; exact hal1
    intro e he
    simp only [probeSteps, List.cons_append, List.nil_append] at he
    rw [linesEvs_cons_of ha1 hpc1, instEvs_none ha1 rfl, List.nil_append,
      linesEvs_cons_of ha2 hpc2, List.mem_append] at he
    rw [probeHitB_succ]
    rcases he with he | he
    · rw [stur_wzr_evs _ _ (checkSP_of hal1) ha2 e he, hsp1]
      simp
    · rw [← hsp2, probeSteps_evs k _ _ hal2 e he, Bool.or_true]

/-- **The stack probes' events** from an aligned `sp`: at the probed bytes (`probeHitB`). -/
theorem probeLines_evs (env : Env) (total : Nat) (s : ArmState) (hal : (spOf s).toNat % 16 = 0) :
    ∀ e ∈ linesEvs env (probeLines total) s, probeHitB (probeCount total) (spOf s) e.addr = true := by
  unfold probeLines
  simp only
  by_cases h0 : probeCount total = 0
  · simp only [h0, beq_self_eq_true, ite_true]
    intro e he; simp [linesEvs] at he
  simp only [show (probeCount total == 0) = false by simpa using h0, Bool.false_eq_true, ite_false]
  obtain ⟨s1, h1, -⟩ := probeSteps_ok (probeCount total) env s hal
  have hadd : ∀ (env' : Env) (t : ArmState), linesEvs env'
      [Line.ins (.aluImm12 .add true .sp .sp ⟨probeCount total, true⟩) none] t = [] :=
    fun _ t => mv_linesEvs_nil t rfl
  intro e he
  rw [linesEvs_append_steps _ h1, hadd, List.append_nil] at he
  exact probeSteps_evs _ env s hal e he

/-! ## The frame -/

/-- **The prologue's events** are in fp/lr and the clobber area,
`[sp₀ - 16 - clobberBytes, sp₀)`, or at the bytes the stack probes zero (`probeHitN`).
(#581: the former statement, every event in `[sp₀ - 16 - clobberBytes, sp₀)` (`EvsIn`), became
false with Cranelift's inline stack probes: for a frame of at least 4 KiB their `stur wzr` writes
4096 bytes and more below fp/lr; `calls` is the new argument of `prologueLines`.) -/
theorem prologue_evsIn (env : Env) {saves : List Reg} {size : Nat} {calls : Bool}
    (hs : size < 2 ^ 64) (hsv : SavesOk saves) (hcb : clobberBytes saves ≤ size) (s : Arm.ArmState)
    (hal : (spOf s).toNat % 16 = 0) :
    ∀ e ∈ linesEvs env (prologueLines saves size calls) s,
      (∃ k < 16 + clobberBytes saves,
        e.addr = spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) + BitVec.ofNat 64 k) ∨
      probeHitN (probeCount (probeTotal size calls)) (spOf s) e.addr = true := by
  have hcbm := clobberBytes_mod saves
  have hcbl := hsv.clobber_le
  have hpIm := pushBytes_mod (savesInt saves).length
  have hpFm := pushBytes_mod (savesFloat saves).length
  have hcbe : clobberBytes saves =
      pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length := rfl
  generalize hBF : spOf s - BitVec.ofNat 64 (16 + clobberBytes saves) = BF
  have hBFa : BF.toNat % 16 = 0 := by rw [← hBF]; exact aligned_sub hal (by omega) (by omega)
  have hBIa : (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)).toNat % 16 = 0 := by
    rw [show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16) by omega]
    exact aligned_add hBFa _
  have hT16 : spOf s - 16#64 = BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length) +
      BitVec.ofNat 64 (pushBytes (savesInt saves).length) := by
    rw [← hBF, hcbe, show 16 + (pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length) =
      16 + pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length by omega,
      BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  -- fp/lr and `mov x29, sp`
  have hal0 : Arm.CheckSPAlignment s := checkSP_of hal
  obtain ⟨a1, ha1, he1⟩ := exec_stp_fplr env s hal0
  obtain ⟨a2, ha2, he2⟩ := exec_mov_fp_sp { env with pc := env.pc + 4 } (Arm.exec_inst a1 s)
  have hpc1 : Arm.r .PC (Arm.exec_inst a1 s) = Arm.r .PC s + 4#64 := by
    rw [he1]; simp [Arm.r_of_w_same]
  have hpc2 : Arm.r .PC (Arm.exec_inst a2 (Arm.exec_inst a1 s)) =
      Arm.r .PC (Arm.exec_inst a1 s) + 4#64 := by
    rw [he2]; simp [Arm.r_of_w_same, Arm.r_of_w_different]
  generalize hs1 : Arm.exec_inst a1 s = s1 at he2 ha2 hpc2
  generalize hs2 : Arm.exec_inst a2 s1 = s2
  have hsp1 : spOf s1 = spOf s - 16#64 := by
    rw [← hs1, he1]; simp [spOf, Arm.r_of_w_same, Arm.r_of_w_different]
  have hsp2 : spOf s2 = spOf s - 16#64 := by
    rw [← hs2, he2]; simp only [spOf] at hsp1 ⊢; simp [Arm.r_of_w_different, hsp1]
  -- the pushes and the `sp` adjustment
  have hrest : ∀ (env2 : Env) (t : ArmState), spOf t = spOf s - 16#64 →
      EvsIn env2 (pushLines true (savesInt saves) ++
        (pushLines false (savesFloat saves) ++ spAdjLines true (size - clobberBytes saves))) t BF
        (clobberBytes saves) := by
    intro env2 t hspt e he
    obtain ⟨s3, h3, hsp3, -⟩ := pushLines_ok env2 true (savesInt saves) t
      (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)) hsv.int
      (by have := hsv.intLen; omega) hBIa (by rw [hspt, hT16])
    rw [linesEvs_append_steps _ h3, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨k, hk, hk'⟩ := pushLines_evs env2 true (savesInt saves) t
        (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)) hsv.int
        (by have := hsv.intLen; omega) hBIa (by rw [hspt, hT16]) e he
      exact ⟨pushBytes (savesFloat saves).length + k, by omega, by rw [hk', add_ofNat_add]⟩
    · obtain ⟨s4, h4, -⟩ := pushLines_ok _ false (savesFloat saves) s3 BF hsv.float
        (by have := hsv.floatLen; omega) hBFa hsp3
      rw [linesEvs_append_steps _ h4, List.mem_append] at he
      rcases he with he | he
      · obtain ⟨k, hk, hk'⟩ := pushLines_evs _ false (savesFloat saves) s3 BF hsv.float
          (by have := hsv.floatLen; omega) hBFa hsp3 e he
        exact ⟨k, by omega, hk'⟩
      · rw [mv_linesEvs_nil _ (kinds_spAdjLines _ _)] at he
        exact absurd he List.not_mem_nil
  -- the stack probes, then the rest
  have hal2 : (spOf s2).toNat % 16 = 0 := by
    rw [hsp2]; exact aligned_sub hal (by decide) (by decide)
  have hprest : ∀ env2 : Env, ∀ e ∈ linesEvs env2 (probeLines (probeTotal size calls) ++
      (pushLines true (savesInt saves) ++
        (pushLines false (savesFloat saves) ++ spAdjLines true (size - clobberBytes saves)))) s2,
      (∃ k < clobberBytes saves, e.addr = BF + BitVec.ofNat 64 k) ∨
        probeHitN (probeCount (probeTotal size calls)) (spOf s) e.addr = true := by
    intro env2 e he
    obtain ⟨sP, hP, hspP, -⟩ := probeLines_ok env2 (probeTotal size calls) s2 hal2
    rw [linesEvs_append_steps _ hP, List.mem_append] at he
    rcases he with he | he
    · right
      have h := probeLines_evs env2 (probeTotal size calls) s2 hal2 e he
      rwa [hsp2] at h
    · exact .inl (hrest _ sP (by rw [hspP, hsp2]) e he)
  intro e he
  rw [prologueLines_eq, List.cons_append, List.cons_append, List.nil_append,
    linesEvs_cons_of ha1 hpc1, hs1, linesEvs_cons_of ha2 hpc2, hs2,
    instEvs_none ha2 rfl, List.nil_append, List.mem_append] at he
  rcases he with he | he
  · left
    obtain ⟨a', ha', -, hev⟩ := stp_fplr_evs env s hal0
    rw [ha1] at ha'; cases ha'
    refine ⟨clobberBytes saves, by omega, ?_⟩
    rw [(hev e he).1, hT16, add_ofNat_add, hcbe, Nat.add_comm (pushBytes _)]
  · rcases hprest _ e he with ⟨k, hk, hk'⟩ | h
    · exact .inl ⟨k, by omega, hk'⟩
    · exact .inr h

/-- **The epilogue's events** (before the `ret`) are in the clobber area and fp/lr,
`[sp + size - clobberBytes, sp + size + 16)` from the body's `sp`. -/
theorem epilogue_evsIn (env : Env) {saves : List Reg} {size : Nat} (hs : size < 2 ^ 64)
    (hsv : SavesOk saves) (hcb : clobberBytes saves ≤ size) (s : Arm.ArmState)
    (hal : (spOf s + BitVec.ofNat 64 (size - clobberBytes saves)).toNat % 16 = 0) :
    EvsIn env (epiLines saves size) s (spOf s + BitVec.ofNat 64 (size - clobberBytes saves))
      (clobberBytes saves + 16) := by
  have hcbm := clobberBytes_mod saves
  have hcbl := hsv.clobber_le
  have hpIm := pushBytes_mod (savesInt saves).length
  have hpFm := pushBytes_mod (savesFloat saves).length
  have hcbe : clobberBytes saves =
      pushBytes (savesInt saves).length + pushBytes (savesFloat saves).length := rfl
  obtain ⟨s1, h1, hsp1, -⟩ := spAdj_ok env false (size := size - clobberBytes saves) (by omega) s
  simp only [Bool.false_eq_true, ite_false] at hsp1
  generalize hBF : spOf s + BitVec.ofNat 64 (size - clobberBytes saves) = BF at hsp1 hal
  obtain ⟨s2, h2, hsp2, -⟩ := popLines_ok
    { env with pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length } false
    (savesFloat saves) s1 BF hsv.float (hsv.2.filter _) hal hsp1
  have hBIa : (BF + BitVec.ofNat 64 (pushBytes (savesFloat saves).length)).toNat % 16 = 0 := by
    rw [show pushBytes (savesFloat saves).length = 16 * (pushBytes (savesFloat saves).length / 16) by omega]
    exact aligned_add hal _
  obtain ⟨s3, h3, hsp3, -⟩ := popLines_ok
    { env with pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length +
      4 * (popLines false (savesFloat saves)).length } true
    (savesInt saves) s2 _ hsv.int (hsv.2.filter _) hBIa hsp2
  have hal3 : Arm.CheckSPAlignment s3 := checkSP_of (by
    rw [hsp3, show pushBytes (savesInt saves).length = 16 * (pushBytes (savesInt saves).length / 16) by omega]
    exact aligned_add hBIa _)
  intro e he
  simp only [epiLines] at he
  rw [linesEvs_append_steps _ h1, mv_linesEvs_nil _ (kinds_spAdjLines _ _), List.nil_append,
    linesEvs_append_steps _ h2, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨k, hk, hk'⟩ := popLines_evs _ false (savesFloat saves) s1 BF hsv.float (hsv.2.filter _)
      hal hsp1 e he
    exact ⟨k, by omega, hk'⟩
  rw [linesEvs_append_steps _ h3, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨k, hk, hk'⟩ := popLines_evs _ true (savesInt saves) s2 _ hsv.int (hsv.2.filter _)
      hBIa hsp2 e he
    exact ⟨pushBytes (savesFloat saves).length + k, by omega, by rw [hk', add_ofNat_add]⟩
  · obtain ⟨a4, ha4, -, hev⟩ := ldp_fplr_evs
      { { env with pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length } with
        pc := env.pc + 4 * (spAdjLines false (size - clobberBytes saves)).length +
          4 * (popLines false (savesFloat saves)).length +
          4 * (popLines true (savesInt saves)).length } s3 hal3
    rw [VCodeAddr.linesEvs_single ha4] at he
    refine ⟨clobberBytes saves, by omega, ?_⟩
    rw [(hev e he).1, hsp3, add_ofNat_add, hcbe, Nat.add_comm (pushBytes _)]

/-! ## The prologue's fields -/

/-- **The prologue keeps every field but the pc, x29, `sp` and x16.** -/
theorem prologue_fields {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) :
    ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
      Arm.r f (iterN R.step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0) = Arm.r f R.s0 := by
  obtain ⟨-, hfs, -, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, -, -, ho', -⟩ :=
    prologue_ok (calls := R.af.isCaller) (R.envOf 1) hs hsv (by rw [hfs]; exact hcb) R.s0 hent.spAligned
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, -, -, -⟩ := iterN_steps hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  rw [hiter]
  exact ho'

/-- A callee-saved register's value depends on fields other than the pc, x16, x29, x30 and
`sp`. -/
theorem regVal_calleeSaved_congr {s t : ArmState}
    (h : ∀ f, f ≠ .PC → f ≠ .GPR 16#5 → f ≠ .GPR 29#5 → f ≠ .GPR 30#5 → f ≠ .GPR 31#5 →
      Arm.r f s = Arm.r f t) :
    ∀ r ∈ calleeSaved, regVal s r = regVal t r := by
  intro r hr
  simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have hne : ∀ n, n < 32 → n ≠ 19 + i →
        StateField.GPR (rnum (19 + i)) ≠ StateField.GPR (BitVec.ofNat 5 n) := by
      intro n hn hni he
      injection he with he'
      have := congrArg BitVec.toNat he'
      simp [rnum] at this
      omega
    simp only [regVal]
    rw [h _ (by simp) (hne 16 (by omega) (by omega)) (hne 29 (by omega) (by omega))
      (hne 30 (by omega) (by omega)) (hne 31 (by omega) (by omega))]
  · simp only [regVal]
    exact h _ (by simp) (by simp) (by simp) (by simp) (by simp)

end Concurrency.ArmAllocThread

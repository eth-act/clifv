import FV.Backend.Proof.RegallocSound
import FV.Backend.Encode
import FV.Arm.Exec

/-!
# The operand-view obligation `OperandsSound` against the Arm model (M6 proof)

`checkAlloc_sound` holds for every instruction semantics `sem`. To use it for the emitted
code, the abstract step of an original instruction (`MStep.op`: read the uses from their
locations, write the defs, havoc the clobbers) must describe what the *emitted* instruction
does. This file states that obligation against the Arm model and discharges it for a
representative set of instructions.

Concrete setting:

* values `CV = BitVec 128`; an X register holds its 64 bits zero-extended (`regVal`);
* `ckeep`: the callee-preserved part (all of an X register, the low 64 bits of a V register);
* the world is the Arm state itself, compared with `SameWorld F` — equal outside the
  allocatable registers, the emitter temporaries x16/x17, the pc (`Masked`) and the frame
  addresses `F` (spill and save slots, which the location store models);
* the emitted instruction `i'` (`MInst.assign i regs`) runs as `execMInst`: its expansion
  `MInst.lines` → `Insn.toArmInst` → `Arm.exec_inst` (what the encoder's words decode to, M5).

`OperandsSound F sem i`: for every register allocation the checker's static checks accept,
from every state, if `sem` gives defs `outs`, world `w'` and falls through, the emitted code
produces a state with the same world as `w'`, `outs` in the def registers, every other
allocatable register unchanged except the clobbers, whose callee-saved part survives.
`operandsSound_step` turns that into the store of `MStep.op` (with `ckeep`, the clobber
havoc chosen from the concrete state), which is how the concrete execution plugs into
`checkAlloc_sound`.

Proven here for `csem` (a value-level semantics of the instructions below, stated with the
Arm model's own operations): `mov` (64-bit), `add` (register, 64-bit), `add` (imm12,
64-bit), `csel`, `cset`, `ldr x` / `str x` (unsigned-offset address), and calls under the
AAPCS64 callee contract `CalleeSound`.
-/

namespace Backend.Proof

open Backend

/-- Values of the concrete instance: 128 bits (an X register zero-extended). -/
abbrev CV := BitVec 128

/-- The Arm model's register number of `x n` / `v n`. -/
def rnum (n : Nat) : BitVec 5 := BitVec.ofNat 5 n

/-- The value an Arm state holds in a register location. -/
def regVal (s : Arm.ArmState) : Reg → CV
  | .x n => (Arm.r (.GPR (rnum n)) s).setWidth 128
  | .v n => Arm.r (.SFP (rnum n)) s
  | _ => 0

/-- The callee-preserved part of a register (AAPCS64: all of x19–x28, the low 64 bits of
v8–v15). -/
def ckeep : Reg → CV → CV
  | .v _, x => (x.setWidth 64).setWidth 128
  | _, x => x

/-- State fields outside the world: allocatable registers (x0–x15, x19–x28, v0–v31), the
emitter temporaries x16/x17, and the pc (control is matched by code position). -/
def Masked : Arm.StateField → Prop
  | .GPR i => i.toNat < 29 ∧ i.toNat ≠ 18
  | .SFP _ => True
  | .PC => True
  | _ => False

/-- `s` and `t` have the same world: equal on every unmasked field and on memory outside the
frame addresses `F`, same program. -/
def SameWorld (F : BitVec 64 → Prop) (s t : Arm.ArmState) : Prop :=
  (∀ f, ¬ Masked f → Arm.r f s = Arm.r f t) ∧ (∀ a, ¬ F a → s.mem a = t.mem a) ∧
    s.program = t.program

theorem SameWorld.refl (F : BitVec 64 → Prop) (s : Arm.ArmState) : SameWorld F s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem SameWorld.w_left {F} {s t : Arm.ArmState} {f : Arm.StateField} {v} (hf : Masked f)
    (h : SameWorld F s t) : SameWorld F (Arm.w f v s) t := by
  refine ⟨fun g hg => ?_, fun a ha => ?_, ?_⟩
  · have hne : g ≠ f := fun e => hg (e ▸ hf)
    rw [Arm.r_of_w_different hne]; exact h.1 g hg
  · rw [Arm.ArmState.mem_w_eq_mem]; exact h.2.1 a ha
  · rw [Arm.w_program]; exact h.2.2

/-! ## Executing an allocated instruction -/

/-- Run the lines of an instruction expansion (straight-line: instructions only); `env.pc`
advances by 4 per instruction. -/
def execLines : Env → List Line → Arm.ArmState → Option Arm.ArmState
  | _, [], s => some s
  | env, .ins i _ :: ls, s =>
    match i.toArmInst env with
    | .ok ai => execLines { env with pc := env.pc + 4 } ls (Arm.exec_inst ai s)
    | .error _ => none
  | _, _ :: _, _ => none

/-- Execute an allocated (real-register) instruction: its expansion, encoded and executed by
the Arm model. -/
def execMInst (ctx : FnCtx) (env : Env) (i : MInst) (s : Arm.ArmState) : Option Arm.ArmState :=
  match i.lines ctx {} with
  | .ok (ls, _) => execLines env ls s
  | .error _ => none

/-- The use values of an instruction whose operands `ops` are allocated to `regs`, in state `s`. -/
def useVals (ops : Array Operand) (regs : Array Reg) (s : Arm.ArmState) : List CV :=
  ((ops.zip regs).toList.filter (·.1.isUse)).map (regVal s ·.2)

/-- The def operands of an instruction allocated to `regs`, paired with values `outs`. -/
def defRegs (ops : Array Operand) (regs : Array Reg) (outs : List CV) : List ((Operand × Reg) × CV) :=
  ((ops.zip regs).toList.filter (·.1.isDef)).zip outs

/-- **The operand-view obligation** for instruction `i` (straight-line outcome `next`). -/
def OperandsSound (F : BitVec 64 → Prop) (exec : MInst → Arm.ArmState → Option Arm.ArmState)
    (sem : ISem CV Arm.ArmState) (i : MInst) : Prop :=
  ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
    (s w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState),
    i.operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
    i.assign regs = .ok i' →
    SameWorld F s w →
    sem i (useVals ops regs s) w = some (outs, w', .next) →
    ∃ s', exec i' s = some s' ∧ SameWorld F s' w' ∧
      (∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ i.clobbers → regVal s' r = regVal s r) ∧
      (∀ r ∈ i.clobbers, r ∈ calleeSaved → ckeep r (regVal s' r) = ckeep r (regVal s r))

deriving instance ReflBEq, LawfulBEq for RegClass
deriving instance ReflBEq, LawfulBEq for Reg

theorem allocatable_iff {r : Reg} : r.allocatable = true ↔
    r ∈ [.x 0, .x 1, .x 2, .x 3, .x 4, .x 5, .x 6, .x 7, .x 8, .x 9, .x 10, .x 11, .x 12, .x 13,
      .x 14, .x 15, .x 19, .x 20, .x 22, .x 23, .x 24, .x 25, .x 26, .x 27, .x 28, .x 21,
      .v 0, .v 1, .v 2, .v 3, .v 4, .v 5, .v 6, .v 7, .v 16, .v 17, .v 18, .v 19, .v 20, .v 21,
      .v 22, .v 23, .v 24, .v 25, .v 26, .v 27, .v 28, .v 29, .v 30, .v 31,
      .v 8, .v 9, .v 10, .v 11, .v 12, .v 13, .v 14, .v 15] := by
  unfold Reg.allocatable
  rw [List.contains_iff_mem]
  rfl

/-- An allocatable register is `x n` (`n < 29`, not x16–x18) or `v n` (`n < 32`). -/
theorem allocatable_cases {r : Reg} (h : r.allocatable = true) :
    (∃ n, r = .x n ∧ n < 29 ∧ n ≠ 16 ∧ n ≠ 17 ∧ n ≠ 18) ∨ (∃ n, r = .v n ∧ n < 32) := by
  rw [allocatable_iff] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> simp

theorem rnum_ne {a b : Nat} (ha : a < 32) (hb : b < 32) (h : a ≠ b) : rnum a ≠ rnum b := by
  intro e
  have := congrArg BitVec.toNat e
  simp [rnum, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

theorem rnum_toNat {a : Nat} (ha : a < 32) : (rnum a).toNat = a := by
  simp [rnum, Nat.mod_eq_of_lt ha]

/-- The state field of a register location. -/
def _root_.Backend.Reg.field : Reg → Option Arm.StateField
  | .x n => some (.GPR (rnum n))
  | .v n => some (.SFP (rnum n))
  | _ => none

theorem regVal_w {s : Arm.ArmState} {f : Arm.StateField} {v} {r : Reg} (h : r.field ≠ some f) :
    regVal (Arm.w f v s) r = regVal s r := by
  cases r <;> simp only [regVal, Reg.field] at h ⊢ <;>
    first | rfl | rw [Arm.r_of_w_different (fun e => h (by rw [e]))]


theorem checkOperand_ok {c : CheckCtx} {wh : String} {ops : Array Operand} {allocs : Array Loc}
    {o : Operand} {l : Loc} {j : Nat} (h : c.checkOperand wh ops allocs ((o, l), j) = .ok ()) :
    c.locOk l o.cls = true ∧ (∀ p, o.con = .fixed p → l = .reg p) := by
  unfold CheckCtx.checkOperand at h
  obtain ⟨h1, h⟩ := Except.seq_ok h
  have h1 := ensure_ok h1
  simp only [Bool.and_eq_true] at h1
  refine ⟨h1.1, fun p hp => ?_⟩
  rw [hp] at h
  simpa using ensure_ok h

/-- What the static checks of an instruction give. -/
theorem checkStatic_facts {c : CheckCtx} {wh : String} {ops : Array Operand} {allocs : Array Loc}
    {clob : List Reg} (h : c.checkStatic wh ops allocs clob = .ok ()) :
    ops.size = allocs.size ∧
    (∀ p ∈ (ops.zip allocs).toList, c.locOk p.2 p.1.cls = true ∧
      ∀ r, p.1.con = .fixed r → p.2 = .reg r) ∧
    (((ops.zip allocs).toList.filter (·.1.kind == .def)).map (·.2)).Nodup ∧
    (∀ p ∈ (ops.zip allocs).toList, p.1.kind = .def → ∀ r ∈ clob, p.2 ≠ .reg r) := by
  unfold CheckCtx.checkStatic at h
  obtain ⟨h1, h⟩ := Except.seq_ok h
  dsimp only at h
  obtain ⟨h2, h⟩ := Except.seq_ok h
  obtain ⟨h3, h⟩ := Except.seq_ok h
  obtain ⟨h4, _⟩ := Except.seq_ok h
  refine ⟨by simpa using ensure_ok h1, ?_, by simpa using ensure_ok h3, ?_⟩
  · intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    have hz : (p, i) ∈ (ops.zip allocs).toList.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
    exact checkOperand_ok (forM_ok h2 (p, i) hz)
  · intro p hp hk r hr e
    have hd : p ∈ (ops.zip allocs).toList.filter (·.1.kind == .def) :=
      List.mem_filter.mpr ⟨hp, by simp [hk]⟩
    have := ensure_ok (forM_ok h4 p hd)
    have hmem : p.2 ∈ defConflicts ((ops.zip allocs).toList.filter (·.1.kind == .use))
        (clob.map Loc.reg) p.1.pos := by
      cases p.1.pos <;> simp [defConflicts, e, hr]
    simp at this
    exact this (by simpa using hmem)

/-- A register location that passes `locOk` for class `int` is an allocatable X register. -/
theorem locOk_int {c : CheckCtx} {r : Reg} (h : c.locOk (.reg r) .int = true) :
    ∃ n, r = .x n ∧ n < 29 ∧ n ≠ 16 ∧ n ≠ 17 ∧ n ≠ 18 := by
  simp only [CheckCtx.locOk, Loc.cls?, Bool.and_eq_true] at h
  rcases allocatable_cases h.2 with ⟨n, rfl, hn⟩ | ⟨n, rfl, _⟩
  · exact ⟨n, rfl, hn⟩
  · simp [Reg.realClass?] at h


theorem Masked_gpr {n : Nat} (h : n < 29) (h18 : n ≠ 18) : Masked (.GPR (rnum n)) := by
  simp only [Masked, rnum_toNat (by omega : n < 32)]; omega

/-- Low 64 bits of a value. -/
def lo64 (x : CV) : BitVec 64 := x.setWidth 64

/-- 64 bits as a value. -/
def ofX (x : BitVec 64) : CV := x.setWidth 128

theorem lo64_regVal_x (s : Arm.ArmState) (n : Nat) : lo64 (regVal s (.x n)) = Arm.r (.GPR (rnum n)) s := by
  simp [lo64, regVal, BitVec.setWidth_setWidth_of_le]

/-- `n` bytes from `a` avoid the frame addresses `F`. -/
def Avoids (F : BitVec 64 → Prop) (n : Nat) (a : BitVec 64) : Prop :=
  ∀ k < n, ¬ F (a + BitVec.ofNat 64 k)

open Classical in
/-- Value-level semantics of the representative instructions: the Arm model's operations on
the operand values, with world `w` (flags, memory). A memory access must avoid the frame
addresses `F` (source memory safety: the program's own accesses never touch the allocator's
frame slots); otherwise the semantics is undefined. -/
noncomputable def csem (F : BitVec 64 → Prop) : ISem CV Arm.ArmState := fun i uses w =>
  match i, uses with
  | .mov .size64 _ _, [a] => some ([ofX (lo64 a)], w, .next)
  | .aluRRR .add .size64 _ _ _, [a, b] => some ([ofX (lo64 a + lo64 b)], w, .next)
  | .aluRRImm12 .add .size64 _ _ imm, [a] =>
    some ([ofX (lo64 a + BitVec.ofNat 64 imm.value)], w, .next)
  | .csel _ _ _ c, [a, b] =>
    some ([ofX (if Arm.ConditionHolds c.bits w then lo64 a else lo64 b)], w, .next)
  | .cset _ c, [] =>
    some ([ofX (if Arm.ConditionHolds c.invert.bits w then 0#64 else 1#64)], w, .next)
  | .load .uload64 _ (.unsignedOffset _ off) _, [base] =>
    if Avoids F 8 (lo64 base + BitVec.ofNat 64 off) then
      some ([ofX (Arm.read_mem_bytes 8 (lo64 base + BitVec.ofNat 64 off) w)], w, .next)
    else none
  | .store .store64 _ (.unsignedOffset _ off) _, [data, base] =>
    if Avoids F 8 (lo64 base + BitVec.ofNat 64 off) then
      some ([], Arm.write_mem_bytes 8 (lo64 base + BitVec.ofNat 64 off) (lo64 data) w, .next)
    else none
  | _, _ => none

theorem operandsSound_mov (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F) (.mov .size64 (.vreg d .int) (.vreg m .int)) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.mov .size64 (.vreg d .int) (.vreg m .int)) =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨m, .int, .use, .early, .reg⟩] := rfl
  rw [this] at hops
  cases hops
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, r1, rfl⟩ : ∃ r0 r1, regs = #[r0, r1] := by
    rcases regs with ⟨_ | ⟨r0, _ | ⟨r1, _ | ⟨r2, l⟩⟩⟩⟩
    · simp at hsz
    · simp at hsz
    · exact ⟨r0, r1, rfl⟩
    · simp at hsz
  have : MInst.assign (.mov .size64 (.vreg d .int) (.vreg m .int)) #[r0, r1] =
      .ok (.mov .size64 r0 r1) := rfl
  rw [this] at hasg
  cases hasg
  obtain ⟨n0, rfl, hn0⟩ := locOk_int (hloc (⟨d, .int, .def, .late, .reg⟩, .reg r0) (by simp)).1
  obtain ⟨n1, rfl, hn1⟩ := locOk_int (hloc (⟨m, .int, .use, .early, .reg⟩, .reg r1) (by simp)).1
  simp [useVals, csem, Operand.isUse] at hsem
  obtain ⟨rfl, rfl⟩ := hsem
  have h0 : rnum n0 ≠ 31#5 := fun e => by have := congrArg BitVec.toNat e; simp [rnum_toNat (by omega : n0 < 32)] at this; omega
  have h1 : rnum n1 ≠ 31#5 := fun e => by have := congrArg BitVec.toNat e; simp [rnum_toNat (by omega : n1 < 32)] at this; omega
  refine ⟨Arm.w (.GPR (rnum n0)) (Arm.r (.GPR (rnum n1)) s) (Arm.w .PC (Arm.r .PC s + 4#64) s), ?_, ?_, ?_, ?_, ?_⟩
  · have hl : MInst.lines ctx (.mov .size64 (.x n0) (.x n1)) {} =
        .ok ([.ins (.mov true (.x n0) (.x n1))], {}) := rfl
    have hn0' : n0 ≤ 30 := by omega
    have hn1' : n1 ≤ 30 := by omega
    have ha : Insn.toArmInst env (.mov true (.x n0) (.x n1)) = .ok (.DPR (.Logical_shifted_reg
        { sf := 1#1, opc := 1#2, shift := 0#2, N := 0#1, Rm := rnum n1, imm6 := 0#6, Rn := 31#5,
          Rd := rnum n0 })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, hn0', hn1', rnum, b1]; rfl
    simp only [execMInst, hl, execLines, ha]
    congr 1
    simp [Arm.exec_inst, Arm.DPR.exec_logical_shifted_reg, Arm.DPR.exec_logical_shifted_reg_op,
      Arm.DPR.decode_op, Arm.read_gpr_zr, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr, h0, h1,
      Arm.decode_shift, Arm.shift_reg, Arm.read_pc, Arm.write_pc]
  · exact SameWorld.w_left (Masked_gpr hn0.1 hn0.2.2.2) (SameWorld.w_left (by simp [Masked]) hw)
  · intro p hp
    simp [defRegs, Operand.isDef] at hp
    subst hp
    rw [lo64_regVal_x]
    simp only [regVal, Arm.r_of_w_same, ofX]
  · intro r hr hnd _
    have hne : r ≠ .x n0 := fun e =>
      hnd (⟨d, .int, .def, .late, .reg⟩, .x n0) (by simp) (by simp [Operand.isDef]) e.symm
    rw [regVal_w, regVal_w]
    · simp [Reg.field]
      cases r <;> simp
    · rcases allocatable_cases hr with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
      · simp only [Reg.field, ne_eq, Option.some.injEq, Arm.StateField.GPR.injEq]
        exact rnum_ne (by omega) (by omega) (fun e => hne (by rw [e]))
      · simp [Reg.field]
  · intro r hr
    simp [MInst.clobbers] at hr

theorem rnum_ne31 {n : Nat} (h : n < 29) : rnum n ≠ 31#5 := fun e => by
  have := congrArg BitVec.toNat e
  simp [rnum_toNat (by omega : n < 32)] at this; omega

/-- The common tail of a straight-line instruction writing one X register: world, the def
register, every other allocatable register. -/
theorem gpr_write_sound {F : BitVec 64 → Prop} {s w : Arm.ArmState} {n0 : Nat}
    (hn0 : n0 < 29 ∧ n0 ≠ 16 ∧ n0 ≠ 17 ∧ n0 ≠ 18) (hw : SameWorld F s w) (v pc : BitVec 64) :
    SameWorld F (Arm.w (.GPR (rnum n0)) v (Arm.w .PC pc s)) w ∧
    regVal (Arm.w (.GPR (rnum n0)) v (Arm.w .PC pc s)) (.x n0) = ofX v ∧
    ∀ r, r.allocatable = true → r ≠ .x n0 →
      regVal (Arm.w (.GPR (rnum n0)) v (Arm.w .PC pc s)) r = regVal s r := by
  refine ⟨SameWorld.w_left (Masked_gpr hn0.1 hn0.2.2.2) (SameWorld.w_left (by simp [Masked]) hw),
    by simp only [regVal, Arm.r_of_w_same, ofX], ?_⟩
  intro r hr hne
  rw [regVal_w, regVal_w]
  · cases r <;> simp [Reg.field]
  · rcases allocatable_cases hr with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp only [Reg.field, ne_eq, Option.some.injEq, Arm.StateField.GPR.injEq]
      exact rnum_ne (by omega) (by omega) (fun e => hne (by rw [e]))
    · simp [Reg.field]

theorem operandsSound_add (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F)
      (.aluRRR .add .size64 (.vreg d .int) (.vreg n .int) (.vreg m .int)) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.aluRRR .add .size64 (.vreg d .int) (.vreg n .int) (.vreg m .int)) =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] := rfl
  rw [this] at hops
  cases hops
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, r1, r2, rfl⟩ : ∃ r0 r1 r2, regs = #[r0, r1, r2] := by
    rcases regs with ⟨_ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, l⟩⟩⟩⟩⟩
    · simp at hsz
    · simp at hsz
    · simp at hsz
    · exact ⟨r0, r1, r2, rfl⟩
    · simp at hsz
  have : MInst.assign (.aluRRR .add .size64 (.vreg d .int) (.vreg n .int) (.vreg m .int))
      #[r0, r1, r2] = .ok (.aluRRR .add .size64 r0 r1 r2) := rfl
  rw [this] at hasg
  cases hasg
  obtain ⟨n0, rfl, hn0⟩ := locOk_int (hloc (⟨d, .int, .def, .late, .reg⟩, .reg r0) (by simp)).1
  obtain ⟨n1, rfl, hn1⟩ := locOk_int (hloc (⟨n, .int, .use, .early, .reg⟩, .reg r1) (by simp)).1
  obtain ⟨n2, rfl, hn2⟩ := locOk_int (hloc (⟨m, .int, .use, .early, .reg⟩, .reg r2) (by simp)).1
  simp [useVals, csem, Operand.isUse] at hsem
  obtain ⟨rfl, rfl⟩ := hsem
  have hl : MInst.lines ctx (.aluRRR .add .size64 (.x n0) (.x n1) (.x n2)) {} =
      .ok ([.ins (.aluRRR .add true (.x n0) (.x n1) (.x n2))], {}) := rfl
  have ha : Insn.toArmInst env (.aluRRR .add true (.x n0) (.x n1) (.x n2)) =
      .ok (.DPR (.Add_sub_shifted_reg
        { sf := 1#1, op := 0#1, S := 0#1, shift := 0#2, Rm := rnum n2, imm6 := 0#6,
          Rn := rnum n1, Rd := rnum n0 })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, show n0 ≤ 30 by omega, show n1 ≤ 30 by omega,
      show n2 ≤ 30 by omega, rnum, b1, ALUOp.addSub?]
    rfl
  have he : Arm.exec_inst (.DPR (.Add_sub_shifted_reg
        { sf := 1#1, op := 0#1, S := 0#1, shift := 0#2, Rm := rnum n2, imm6 := 0#6,
          Rn := rnum n1, Rd := rnum n0 })) s =
      Arm.w (.GPR (rnum n0)) (Arm.r (.GPR (rnum n1)) s + Arm.r (.GPR (rnum n2)) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
    simp [Arm.exec_inst, Arm.DPR.exec_add_sub_shifted_reg, Arm.read_gpr_zr, Arm.write_gpr_zr,
      Arm.read_gpr, Arm.write_gpr, rnum_ne31 hn0.1, rnum_ne31 hn1.1, rnum_ne31 hn2.1,
      Arm.decode_shift, Arm.shift_reg, Arm.read_pc, Arm.write_pc, Arm.fst_AddWithCarry_eq_add]
  obtain ⟨hW, hD, hO⟩ := gpr_write_sound hn0 hw
    (Arm.r (.GPR (rnum n1)) s + Arm.r (.GPR (rnum n2)) s) (Arm.r .PC s + 4#64)
  refine ⟨_, by simp only [execMInst, hl, execLines, ha, he], hW, ?_, ?_, ?_⟩
  · intro p hp
    simp [defRegs, Operand.isDef] at hp
    subst hp
    rw [hD, lo64_regVal_x, lo64_regVal_x]
  · intro r hr hnd _
    have hne : r ≠ .x n0 := fun e =>
      hnd (⟨d, .int, .def, .late, .reg⟩, .x n0) (by simp) (by simp [Operand.isDef]) e.symm
    exact hO r hr hne
  · intro r hr
    simp [MInst.clobbers] at hr


theorem ConditionHolds_sameWorld {F} {s w : Arm.ArmState} (hw : SameWorld F s w) (c : BitVec 4) :
    Arm.ConditionHolds c s = Arm.ConditionHolds c w := by
  have hf : ∀ f, Arm.read_flag f s = Arm.read_flag f w := fun f =>
    hw.1 (.FLAG f) (by simp [Masked])
  simp only [Arm.ConditionHolds, hf]

theorem operandsSound_csel (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d n m : Nat)
    (cc : Cond) :
    OperandsSound F (execMInst ctx env) (csem F)
      (.csel (.vreg d .int) (.vreg n .int) (.vreg m .int) cc) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.csel (.vreg d .int) (.vreg n .int) (.vreg m .int) cc) =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
        ⟨m, .int, .use, .early, .reg⟩] := rfl
  rw [this] at hops
  cases hops
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, r1, r2, rfl⟩ : ∃ r0 r1 r2, regs = #[r0, r1, r2] := by
    rcases regs with ⟨_ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, l⟩⟩⟩⟩⟩
    · simp at hsz
    · simp at hsz
    · simp at hsz
    · exact ⟨r0, r1, r2, rfl⟩
    · simp at hsz
  have : MInst.assign (.csel (.vreg d .int) (.vreg n .int) (.vreg m .int) cc)
      #[r0, r1, r2] = .ok (.csel r0 r1 r2 cc) := rfl
  rw [this] at hasg
  cases hasg
  obtain ⟨n0, rfl, hn0⟩ := locOk_int (hloc (⟨d, .int, .def, .late, .reg⟩, .reg r0) (by simp)).1
  obtain ⟨n1, rfl, hn1⟩ := locOk_int (hloc (⟨n, .int, .use, .early, .reg⟩, .reg r1) (by simp)).1
  obtain ⟨n2, rfl, hn2⟩ := locOk_int (hloc (⟨m, .int, .use, .early, .reg⟩, .reg r2) (by simp)).1
  simp [useVals, csem, Operand.isUse] at hsem
  obtain ⟨rfl, rfl⟩ := hsem
  have hl : MInst.lines ctx (.csel (.x n0) (.x n1) (.x n2) cc) {} =
      .ok ([.ins (.csel (.x n0) (.x n1) (.x n2) cc)], {}) := rfl
  have ha : Insn.toArmInst env (.csel (.x n0) (.x n1) (.x n2) cc) =
      .ok (.DPR (.Conditional_select
        { sf := 1#1, op := 0#1, S := 0#1, Rm := rnum n2, cond := cc.bits, op2 := 0#2,
          Rn := rnum n1, Rd := rnum n0 })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, show n0 ≤ 30 by omega,
      show n1 ≤ 30 by omega, show n2 ≤ 30 by omega, rnum]
    rfl
  have he : Arm.exec_inst (.DPR (.Conditional_select
        { sf := 1#1, op := 0#1, S := 0#1, Rm := rnum n2, cond := cc.bits, op2 := 0#2,
          Rn := rnum n1, Rd := rnum n0 })) s =
      Arm.w (.GPR (rnum n0))
        (if Arm.ConditionHolds cc.bits s then Arm.r (.GPR (rnum n1)) s else Arm.r (.GPR (rnum n2)) s)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
    simp [Arm.exec_inst, Arm.DPR.exec_conditional_select, Arm.read_gpr_zr, Arm.write_gpr_zr,
      Arm.read_gpr, Arm.write_gpr, rnum_ne31 hn0.1, rnum_ne31 hn1.1, rnum_ne31 hn2.1,
      Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb]
  obtain ⟨hW, hD, hO⟩ := gpr_write_sound hn0 hw
    (if Arm.ConditionHolds cc.bits s then Arm.r (.GPR (rnum n1)) s else Arm.r (.GPR (rnum n2)) s)
    (Arm.r .PC s + 4#64)
  refine ⟨_, by simp only [execMInst, hl, execLines, ha, he], hW, ?_, ?_, ?_⟩
  · intro p hp
    simp [defRegs, Operand.isDef] at hp
    subst hp
    rw [hD, lo64_regVal_x, lo64_regVal_x, ConditionHolds_sameWorld hw]
  · intro r hr hnd _
    have hne : r ≠ .x n0 := fun e =>
      hnd (⟨d, .int, .def, .late, .reg⟩, .x n0) (by simp) (by simp [Operand.isDef]) e.symm
    exact hO r hr hne
  · intro r hr
    simp [MInst.clobbers] at hr

theorem operandsSound_cset (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d : Nat)
    (cc : Cond) (hcc : cc ≠ .al ∧ cc ≠ .nv) :
    OperandsSound F (execMInst ctx env) (csem F) (.cset (.vreg d .int) cc) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.cset (.vreg d .int) cc) = .ok #[⟨d, .int, .def, .late, .reg⟩] := rfl
  rw [this] at hops
  cases hops
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, rfl⟩ : ∃ r0, regs = #[r0] := by
    rcases regs with ⟨_ | ⟨r0, _ | ⟨r1, l⟩⟩⟩
    · simp at hsz
    · exact ⟨r0, rfl⟩
    · simp at hsz
  have : MInst.assign (.cset (.vreg d .int) cc) #[r0] = .ok (.cset r0 cc) := rfl
  rw [this] at hasg
  cases hasg
  obtain ⟨n0, rfl, hn0⟩ := locOk_int (hloc (⟨d, .int, .def, .late, .reg⟩, .reg r0) (by simp)).1
  simp [useVals, csem, Operand.isUse] at hsem
  obtain ⟨rfl, rfl⟩ := hsem
  have hl : MInst.lines ctx (.cset (.x n0) cc) {} = .ok ([.ins (.cset (.x n0) cc)], {}) := rfl
  have ha : Insn.toArmInst env (.cset (.x n0) cc) =
      .ok (.DPR (.Conditional_select
        { sf := 1#1, op := 0#1, S := 0#1, Rm := 31#5, cond := cc.invert.bits, op2 := 1#2,
          Rn := 31#5, Rd := rnum n0 })) := by
    have h1 : (cc == .al || cc == .nv) = false := by
      cases cc <;> first | rfl | (exfalso; simp_all)
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, show n0 ≤ 30 by omega,
      rnum, h1]
    rfl
  have he : Arm.exec_inst (.DPR (.Conditional_select
        { sf := 1#1, op := 0#1, S := 0#1, Rm := 31#5, cond := cc.invert.bits, op2 := 1#2,
          Rn := 31#5, Rd := rnum n0 })) s =
      Arm.w (.GPR (rnum n0)) (if Arm.ConditionHolds cc.invert.bits s then 0#64 else 1#64)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
    simp [Arm.exec_inst, Arm.DPR.exec_conditional_select, Arm.read_gpr_zr, Arm.write_gpr_zr,
      Arm.read_gpr, Arm.write_gpr, rnum_ne31 hn0.1, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb]
  obtain ⟨hW, hD, hO⟩ := gpr_write_sound hn0 hw
    (if Arm.ConditionHolds cc.invert.bits s then 0#64 else 1#64) (Arm.r .PC s + 4#64)
  refine ⟨_, by simp only [execMInst, hl, execLines, ha, he], hW, ?_, ?_, ?_⟩
  · intro p hp
    simp [defRegs, Operand.isDef] at hp
    subst hp
    rw [hD, ConditionHolds_sameWorld hw]
  · intro r hr hnd _
    have hne : r ≠ .x n0 := fun e =>
      hnd (⟨d, .int, .def, .late, .reg⟩, .x n0) (by simp) (by simp [Operand.isDef]) e.symm
    exact hO r hr hne
  · intro r hr
    simp [MInst.clobbers] at hr


theorem addImm_value (imm : Imm12) (h : imm.bits < 4096) :
    BitVec.zeroExtend 64 (if b1 imm.shift12 = 0#1 then 0#52 ++ BitVec.ofNat 12 imm.bits
      else (0#52 ++ BitVec.ofNat 12 imm.bits) <<< 12) = BitVec.ofNat 64 imm.value := by
  have ht : (0#52 ++ BitVec.ofNat 12 imm.bits).toNat = imm.bits := by
    rw [BitVec.toNat_append]; simp [Nat.mod_eq_of_lt h]
  apply BitVec.eq_of_toNat_eq
  cases hs : imm.shift12 <;> simp [b1, hs, Imm12.value, BitVec.toNat_shiftLeft, ht] <;> omega

theorem operandsSound_addImm (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d n : Nat)
    (imm : Imm12) (himm : imm.bits < 4096) :
    OperandsSound F (execMInst ctx env) (csem F)
      (.aluRRImm12 .add .size64 (.vreg d .int) (.vreg n .int) imm) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.aluRRImm12 .add .size64 (.vreg d .int) (.vreg n .int) imm) =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] := rfl
  rw [this] at hops
  cases hops
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, r1, rfl⟩ : ∃ r0 r1, regs = #[r0, r1] := by
    rcases regs with ⟨_ | ⟨r0, _ | ⟨r1, _ | ⟨r2, l⟩⟩⟩⟩
    · simp at hsz
    · simp at hsz
    · exact ⟨r0, r1, rfl⟩
    · simp at hsz
  have : MInst.assign (.aluRRImm12 .add .size64 (.vreg d .int) (.vreg n .int) imm) #[r0, r1] =
      .ok (.aluRRImm12 .add .size64 r0 r1 imm) := rfl
  rw [this] at hasg
  cases hasg
  obtain ⟨n0, rfl, hn0⟩ := locOk_int (hloc (⟨d, .int, .def, .late, .reg⟩, .reg r0) (by simp)).1
  obtain ⟨n1, rfl, hn1⟩ := locOk_int (hloc (⟨n, .int, .use, .early, .reg⟩, .reg r1) (by simp)).1
  simp [useVals, csem, Operand.isUse] at hsem
  obtain ⟨rfl, rfl⟩ := hsem
  have hl : MInst.lines ctx (.aluRRImm12 .add .size64 (.x n0) (.x n1) imm) {} =
      .ok ([.ins (.aluImm12 .add true (.x n0) (.x n1) imm)], {}) := rfl
  have ha : Insn.toArmInst env (.aluImm12 .add true (.x n0) (.x n1) imm) =
      .ok (.DPI (.Add_sub_imm
        { sf := 1#1, op := 0#1, S := 0#1, sh := b1 imm.shift12, imm12 := BitVec.ofNat 12 imm.bits,
          Rn := rnum n1, Rd := rnum n0 })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encSP, show n0 ≤ 30 by omega,
      show n1 ≤ 30 by omega, rnum, ALUOp.addSub?, uField, himm]
    rfl
  have he : Arm.exec_inst (.DPI (.Add_sub_imm
        { sf := 1#1, op := 0#1, S := 0#1, sh := b1 imm.shift12, imm12 := BitVec.ofNat 12 imm.bits,
          Rn := rnum n1, Rd := rnum n0 })) s =
      Arm.w (.GPR (rnum n0)) (Arm.r (.GPR (rnum n1)) s + BitVec.ofNat 64 imm.value)
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
    rw [← addImm_value imm himm]
    simp [Arm.exec_inst, Arm.DPI.exec_add_sub_imm, Arm.read_gpr_zr, Arm.write_gpr_zr,
      Arm.read_gpr, Arm.write_gpr, rnum_ne31 hn0.1, Arm.read_pc, Arm.write_pc,
      Arm.fst_AddWithCarry_eq_add]
  obtain ⟨hW, hD, hO⟩ := gpr_write_sound hn0 hw
    (Arm.r (.GPR (rnum n1)) s + BitVec.ofNat 64 imm.value) (Arm.r .PC s + 4#64)
  refine ⟨_, by simp only [execMInst, hl, execLines, ha, he], hW, ?_, ?_, ?_⟩
  · intro p hp
    simp [defRegs, Operand.isDef] at hp
    subst hp
    rw [hD, lo64_regVal_x]
  · intro r hr hnd _
    have hne : r ≠ .x n0 := fun e =>
      hnd (⟨d, .int, .def, .late, .reg⟩, .x n0) (by simp) (by simp [Operand.isDef]) e.symm
    exact hO r hr hne
  · intro r hr
    simp [MInst.clobbers] at hr

end Backend.Proof

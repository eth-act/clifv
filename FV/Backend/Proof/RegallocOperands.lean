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

theorem read_mem_bytes_congr {s t : Arm.ArmState} :
    ∀ (n : Nat) (a : BitVec 64), (∀ k < n, s.mem (a + BitVec.ofNat 64 k) = t.mem (a + BitVec.ofNat 64 k)) →
      Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a t
  | 0, _, _ => rfl
  | n + 1, a, h => by
    unfold Arm.read_mem_bytes
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    have ih := read_mem_bytes_congr (s := s) (t := t) n (a + 1#64) (fun k hk => by
      have e : a + 1#64 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [e]; exact h (k + 1) (by omega))
    simp only [Arm.read_mem, Arm.read_store, h0, ih]

theorem write_bytes_congr {m1 m2 : Arm.Memory} {b : BitVec 64} (hb : m1 b = m2 b) :
    ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)),
      Arm.Memory.write_bytes n a v m1 b = Arm.Memory.write_bytes n a v m2 b
  | 0, _, _ => hb
  | n + 1, a, v => by
    unfold Arm.Memory.write_bytes
    simp only
    have : ∀ m1 m2 : Arm.Memory, m1 b = m2 b →
        Arm.Memory.write_bytes n (a + 1#64) (BitVec.setWidth (n * 8) (v >>> 8)) m1 b =
        Arm.Memory.write_bytes n (a + 1#64) (BitVec.setWidth (n * 8) (v >>> 8)) m2 b :=
      fun m1 m2 h => write_bytes_congr (m1 := m1) (m2 := m2) h n _ _
    apply this
    simp only [Arm.Memory.write, Arm.write_store]
    split <;> simp_all

theorem SameWorld.write_mem_bytes {F} {s w : Arm.ArmState} (hw : SameWorld F s w) (n : Nat)
    (a : BitVec 64) (v : BitVec (n * 8)) :
    SameWorld F (Arm.write_mem_bytes n a v s) (Arm.write_mem_bytes n a v w) := by
  refine ⟨fun f hf => ?_, fun b hb => ?_, ?_⟩
  · rw [Arm.r_of_write_mem_bytes, Arm.r_of_write_mem_bytes]; exact hw.1 f hf
  · rw [Arm.Memory.write_mem_bytes_eq_mem_write_bytes, Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
    exact write_bytes_congr (hw.2.1 b hb) n a v
  · rw [Arm.write_mem_bytes_program, Arm.write_mem_bytes_program]; exact hw.2.2

theorem ldst_offset (off : Nat) (h8 : off % 8 = 0) (h : off / 8 < 4096) :
    BitVec.setWidth 64 (BitVec.ofNat 12 (off / 8)) <<< 3 = BitVec.ofNat 64 off := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt h]
  omega


theorem regVal_write_mem_bytes (s : Arm.ArmState) (n : Nat) (a : BitVec 64) (v : BitVec (n * 8))
    (r : Reg) : regVal (Arm.write_mem_bytes n a v s) r = regVal s r := by
  cases r <;> simp [regVal, Arm.r_of_write_mem_bytes]

theorem operandsSound_load (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d n off : Nat)
    (fl : Clif.MemFlags) (h8 : off % 8 = 0) (h12 : off / 8 < 4096) :
    OperandsSound F (execMInst ctx env) (csem F)
      (.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl) =
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
  have : MInst.assign (.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl)
      #[r0, r1] = .ok (.load .uload64 r0 (.unsignedOffset r1 off) fl) := rfl
  rw [this] at hasg
  cases hasg
  obtain ⟨n0, rfl, hn0⟩ := locOk_int (hloc (⟨d, .int, .def, .late, .reg⟩, .reg r0) (by simp)).1
  obtain ⟨n1, rfl, hn1⟩ := locOk_int (hloc (⟨n, .int, .use, .early, .reg⟩, .reg r1) (by simp)).1
  simp only [useVals, csem, Operand.isUse] at hsem
  simp at hsem
  obtain ⟨hav, rfl, rfl⟩ := hsem
  · 
    have hl : MInst.lines ctx (.load .uload64 (.x n0) (.unsignedOffset (.x n1) off) fl) {} =
        .ok ([.ins (.load .uload64 (.x n0) (.unsignedOffset (.x n1) off)) fl.trapCode], {}) := rfl
    have ha : Insn.toArmInst env (.load .uload64 (.x n0) (.unsignedOffset (.x n1) off)) =
        .ok (.LDST (.Reg_unsigned_imm
          { size := 3#2, V := 0#1, opc := 1#2, imm12 := BitVec.ofNat 12 (off / 8),
            Rn := rnum n1, Rt := rnum n0 })) := by
      simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, LoadOp.fields, ldstFields,
        Reg.encZR, Reg.encSP, show n0 ≤ 30 by omega, show n1 ≤ 30 by omega, rnum, uField, h8,
        h12, LoadOp.bytes]
      rfl
    have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm
          { size := 3#2, V := 0#1, opc := 1#2, imm12 := BitVec.ofNat 12 (off / 8),
            Rn := rnum n1, Rt := rnum n0 })) s =
        Arm.w (.GPR (rnum n0))
          (Arm.read_mem_bytes 8 (Arm.r (.GPR (rnum n1)) s + BitVec.ofNat 64 off) s)
          (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
      rw [← ldst_offset off h8 h12, Arm.w_of_w_commute (by simp)]
      simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
        Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
        Arm.LDST.reg_imm_constrain_unpredictable, Arm.write_gpr_zr, Arm.read_gpr, Arm.write_gpr,
        rnum_ne31 hn0.1, rnum_ne31 hn1.1, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb]
      rfl
    obtain ⟨hW, hD, hO⟩ := gpr_write_sound hn0 hw
      (Arm.read_mem_bytes 8 (Arm.r (.GPR (rnum n1)) s + BitVec.ofNat 64 off) s)
      (Arm.r .PC s + 4#64)
    refine ⟨_, by simp only [execMInst, hl, execLines, ha, he], hW, ?_, ?_, ?_⟩
    · intro p hp
      simp [defRegs, Operand.isDef] at hp
      subst hp
      rw [hD, lo64_regVal_x] at *
      congr 1
      exact read_mem_bytes_congr 8 _ (fun k hk => hw.2.1 _ (hav k hk))
    · intro r hr hnd _
      have hne : r ≠ .x n0 := fun e =>
        hnd (⟨d, .int, .def, .late, .reg⟩, .x n0) (by simp) (by simp [Operand.isDef]) e.symm
      exact hO r hr hne
    · intro r hr
      simp [MInst.clobbers] at hr


theorem operandsSound_store (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (d n off : Nat)
    (fl : Clif.MemFlags) (h8 : off % 8 = 0) (h12 : off / 8 < 4096) :
    OperandsSound F (execMInst ctx env) (csem F)
      (.store .store64 (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.store .store64 (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl) =
      .ok #[⟨d, .int, .use, .early, .reg⟩, ⟨n, .int, .use, .early, .reg⟩] := rfl
  rw [this] at hops
  cases hops
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, r1, rfl⟩ : ∃ r0 r1, regs = #[r0, r1] := by
    rcases regs with ⟨_ | ⟨r0, _ | ⟨r1, _ | ⟨r2, l⟩⟩⟩⟩
    · simp at hsz
    · simp at hsz
    · exact ⟨r0, r1, rfl⟩
    · simp at hsz
  have : MInst.assign (.store .store64 (.vreg d .int) (.unsignedOffset (.vreg n .int) off) fl)
      #[r0, r1] = .ok (.store .store64 r0 (.unsignedOffset r1 off) fl) := rfl
  rw [this] at hasg
  cases hasg
  obtain ⟨n0, rfl, hn0⟩ := locOk_int (hloc (⟨d, .int, .use, .early, .reg⟩, .reg r0) (by simp)).1
  obtain ⟨n1, rfl, hn1⟩ := locOk_int (hloc (⟨n, .int, .use, .early, .reg⟩, .reg r1) (by simp)).1
  simp only [useVals, csem, Operand.isUse] at hsem
  simp at hsem
  obtain ⟨hav, rfl, rfl⟩ := hsem
  have hl : MInst.lines ctx (.store .store64 (.x n0) (.unsignedOffset (.x n1) off) fl) {} =
      .ok ([.ins (.store .store64 (.x n0) (.unsignedOffset (.x n1) off)) fl.trapCode], {}) := rfl
  have ha : Insn.toArmInst env (.store .store64 (.x n0) (.unsignedOffset (.x n1) off)) =
      .ok (.LDST (.Reg_unsigned_imm
        { size := 3#2, V := 0#1, opc := 0#2, imm12 := BitVec.ofNat 12 (off / 8),
          Rn := rnum n1, Rt := rnum n0 })) := by
    simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, StoreOp.fields, ldstFields,
      Reg.encZR, Reg.encSP, show n0 ≤ 30 by omega, show n1 ≤ 30 by omega, rnum, uField, h8,
      h12, StoreOp.bytes]
    rfl
  have he : Arm.exec_inst (.LDST (.Reg_unsigned_imm
        { size := 3#2, V := 0#1, opc := 0#2, imm12 := BitVec.ofNat 12 (off / 8),
          Rn := rnum n1, Rt := rnum n0 })) s =
      Arm.w .PC (Arm.r .PC s + 4#64)
        (Arm.write_mem_bytes 8 (Arm.r (.GPR (rnum n1)) s + BitVec.ofNat 64 off)
          (Arm.r (.GPR (rnum n0)) s) s) := by
    rw [← ldst_offset off h8 h12]
    simp [Arm.exec_inst, Arm.LDST.exec_reg_imm_unsigned_offset, Arm.LDST.exec_reg_imm_common,
      Arm.LDST.reg_imm_operation, Arm.LDST.Reg_offset.value,
      Arm.LDST.reg_imm_constrain_unpredictable, Arm.ldst_read, Arm.read_gpr_zr, Arm.read_gpr,
      rnum_ne31 hn0.1, rnum_ne31 hn1.1, Arm.read_pc, Arm.write_pc, Arm.BitVec.lsb]
    rfl
  refine ⟨Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.write_mem_bytes 8 (Arm.r (.GPR (rnum n1)) s + BitVec.ofNat 64 off)
        (Arm.r (.GPR (rnum n0)) s) s), by simp only [execMInst, hl, execLines, ha, he], ?_, ?_, ?_, ?_⟩
  · rw [lo64_regVal_x, lo64_regVal_x]
    exact SameWorld.w_left (by simp [Masked]) (SameWorld.write_mem_bytes hw 8 _ _)
  · intro p hp
    simp [defRegs, Operand.isDef] at hp
  · intro r _ _ _
    rw [regVal_w (by cases r <;> simp [Reg.field]), regVal_write_mem_bytes]
  · intro r hr
    simp [MInst.clobbers] at hr

theorem writeM_not_mem {V : Type} {m : Loc → V} {l : Loc} :
    ∀ {dl : List ((Operand × Loc) × V)}, l ∉ dl.map (·.1.2) → writeM m dl l = m l
  | [], _ => rfl
  | p :: dl, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [writeM, List.foldl_cons] at *
    have := writeM_not_mem (m := upd m p.1.2 p.2) (l := l) h.2
    simp only [writeM] at this
    rw [this]; simp [upd, h.1]

theorem writeM_mem {V : Type} {m : Loc → V} :
    ∀ {dl : List ((Operand × Loc) × V)}, (dl.map (·.1.2)).Nodup → ∀ p ∈ dl, writeM m dl p.1.2 = p.2
  | [], _, _, hp => by simp at hp
  | q :: dl, hn, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [writeM, List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · have := writeM_not_mem (m := upd m p.1.2 p.2) (l := p.1.2) hn.1
      simp only [writeM] at this
      rw [this]; simp [upd]
    · have := writeM_mem (m := upd m q.1.2 q.2) hn.2 p hp
      simpa only [writeM] using this

theorem calleeSaved_allocatable {r : Reg} (h : r ∈ calleeSaved) : r.allocatable = true := by
  simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at h
  rw [allocatable_iff]
  rcases h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    (rcases i with _|_|_|_|_|_|_|_|_|_|i <;> simp_all <;> omega)


theorem pairs_regs (ops : Array Operand) (regs : Array Reg) :
    (ops.zip (regs.map Loc.reg)).toList = (ops.zip regs).toList.map (fun p => (p.1, Loc.reg p.2)) := by
  rw [Array.toList_zip, Array.toList_zip, Array.toList_map, List.zip_map_right]
  rfl

/-- The store part of `operandsSound_step`, for any list `D` of def writes whose locations are
distinct registers holding the concrete results. -/
theorem defs_store {s s' : Arm.ArmState} {m : Loc → CV} {clob : List Reg}
    (D : List ((Operand × Loc) × CV)) (hnd : (D.map (·.1.2)).Nodup)
    (hval : ∀ p ∈ D, ∃ r, p.1.2 = .reg r ∧ regVal s' r = p.2)
    (hclobD : ∀ p ∈ D, ∀ r ∈ clob, p.1.2 ≠ .reg r)
    (hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r)
    (hoth : ∀ r, r.allocatable = true → (∀ p ∈ D, p.1.2 ≠ .reg r) → r ∉ clob →
      regVal s' r = regVal s r)
    (hcl : ∀ r ∈ clob, r ∈ calleeSaved → ckeep r (regVal s' r) = ckeep r (regVal s r)) :
    ∃ m2, Clobbered ckeep clob (writeM m (D.filter (·.1.1.isEarly))) m2 ∧
      (∀ r, r.allocatable = true →
        writeM m2 (D.filter (·.1.1.isLate)) (.reg r) = regVal s' r) ∧
      (∀ l, (∀ r, l ≠ .reg r) → writeM m2 (D.filter (·.1.1.isLate)) l = m l) := by
  have hndE : ((D.filter (·.1.1.isEarly)).map (·.1.2)).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup hnd
  have hndL : ((D.filter (·.1.1.isLate)).map (·.1.2)).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup hnd
  let m1 := writeM m (D.filter (·.1.1.isEarly))
  let m2 : Loc → CV := fun l => match l with
    | .reg r => if r ∈ clob then regVal s' r else m1 l
    | l => m1 l
  have hm1 : ∀ l, l ∉ D.map (·.1.2) → m1 l = m l := fun l hl =>
    writeM_not_mem (fun h => hl ((List.Sublist.map _ List.filter_sublist).subset h))
  refine ⟨m2, ⟨fun l hl => ?_, fun c hc hcs => ?_⟩, fun r hr => ?_, fun l hl => ?_⟩
  · cases l with
    | reg r => simp only [m2, m1, show r ∉ clob from fun h => hl r h rfl, if_false]
    | _ => rfl
  · simp only [m2, hc, if_true]
    have hnot : Loc.reg c ∉ D.map (·.1.2) := by
      intro h
      obtain ⟨p, hp, e⟩ := List.mem_map.mp h
      exact hclobD p hp c hc e
    have h1 := hm1 _ hnot
    simp only [m1] at h1
    rw [hcl c hc hcs, h1, hm c (calleeSaved_allocatable hcs)]
  · by_cases hL : Loc.reg r ∈ (D.filter (·.1.1.isLate)).map (·.1.2)
    · obtain ⟨p, hp, e⟩ := List.mem_map.mp hL
      rw [← e, writeM_mem hndL p hp]
      obtain ⟨r', hr', hv⟩ := hval p (List.mem_filter.mp hp).1
      rw [e] at hr'
      cases hr'
      exact hv.symm
    · rw [writeM_not_mem hL]
      by_cases hc : r ∈ clob
      · simp only [m2, hc, if_true]
      · simp only [m2, hc, if_false]
        by_cases hE : Loc.reg r ∈ (D.filter (·.1.1.isEarly)).map (·.1.2)
        · obtain ⟨p, hp, e⟩ := List.mem_map.mp hE
          show writeM m (D.filter (·.1.1.isEarly)) (Loc.reg r) = _
          rw [← e, writeM_mem hndE p hp]
          obtain ⟨r', hr', hv⟩ := hval p (List.mem_filter.mp hp).1
          rw [e] at hr'
          cases hr'
          exact hv.symm
        · have hnD : ∀ p ∈ D, p.1.2 ≠ .reg r := by
            intro p hp e
            cases hpos : p.1.1.pos
            · exact hE (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by
                simp [Operand.isEarly, hpos]⟩, e⟩)
            · exact hL (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by
                simp [Operand.isLate, hpos]⟩, e⟩)
          show writeM m (D.filter (·.1.1.isEarly)) (Loc.reg r) = _
          rw [writeM_not_mem hE, hm r hr, hoth r hr hnD hc]
  · have hnL : l ∉ (D.filter (·.1.1.isLate)).map (·.1.2) := by
      intro h
      obtain ⟨p, hp, e⟩ := List.mem_map.mp h
      obtain ⟨r, hr, _⟩ := hval p (List.mem_filter.mp hp).1
      exact hl r (e ▸ hr)
    rw [writeM_not_mem hnL]
    have hnD : l ∉ D.map (·.1.2) := by
      intro h
      obtain ⟨p, hp, e⟩ := List.mem_map.mp h
      obtain ⟨r, hr, _⟩ := hval p hp
      exact hl r (e ▸ hr)
    cases l with
    | reg r => exact absurd rfl (hl r)
    | _ => exact hm1 _ hnD


/-- **`OperandsSound` makes a concrete instruction an `MStep.op`.** If the location store `m`
agrees with the Arm state `s` on allocatable registers and `s` has the world `w`, executing the
emitted instruction gives a state `s'` with the world `sem` computes, and a clobber havoc `m2`
(`Clobbered ckeep`, as `MStep.op` requires) such that the store after the late defs agrees
with `s'` on allocatable registers; frame locations are untouched. -/
theorem operandsSound_step {F : BitVec 64 → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState}
    {sem : ISem CV Arm.ArmState} {i : MInst} (hs : OperandsSound F exec sem i)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : i.operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') {m : Loc → CV} {s w : Arm.ArmState}
    (hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r) (hw : SameWorld F s w)
    {outs : List CV} {w' : Arm.ArmState}
    (hsem : sem i (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length) :
    ∃ s' m2, exec i' s = some s' ∧ SameWorld F s' w' ∧
      Clobbered ckeep i.clobbers
        (writeM m ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isEarly))) m2 ∧
      (∀ r, r.allocatable = true →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) (.reg r) = regVal s' r) ∧
      (∀ l, (∀ r, l ≠ .reg r) →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) l = m l) := by
  obtain ⟨_, hloc, hnd, hdc⟩ := checkStatic_facts hst
  have halloc : ∀ p ∈ (ops.zip regs).toList, p.2.allocatable = true := by
    intro p hp
    have := (hloc (p.1, .reg p.2) (by rw [pairs_regs]; exact List.mem_map_of_mem hp)).1
    simp only [CheckCtx.locOk, Loc.cls?, Bool.and_eq_true] at this
    exact this.2
  have huse : ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2) =
      useVals ops regs s := by
    rw [pairs_regs, useVals, List.filter_map, List.map_map]
    apply List.map_congr_left
    intro p hp
    exact hm _ (halloc p (List.mem_filter.mp hp).1)
  rw [huse] at hsem
  obtain ⟨s', hex, hW, hdef, hoth, hcl⟩ := hs c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have htrip : ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs =
      (defRegs ops regs outs).map (fun p => ((p.1.1, Loc.reg p.1.2), p.2)) := by
    rw [pairs_regs, List.filter_map, defRegs, List.zip_map_left]
    rfl
  have hfst : (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).map (·.1) =
      (ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef) :=
    List.map_fst_zip (by omega)
  obtain ⟨m2, hc2, hr2, hl2⟩ := defs_store (s := s) (s' := s') (m := m) (clob := i.clobbers)
    (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs)
    (by
      rw [show ∀ D : List ((Operand × Loc) × CV), D.map (·.1.2) = (D.map (·.1)).map (·.2) from
        fun D => by simp, hfst]
      exact hnd)
    (by
      intro p hp
      rw [htrip] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ⟨q.1.2, rfl, hdef q hq⟩)
    (by
      intro p hp r hr
      have hp' : p.1 ∈ (ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef) := by
        rw [← hfst]; exact List.mem_map_of_mem hp
      have := List.mem_filter.mp hp'
      exact hdc p.1 this.1 (by simpa [Operand.isDef] using this.2) r hr)
    hm
    (by
      intro r hr hnD hc
      refine hoth r hr (fun q hq hqd e => ?_) hc
      have hq' : (q.1, Loc.reg q.2) ∈ (ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef) := by
        rw [pairs_regs, List.filter_map]
        exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hq, hqd⟩)
      rw [← hfst] at hq'
      obtain ⟨p, hp, e'⟩ := List.mem_map.mp hq'
      exact hnD p hp (by rw [e', e]))
    hcl
  exact ⟨s', m2, hex, hW, hc2, hr2, hl2⟩

/-- Execution with calls: a call runs the external `callee` (from the `bl` to the return; the
Arm model does not execute other functions), everything else runs as `execMInst`. -/
def execWithCalls (callee : CallInfo → Arm.ArmState → Option Arm.ArmState) (ctx : FnCtx)
    (env : Env) : MInst → Arm.ArmState → Option Arm.ArmState
  | .call info, s => callee info s
  | i, s => execMInst ctx env i s

/-- `csem` with calls given by `callSem dest args w = (results, world)`. -/
noncomputable def csemWith (F : BitVec 64 → Prop)
    (callSem : CallDest → List CV → Arm.ArmState → Option (List CV × Arm.ArmState)) :
    ISem CV Arm.ArmState := fun i uses w =>
  match i with
  | .call info => (callSem info.dest uses w).map fun (o, w') => (o, w', .next)
  | i => csem F i uses w

/-- **AAPCS64 callee contract**: called with the argument registers holding `args` in a
state with world `w`, the callee returns the results `callSem` computes in the return
registers, with world `w'`; it preserves every allocatable register outside
`DEFAULT_AAPCS_CLOBBERS` and the low 64 bits of v8–v15. -/
def CalleeSound (F : BitVec 64 → Prop) (callee : CallInfo → Arm.ArmState → Option Arm.ArmState)
    (callSem : CallDest → List CV → Arm.ArmState → Option (List CV × Arm.ArmState)) : Prop :=
  ∀ (info : CallInfo) (s w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState),
    SameWorld F s w → callSem info.dest (info.uses.map fun p => regVal s p.2) w = some (outs, w') →
    ∃ s', callee info s = some s' ∧ SameWorld F s' w' ∧
      (∀ p ∈ (info.defs.map (·.1)).zip outs, regVal s' p.1 = p.2) ∧
      (∀ r, r.allocatable = true → r ∉ defaultAapcsClobbers → regVal s' r = regVal s r) ∧
      (∀ r ∈ calleeSaved, ckeep r (regVal s' r) = ckeep r (regVal s r))

/-- A call with one argument and one result (both in x0), under the callee contract: the
operand view (fixed use/def x0, clobbers `DEFAULT_AAPCS_CLOBBERS` minus x0) is sound. -/
theorem operandsSound_call (F : BitVec 64 → Prop) (callee : CallInfo → Arm.ArmState → Option Arm.ArmState)
    (callSem : CallDest → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hcallee : CalleeSound F callee callSem) (ctx : FnCtx) (env : Env) (nm : String) (a r : Nat) :
    OperandsSound F (execWithCalls callee ctx env) (csemWith F callSem)
      (.call ⟨.sym nm, [(.vreg a .int, .x 0)], [(.x 0, .vreg r .int)]⟩) := by
  intro c wh ops regs i' s w outs w' hops hst hasg hw hsem
  have : MInst.operands (.call ⟨.sym nm, [(.vreg a .int, .x 0)], [(.x 0, .vreg r .int)]⟩) =
      .ok #[⟨a, .int, .use, .early, .fixed (.x 0)⟩, ⟨r, .int, .def, .late, .fixed (.x 0)⟩] := rfl
  rw [this] at hops
  cases hops
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, r1, rfl⟩ : ∃ r0 r1, regs = #[r0, r1] := by
    rcases regs with ⟨_ | ⟨r0, _ | ⟨r1, _ | ⟨r2, l⟩⟩⟩⟩
    · simp at hsz
    · simp at hsz
    · exact ⟨r0, r1, rfl⟩
    · simp at hsz
  have e0 := (hloc (⟨a, .int, .use, .early, .fixed (.x 0)⟩, .reg r0) (by simp)).2 (.x 0) rfl
  have e1 := (hloc (⟨r, .int, .def, .late, .fixed (.x 0)⟩, .reg r1) (by simp)).2 (.x 0) rfl
  cases e0
  cases e1
  have : MInst.assign (.call ⟨.sym nm, [(.vreg a .int, .x 0)], [(.x 0, .vreg r .int)]⟩)
      #[.x 0, .x 0] = .ok (.call ⟨.sym nm, [(.x 0, .x 0)], [(.x 0, .x 0)]⟩) := rfl
  rw [this] at hasg
  cases hasg
  simp only [csemWith, useVals] at hsem
  simp [Operand.isUse] at hsem
  obtain ⟨s', hs', hW, hres, hpres, hcs'⟩ := hcallee ⟨.sym nm, [(.x 0, .x 0)], [(.x 0, .x 0)]⟩ s w
    outs w' hw (by simpa using hsem)
  refine ⟨s', hs', hW, ?_, ?_, ?_⟩
  · intro p hp
    simp [defRegs, Operand.isDef] at hp
    cases outs with
    | nil => simp at hp
    | cons o t =>
      simp at hp
      subst hp
      simpa using hres (.x 0, o) (by simp)
  · intro r' hr hnd hnc
    have hne : Reg.x 0 ≠ r' := hnd (⟨r, .int, .def, .late, .fixed (.x 0)⟩, .x 0) (by simp)
      (by simp [Operand.isDef])
    refine hpres r' hr (fun hd => hnc ?_)
    simp [MInst.clobbers, hd, hne]
  · intro r hr hcs
    exact hcs' r hcs

end Backend.Proof

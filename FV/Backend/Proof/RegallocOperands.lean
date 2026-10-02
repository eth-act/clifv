import FV.Backend.Proof.RegallocSound
import FV.Backend.Encode
import FV.Arm.Exec

/-!
# The operand-view obligation `OperandsSound` against the Arm model (M6 proof)

`checkAlloc_sound` holds for every instruction semantics `sem`. To use it for the emitted
code, the abstract step of an original instruction (`MStep.op`: read the uses from their
locations, write the defs, havoc the clobbers) must describe what the *emitted* instruction
does. This file states that obligation against the Arm model (`OperandsSound`) and turns it
into `MStep.op` (`operandsSound_step`). The concrete semantics `csem` and the per-instruction
proofs are in `RegallocCSem.lean` and `RegallocInsts.lean`.

Concrete setting:

* values `CV = BitVec 128`; an X register holds its 64 bits zero-extended (`regVal`);
* `ckeep`: the callee-preserved part (all of an X register, the low 64 bits of a V register);
* the world is the Arm state itself, compared with `SameWorld F` — equal outside the
  allocatable registers, the emitter temporaries x16/x17, the pc (`Masked`) and the frame
  addresses `F` (spill and save slots, which the location store models);
* the emitted instruction `i'` (`MInst.assign i regs`) runs as `execMInst`: its expansion
  `MInst.lines` → `Insn.toArmInst` → `Arm.exec_inst` (what the encoder's words decode to, M5).

`OperandsSound F exec sem i`: for every register allocation the checker's static checks
accept, from every state, if `sem` gives defs `outs`, world `w'` and falls through, the
emitted code produces a state with the same world as `w'`, `outs` in the def registers, every
other allocatable register unchanged except the clobbers, whose callee-saved part survives,
and the frame (`sp` and the memory at the frame addresses `F`) untouched.
`operandsSound_step` turns that (at one state, `OperandsSoundCtlAt`, with the kept frame `FK`
possibly smaller than `F`: a call keeps the frame only outside the callees' dead stack) into the
store of `MStep.op` (with `ckeep`, the clobber havoc chosen from the concrete state), which is
how the concrete execution plugs into `checkAlloc_sound`.
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
emitter temporaries x16/x17, the link register x30 (not allocatable; the prologue saves it and
the epilogue reloads it, a `bl`/`blr` and the TLSDESC call of `tls_value` overwrite it), and the
pc (control is matched by code position). -/
def Masked : Arm.StateField → Prop
  | .GPR i => (i.toNat < 29 ∧ i.toNat ≠ 18) ∨ i.toNat = 30
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

/-- Run the lines of an instruction expansion (straight-line: instructions only, each one
advancing the pc by 4); `env.pc` advances by 4 per instruction. -/
def execLines : Env → List Line → Arm.ArmState → Option Arm.ArmState
  | _, [], s => some s
  | env, .ins i _ :: ls, s =>
    match i.toArmInst env with
    | .ok ai =>
      if Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64 then
        execLines { env with pc := env.pc + 4 } ls (Arm.exec_inst ai s)
      else none
    | .error _ => none
  | _, _ :: _, _ => none

theorem execLines_one {env : Env} {i : Insn} {t : Option Clif.TrapCode} {s : Arm.ArmState}
    {ai : Arm.ArmInst} (ha : i.toArmInst env = .ok ai)
    (hpc : Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64) :
    execLines env [.ins i t] s = some (Arm.exec_inst ai s) := by
  simp [execLines, ha, hpc]

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

/-- The stack pointer. -/
def spOf (s : Arm.ArmState) : BitVec 64 := Arm.r (.GPR 31#5) s

/-- `s'` keeps the frame of `s`: same `sp`, same bytes at the frame addresses `F`. -/
def FrameKeep (F : BitVec 64 → Prop) (s s' : Arm.ArmState) : Prop :=
  spOf s' = spOf s ∧ ∀ a, F a → s'.mem a = s.mem a

/-- **The operand-view obligation** for instruction `i` with control outcome `ctl` (the def
values, world and preserved registers of the executed instruction; a `try_call`'s call has
outcome `goto`). -/
def OperandsSoundCtl (F : BitVec 64 → Prop) (exec : MInst → Arm.ArmState → Option Arm.ArmState)
    (sem : ISem CV Arm.ArmState) (i : MInst) (ctl : Ctl) : Prop :=
  ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
    (s w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState),
    i.operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
    i.assign regs = .ok i' →
    SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
    sem i (useVals ops regs s) w = some (outs, w', ctl) →
    ∃ s', exec i' s = some s' ∧ SameWorld F s' w' ∧ FrameKeep F s s' ∧
      (∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ i.clobbers → regVal s' r = regVal s r) ∧
      (∀ r ∈ i.clobbers, r ∈ calleeSaved → ckeep r (regVal s' r) = ckeep r (regVal s r))

/-- **The operand-view obligation** for instruction `i` (straight-line outcome `next`). -/
abbrev OperandsSound (F : BitVec 64 → Prop) (exec : MInst → Arm.ArmState → Option Arm.ArmState)
    (sem : ISem CV Arm.ArmState) (i : MInst) : Prop :=
  OperandsSoundCtl F exec sem i .next

/-- **The operand-view obligation at one state `s`** (`OperandsSoundCtl` instantiated at `s`),
with the world compared outside `F` and the frame kept on `FK`. -/
def OperandsSoundCtlAt (F FK : BitVec 64 → Prop) (exec : MInst → Arm.ArmState → Option Arm.ArmState)
    (sem : ISem CV Arm.ArmState) (i : MInst) (ctl : Ctl) (s : Arm.ArmState) : Prop :=
  ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
    (w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState),
    i.operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
    i.assign regs = .ok i' →
    SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
    sem i (useVals ops regs s) w = some (outs, w', ctl) →
    ∃ s', exec i' s = some s' ∧ SameWorld F s' w' ∧ FrameKeep FK s s' ∧
      (∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ i.clobbers → regVal s' r = regVal s r) ∧
      (∀ r ∈ i.clobbers, r ∈ calleeSaved → ckeep r (regVal s' r) = ckeep r (regVal s r))

/-- `OperandsSoundCtl` at a state, keeping a smaller frame `FK ⊆ F`. -/
theorem OperandsSoundCtl.at {F FK : BitVec 64 → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState} {sem : ISem CV Arm.ArmState} {i : MInst}
    {ctl : Ctl} (h : OperandsSoundCtl F exec sem i ctl) (hFK : ∀ a, FK a → F a)
    (s : Arm.ArmState) : OperandsSoundCtlAt F FK exec sem i ctl s := by
  intro c wh ops regs i' w outs w' hops hst hasg hw hal herr hsem
  obtain ⟨s', hex, hW, hK, hd, ho, hc⟩ := h c wh ops regs i' s w outs w' hops hst hasg hw hal herr hsem
  exact ⟨s', hex, hW, ⟨hK.1, fun a ha => hK.2 a (hFK a ha)⟩, hd, ho, hc⟩

theorem OperandsSoundCtlAt.mono {F FK FK' : BitVec 64 → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState} {sem : ISem CV Arm.ArmState} {i : MInst}
    {ctl : Ctl} {s : Arm.ArmState} (h : OperandsSoundCtlAt F FK exec sem i ctl s)
    (hFK : ∀ a, FK' a → FK a) : OperandsSoundCtlAt F FK' exec sem i ctl s := by
  intro c wh ops regs i' w outs w' hops hst hasg hw hal herr hsem
  obtain ⟨s', hex, hW, hK, hd, ho, hc⟩ := h c wh ops regs i' w outs w' hops hst hasg hw hal herr hsem
  exact ⟨s', hex, hW, ⟨hK.1, fun a ha => hK.2 a (hFK a ha)⟩, hd, ho, hc⟩

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


theorem ConditionHolds_sameWorld {F} {s w : Arm.ArmState} (hw : SameWorld F s w) (c : BitVec 4) :
    Arm.ConditionHolds c s = Arm.ConditionHolds c w := by
  have hf : ∀ f, Arm.read_flag f s = Arm.read_flag f w := fun f =>
    hw.1 (.FLAG f) (by simp [Masked])
  simp only [Arm.ConditionHolds, hf]



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


/-- The use values read from a store `m` that agrees with `s` on allocatable registers, for an
allocation that passes the static checks: those of `s` (`useVals`). -/
theorem useVals_of_store {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg}
    {clob : List Reg} (hst : c.checkStatic wh ops (regs.map Loc.reg) clob = .ok ())
    {m : Loc → CV} {s : Arm.ArmState}
    (hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r) :
    ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2) = useVals ops regs s := by
  obtain ⟨_, hloc, -, -⟩ := checkStatic_facts hst
  have halloc : ∀ p ∈ (ops.zip regs).toList, p.2.allocatable = true := by
    intro p hp
    have := (hloc (p.1, .reg p.2) (by rw [pairs_regs]; exact List.mem_map_of_mem hp)).1
    simp only [CheckCtx.locOk, Loc.cls?, Bool.and_eq_true] at this
    exact this.2
  rw [pairs_regs, useVals, List.filter_map, List.map_map]
  apply List.map_congr_left
  intro p hp
  exact hm _ (halloc p (List.mem_filter.mp hp).1)

/-- **The store after an executed instruction**: if the location store `m` agrees with the Arm
state `s` on allocatable registers and the instruction's execution reached `s'`, which holds
the values `outs` in the def registers, keeps the other allocatable registers that are not
clobbered and the `ckeep`-part of the clobbered callee-saved ones, there is a clobber havoc
`m2` (`Clobbered ckeep`, as `MStep.op` requires) such that the store after the late defs agrees
with `s'` on allocatable registers and with `m` elsewhere. -/
theorem operandsSound_post {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg}
    {i : MInst} (hst : c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ())
    {m : Loc → CV} {s s' : Arm.ArmState}
    (hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r) {outs : List CV}
    (hlen : outs.length = ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length)
    (hdef : ∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2)
    (hoth : ∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
      r ∉ i.clobbers → regVal s' r = regVal s r)
    (hcl : ∀ r ∈ i.clobbers, r ∈ calleeSaved → ckeep r (regVal s' r) = ckeep r (regVal s r)) :
    ∃ m2, Clobbered ckeep i.clobbers
        (writeM m ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isEarly))) m2 ∧
      (∀ r, r.allocatable = true →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) (.reg r) = regVal s' r) ∧
      (∀ l, (∀ r, l ≠ .reg r) →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) l = m l) := by
  obtain ⟨_, -, hnd, hdc⟩ := checkStatic_facts hst
  have htrip : ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs =
      (defRegs ops regs outs).map (fun p => ((p.1.1, Loc.reg p.1.2), p.2)) := by
    rw [pairs_regs, List.filter_map, defRegs, List.zip_map_left]
    rfl
  have hfst : (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).map (·.1) =
      (ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef) :=
    List.map_fst_zip (by omega)
  exact defs_store (s := s) (s' := s') (m := m) (clob := i.clobbers)
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

/-- **`OperandsSound` makes a concrete instruction an `MStep.op`.** If the location store `m`
agrees with the Arm state `s` on allocatable registers and `s` has the world `w`, executing the
emitted instruction gives a state `s'` with the world `sem` computes, and a clobber havoc `m2`
(`Clobbered ckeep`, as `MStep.op` requires) such that the store after the late defs agrees
with `s'` on allocatable registers; the frame `FK` is untouched. Stated for the obligation at
the one state `s` (`OperandsSoundCtlAt`; `OperandsSoundCtl.at` for the obligation at every
state). -/
theorem operandsSound_step {F FK : BitVec 64 → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState}
    {sem : ISem CV Arm.ArmState} {i : MInst} {ctl : Ctl} {s : Arm.ArmState}
    (hs : OperandsSoundCtlAt F FK exec sem i ctl s)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : i.operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i') {m : Loc → CV} {w : Arm.ArmState}
    (hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r) (hw : SameWorld F s w)
    (hal : Arm.CheckSPAlignment s) (herr : Arm.r .ERR s = .None) {outs : List CV} {w' : Arm.ArmState}
    (hsem : sem i (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', ctl))
    (hlen : outs.length = ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length) :
    ∃ s' m2, exec i' s = some s' ∧ SameWorld F s' w' ∧ FrameKeep FK s s' ∧
      Clobbered ckeep i.clobbers
        (writeM m ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isEarly))) m2 ∧
      (∀ r, r.allocatable = true →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) (.reg r) = regVal s' r) ∧
      (∀ l, (∀ r, l ≠ .reg r) →
        writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip outs).filter
          (·.1.1.isLate)) l = m l) := by
  rw [useVals_of_store hst hm] at hsem
  obtain ⟨s', hex, hW, hK, hdef, hoth, hcl⟩ := hs c wh ops regs i' w outs w' hops hst hasg hw hal herr hsem
  obtain ⟨m2, hc2, hr2, hl2⟩ := operandsSound_post hst hm hlen hdef hoth hcl
  exact ⟨s', m2, hex, hW, hK, hc2, hr2, hl2⟩

/-! ## Calls and the calls of `try_call`s -/

/-- The operand visit of a call's `CallInfo` (as `MInst.visitOperands` does it). -/
def callVisit {m : Type → Type} [Monad m] (f : OpSpec → Reg → m Reg) (info : CallInfo) :
    m CallInfo := do
  let dest ← match info.dest with
    | .reg r => do pure (CallDest.reg (← f .use r))
    | d => pure d
  let uses ← info.uses.mapM fun (v, p) => do pure ((← f (.fixedUse p) v), p)
  let defs ← info.defs.mapM fun (p, v) => do pure (p, (← f (.fixedDef p) v))
  pure ⟨dest, uses, defs⟩

theorem visit_call_eq {m : Type → Type} [Monad m] [LawfulMonad m] (f : OpSpec → Reg → m Reg)
    (info : CallInfo) : MInst.visitOperands f (.call info) = MInst.call <$> callVisit f info := by
  obtain ⟨dest, uses, defs⟩ := info
  cases dest <;> simp [MInst.visitOperands, callVisit, map_bind]

/-- The call of a `try_call` visits its operands as the plain call does. -/
theorem visit_tryCall_eq {m : Type → Type} [Monad m] [LawfulMonad m] (f : OpSpec → Reg → m Reg)
    (info : CallInfo) (ti : TryInfo) :
    MInst.visitOperands f (.tryCall info ti) = (fun c => MInst.tryCall c ti) <$> callVisit f info := by
  obtain ⟨dest, uses, defs⟩ := info
  cases dest <;> simp [MInst.visitOperands, callVisit, map_bind]

/-- The call of a `try_call` has the operands of the plain call. -/
theorem operands_tryCall_call (info : CallInfo) (ti : TryInfo) :
    (MInst.tryCall info ti).operands = (MInst.call info).operands := by
  unfold MInst.operands
  dsimp only
  rw [visit_tryCall_eq, visit_call_eq, StateT.run_map, StateT.run_map]
  simp only [bind_map_left]

/-- The allocated form of a call is a call; that of the call of a `try_call` is the call of a
`try_call`, with the allocated form of the plain call. -/
theorem assign_call_tryCall (info : CallInfo) (regs : Array Reg) :
    (∀ i', (MInst.call info).assign regs = .ok i' → ∃ ic, i' = .call ic) ∧
    ∀ ti i', (MInst.tryCall info ti).assign regs = .ok i' →
      ∃ ic, i' = .tryCall ic ti ∧ (MInst.call info).assign regs = .ok (.call ic) := by
  have hb : ∀ {α β : Type} {x : Except String α} {g : α → Except String β} {b : β},
      x >>= g = .ok b → ∃ a, x = .ok a ∧ g a = .ok b := by
    intro α β x g b h
    cases x with
    | error e => cases h
    | ok a => exact ⟨a, rfl, h⟩
  unfold MInst.assign
  dsimp only
  rw [visit_call_eq, StateT.run_map]
  refine ⟨fun i' h => ?_, fun ti i' h => ?_⟩
  · simp only [bind_map_left] at h
    obtain ⟨q, -, h⟩ := hb h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨q.1, h.symm⟩
  · rw [visit_tryCall_eq, StateT.run_map] at h
    simp only [bind_map_left] at h ⊢
    obtain ⟨q, hq, h⟩ := hb h
    split at h
    · cases h
    · rename_i hk
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨q.1, h.symm, ?_⟩
      rw [hq]
      have hk' : q.2 = regs.size := by simpa using hk
      simp [bind, Except.bind, hk', pure, Except.pure]

/-- The allocated form of a call is a call. -/
theorem assign_call_form {info : CallInfo} {regs : Array Reg} {i' : MInst}
    (h : (MInst.call info).assign regs = .ok i') : ∃ ic, i' = .call ic :=
  (assign_call_tryCall info regs).1 i' h

end Backend.Proof

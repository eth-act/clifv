import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.IselContract

/-!
# The concrete instruction semantics `csem` (M6 proof)

`checkAlloc_sound` is parametric in the instruction semantics. The semantics the backend is
proven against, `csem F ctx X`, is **defined by the Arm model**: a straight-line instruction
means what its emitted code does under a *canonical* register allocation. For an instruction
`i` with operands `ops`:

* `canonRegs ops`: operand `k` of class int is `x k`, of class float `v k`; a fixed operand is
  its register; a `reuse j` def is operand `j`'s register;
* `placeUses`: the use values are written into their canonical registers of the world `w`;
* the canonical instruction `i.assign (canonRegs ops)` is run by `execMInst` (its `MInst.lines`
  expansion, `Insn.toArmInst`, `Arm.exec_inst`: M5's `Insn.sem`);
* the defs are read back from the canonical registers (`defVals`), the world is the resulting
  state (compared with `SameWorld F`, which ignores registers, the pc and the frame `F`).

A memory access must avoid the frame addresses `F` (`AccessOk`; the program never addresses
the allocator's slots), otherwise `csem` is undefined. Nothing is hand-written per
instruction, so `csem` cannot disagree with the Arm model; M4 computes through it with the
same lemmas as for the allocated code.

Instructions whose meaning is outside the function: calls (`ExtSem.call`, the callee) and
symbol addresses (`ExtSem.sym`, the linker's relocations). Control flow: branches give
`goto j`, traps `halt`, `Rets` `ret`; `Args` reads the incoming argument registers of the
world (the entry state).

The per-instruction obligation `OperandsSound` then reduces (`os_of_corr`) to `Corr`: the
allocated code, run on any state, and the canonical code, run on the canonical state, agree
(same world, same def values, other registers and the frame untouched). `corr_tac` proves
`Corr` for a concrete instruction form by computing both runs with `simp`.
-/

/-- Unfolding set for runs of emitted code (`execMInst` → `MInst.lines` → `Insn.toArmInst` →
`Arm.exec_inst`), used by the per-instruction proofs. -/
register_simp_attr csimp_rules

namespace Backend.Proof

open Backend

deriving instance ReflBEq, LawfulBEq for OperandSize, ALUOp, ALUOp3, MoveWideOp, BfmOp, BitOp,
  Cond, ExtendOp, ShiftOp, ScalarSize, VectorSize, VecMisc2, VecLanesOp, VecALUOp,
  TestBitAndBranchKind, LoadOp, StoreOp

/-! ## Canonical allocation -/

/-- Canonical register of operand `k`, ignoring `reuse`. -/
def canonBase (ops : Array Operand) (k : Nat) : Reg :=
  match ops[k]? with
  | some ⟨_, _, _, _, .fixed p⟩ => p
  | some ⟨_, .float, _, _, _⟩ => .v k
  | _ => .x k

/-- Canonical register of operand `k`: a `reuse j` def gets operand `j`'s register. -/
def canonReg (ops : Array Operand) (k : Nat) : Reg :=
  match ops[k]? with
  | some ⟨_, _, _, _, .reuse j⟩ => canonBase ops j
  | _ => canonBase ops k

def canonRegs (ops : Array Operand) : Array Reg := ⟨(List.range ops.size).map (canonReg ops)⟩

theorem beq_eq_decide' {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-- The bitmask immediate of `uxt` from one bit (`extend` from 1 bit is `and wd, wn, #1`). -/
theorem bitmaskEnc_false_one : bitmaskEnc? false 1 = some (0#1, 0#6, 0#6) := by rfl

/-- Write a value into a register (X registers get the low 64 bits). -/
def setReg (s : Arm.ArmState) : Reg → CV → Arm.ArmState
  | .x n, v => Arm.w (.GPR (rnum n)) (lo64 v) s
  | .v n, v => Arm.w (.SFP (rnum n)) v s
  | _, _ => s

/-- The world `w` with the use values in the use operands' registers `regs`. -/
def placeUses (ops : Array Operand) (regs : Array Reg) (uses : List CV) (w : Arm.ArmState) :
    Arm.ArmState :=
  ((((ops.zip regs).toList.filter (·.1.isUse)).map (·.2)).zip uses).foldl
    (fun s p => setReg s p.1 p.2) w

/-- The values of the def operands (allocated to `regs`) in state `s`. -/
def defVals (ops : Array Operand) (regs : Array Reg) (s : Arm.ArmState) : List CV :=
  ((ops.zip regs).toList.filter (·.1.isDef)).map (regVal s ·.2)

@[simp] theorem except_pure_eq {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl
@[simp] theorem except_throw_eq {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl
@[simp] theorem except_map_error {ε α β : Type} (e : ε) (f : α → β) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl
@[simp] theorem except_map_ok {ε α β : Type} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl
@[simp] theorem setReg_x (s : Arm.ArmState) (n : Nat) (v : CV) :
    setReg s (.x n) v = Arm.w (.GPR (rnum n)) (lo64 v) s := rfl
@[simp] theorem setReg_v (s : Arm.ArmState) (n : Nat) (v : CV) :
    setReg s (.v n) v = Arm.w (.SFP (rnum n)) v s := rfl

/-- The address the emitter's environment `env0` gives straight-line code (it reads no label
and no pc). -/
def env0 : Env := ⟨0, fun _ => none⟩

/-! ## Reading and writing state fields -/

@[simp] theorem r_gpr_w_gpr (i j : BitVec 5) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r (.GPR i) (Arm.w (.GPR j) v s) = if i = j then v else Arm.r (.GPR i) s := by
  split
  · subst_vars; exact Arm.r_of_w_same
  · exact Arm.r_of_w_different (by simpa)

@[simp] theorem r_sfp_w_sfp (i j : BitVec 5) (v : BitVec 128) (s : Arm.ArmState) :
    Arm.r (.SFP i) (Arm.w (.SFP j) v s) = if i = j then v else Arm.r (.SFP i) s := by
  split
  · subst_vars; exact Arm.r_of_w_same
  · exact Arm.r_of_w_different (by simpa)

@[simp] theorem r_flag_w_flag (i j : Arm.PFlag) (v : BitVec 1) (s : Arm.ArmState) :
    Arm.r (.FLAG i) (Arm.w (.FLAG j) v s) = if i = j then v else Arm.r (.FLAG i) s := by
  split
  · subst_vars; exact Arm.r_of_w_same
  · exact Arm.r_of_w_different (by simpa)

@[simp] theorem r_pc_w_pc (v : BitVec 64) (s : Arm.ArmState) : Arm.r .PC (Arm.w .PC v s) = v :=
  Arm.r_of_w_same

@[simp] theorem r_err_w_err (v : Arm.StateError) (s : Arm.ArmState) :
    Arm.r .ERR (Arm.w .ERR v s) = v := Arm.r_of_w_same

@[simp] theorem r_gpr_w_sfp (i j : BitVec 5) (v : BitVec 128) (s : Arm.ArmState) :
    Arm.r (.GPR i) (Arm.w (.SFP j) v s) = Arm.r (.GPR i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_gpr_w_pc (i : BitVec 5) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r (.GPR i) (Arm.w .PC v s) = Arm.r (.GPR i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_gpr_w_flag (i : BitVec 5) (j : Arm.PFlag) (v : BitVec 1) (s : Arm.ArmState) :
    Arm.r (.GPR i) (Arm.w (.FLAG j) v s) = Arm.r (.GPR i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_gpr_w_err (i : BitVec 5) (v : Arm.StateError) (s : Arm.ArmState) :
    Arm.r (.GPR i) (Arm.w .ERR v s) = Arm.r (.GPR i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_sfp_w_gpr (i j : BitVec 5) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r (.SFP i) (Arm.w (.GPR j) v s) = Arm.r (.SFP i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_sfp_w_pc (i : BitVec 5) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r (.SFP i) (Arm.w .PC v s) = Arm.r (.SFP i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_sfp_w_flag (i : BitVec 5) (j : Arm.PFlag) (v : BitVec 1) (s : Arm.ArmState) :
    Arm.r (.SFP i) (Arm.w (.FLAG j) v s) = Arm.r (.SFP i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_sfp_w_err (i : BitVec 5) (v : Arm.StateError) (s : Arm.ArmState) :
    Arm.r (.SFP i) (Arm.w .ERR v s) = Arm.r (.SFP i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_pc_w_gpr (j : BitVec 5) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r .PC (Arm.w (.GPR j) v s) = Arm.r .PC s := Arm.r_of_w_different (by simp)
@[simp] theorem r_pc_w_sfp (j : BitVec 5) (v : BitVec 128) (s : Arm.ArmState) :
    Arm.r .PC (Arm.w (.SFP j) v s) = Arm.r .PC s := Arm.r_of_w_different (by simp)
@[simp] theorem r_pc_w_flag (j : Arm.PFlag) (v : BitVec 1) (s : Arm.ArmState) :
    Arm.r .PC (Arm.w (.FLAG j) v s) = Arm.r .PC s := Arm.r_of_w_different (by simp)
@[simp] theorem r_pc_w_err (v : Arm.StateError) (s : Arm.ArmState) :
    Arm.r .PC (Arm.w .ERR v s) = Arm.r .PC s := Arm.r_of_w_different (by simp)
@[simp] theorem r_flag_w_gpr (i : Arm.PFlag) (j : BitVec 5) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r (.FLAG i) (Arm.w (.GPR j) v s) = Arm.r (.FLAG i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_flag_w_sfp (i : Arm.PFlag) (j : BitVec 5) (v : BitVec 128) (s : Arm.ArmState) :
    Arm.r (.FLAG i) (Arm.w (.SFP j) v s) = Arm.r (.FLAG i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_flag_w_pc (i : Arm.PFlag) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r (.FLAG i) (Arm.w .PC v s) = Arm.r (.FLAG i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_flag_w_err (i : Arm.PFlag) (v : Arm.StateError) (s : Arm.ArmState) :
    Arm.r (.FLAG i) (Arm.w .ERR v s) = Arm.r (.FLAG i) s := Arm.r_of_w_different (by simp)
@[simp] theorem r_err_w_gpr (j : BitVec 5) (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r .ERR (Arm.w (.GPR j) v s) = Arm.r .ERR s := Arm.r_of_w_different (by simp)
@[simp] theorem r_err_w_sfp (j : BitVec 5) (v : BitVec 128) (s : Arm.ArmState) :
    Arm.r .ERR (Arm.w (.SFP j) v s) = Arm.r .ERR s := Arm.r_of_w_different (by simp)
@[simp] theorem r_err_w_pc (v : BitVec 64) (s : Arm.ArmState) :
    Arm.r .ERR (Arm.w .PC v s) = Arm.r .ERR s := Arm.r_of_w_different (by simp)
@[simp] theorem r_err_w_flag (j : Arm.PFlag) (v : BitVec 1) (s : Arm.ArmState) :
    Arm.r .ERR (Arm.w (.FLAG j) v s) = Arm.r .ERR s := Arm.r_of_w_different (by simp)

theorem ofNat5_eq_iff {a b : Nat} (ha : a < 32) (hb : b < 32) :
    BitVec.ofNat 5 a = BitVec.ofNat 5 b ↔ a = b := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · rintro rfl; rfl

theorem le30_of {n : Nat} (h : n < 29) : (n ≤ 30) = True := by simp; omega
theorem le31_of {n : Nat} (h : n < 32) : (n ≤ 31) = True := by simp; omega
theorem ne31_of {n : Nat} (h : n < 29) : (BitVec.ofNat 5 n = 31#5) = False := by
  simp only [eq_iff_iff, iff_false]; exact rnum_ne31 h
theorem ne31_of' {n : Nat} (h : n < 29) : (31#5 = BitVec.ofNat 5 n) = False := by
  simp only [eq_iff_iff, iff_false]; exact fun e => rnum_ne31 h e.symm

/-! ## Worlds -/

theorem SameWorld.w_right {F} {s t : Arm.ArmState} {f : Arm.StateField} {v} (hf : Masked f)
    (h : SameWorld F s t) : SameWorld F s (Arm.w f v t) := by
  refine ⟨fun g hg => ?_, fun a ha => ?_, ?_⟩
  · have hne : g ≠ f := fun e => hg (e ▸ hf)
    rw [Arm.r_of_w_different hne]; exact h.1 g hg
  · rw [Arm.ArmState.mem_w_eq_mem]; exact h.2.1 a ha
  · rw [Arm.w_program]; exact h.2.2

theorem SameWorld.w_both {F} {s t : Arm.ArmState} {f : Arm.StateField} {v}
    (h : SameWorld F s t) : SameWorld F (Arm.w f v s) (Arm.w f v t) := by
  refine ⟨fun g hg => ?_, fun a ha => ?_, ?_⟩
  · by_cases e : g = f
    · subst e; rw [Arm.r_of_w_same, Arm.r_of_w_same]
    · rw [Arm.r_of_w_different e, Arm.r_of_w_different e]; exact h.1 g hg
  · rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]; exact h.2.1 a ha
  · rw [Arm.w_program, Arm.w_program]; exact h.2.2

theorem SameWorld.w_both' {F} {s t : Arm.ArmState} {f : Arm.StateField} {v1 v2 : Arm.state_value f}
    (hv : v1 = v2) (h : SameWorld F s t) : SameWorld F (Arm.w f v1 s) (Arm.w f v2 t) :=
  hv ▸ SameWorld.w_both h

theorem SameWorld.write_mem_bytes' {F} {s t : Arm.ArmState} {n : Nat} {a1 a2 : BitVec 64}
    {v1 v2 : BitVec (n * 8)} (ha : a1 = a2) (hv : v1 = v2) (h : SameWorld F s t) :
    SameWorld F (Arm.write_mem_bytes n a1 v1 s) (Arm.write_mem_bytes n a2 v2 t) :=
  ha ▸ hv ▸ SameWorld.write_mem_bytes h n a1 v1

theorem SameWorld.ite_both {F} {c : Prop} [Decidable c] {s s' t t' : Arm.ArmState}
    (h1 : c → SameWorld F s t) (h2 : ¬c → SameWorld F s' t') :
    SameWorld F (if c then s else s') (if c then t else t') := by
  by_cases hc : c <;> simp [hc, h1, h2]

theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  rcases x with ⟨⟨_ | _ | n, h⟩⟩
  · left; rfl
  · right; rfl
  · simp at h; omega

theorem SameWorld.symm {F} {s t : Arm.ArmState} (h : SameWorld F s t) : SameWorld F t s :=
  ⟨fun f hf => (h.1 f hf).symm, fun a ha => (h.2.1 a ha).symm, h.2.2.symm⟩

theorem SameWorld.trans {F} {s t u : Arm.ArmState} (h1 : SameWorld F s t) (h2 : SameWorld F t u) :
    SameWorld F s u :=
  ⟨fun f hf => (h1.1 f hf).trans (h2.1 f hf), fun a ha => (h1.2.1 a ha).trans (h2.2.1 a ha),
    h1.2.2.trans h2.2.2⟩

theorem read_mem_bytes_sameWorld {F} {s t : Arm.ArmState} (h : SameWorld F s t) {n : Nat}
    {a : BitVec 64} (hav : Avoids F n a) : Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a t :=
  read_mem_bytes_congr n a (fun k hk => h.2.1 _ (hav k hk))

/-! ## Allocation facts -/

/-- What the static checks give about the register of one operand. -/
def RegFits (o : Operand) (r : Reg) : Prop :=
  (match o.cls with
   | .int => ∃ n, r = .x n ∧ n < 29 ∧ n ≠ 16 ∧ n ≠ 17 ∧ n ≠ 18
   | .float => ∃ n, r = .v n ∧ n < 32) ∧
  (∀ p, o.con = .fixed p → r = p)

/-- The facts about a register allocation of one instruction that its static checks
(`CheckCtx.checkStatic`) establish. -/
structure AllocOk (ops : Array Operand) (regs : Array Reg) : Prop where
  size : regs.size = ops.size
  fits : ∀ p ∈ (ops.zip regs).toList, RegFits p.1 p.2
  reuse : ∀ k j : Nat, (ops[k]?).map (fun o : Operand => o.con) = some (Constraint.reuse j) →
    regs[k]? = regs[j]?
  nodup : (((ops.zip regs).toList.filter (·.1.isDef)).map (·.2)).Nodup
  early : ∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.1.isEarly = true →
    ∀ q ∈ (ops.zip regs).toList, q.1.isUse = true → p.2 ≠ q.2

theorem regFits_of_locOk {c : CheckCtx} {o : Operand} {r : Reg}
    (h : c.locOk (.reg r) o.cls = true) (hf : ∀ p, o.con = .fixed p → Loc.reg r = .reg p) :
    RegFits o r := by
  simp only [CheckCtx.locOk, Loc.cls?, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨?_, fun p hp => by simpa using hf p hp⟩
  rcases allocatable_cases h.2 with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
  · cases hc : o.cls <;> simp_all [Reg.realClass?]
  · cases hc : o.cls <;> simp_all [Reg.realClass?]

theorem allocOk_of_checkStatic {c : CheckCtx} {wh : String} {ops : Array Operand}
    {regs : Array Reg} {clob : List Reg} (h : c.checkStatic wh ops (regs.map .reg) clob = .ok ()) :
    AllocOk ops regs := by
  obtain ⟨hsz, hloc, hnd, -⟩ := checkStatic_facts h
  have hsz' : regs.size = ops.size := by simpa using hsz.symm
  unfold CheckCtx.checkStatic at h
  obtain ⟨-, h⟩ := Except.seq_ok h
  dsimp only at h
  obtain ⟨h2, h⟩ := Except.seq_ok h
  obtain ⟨-, h⟩ := Except.seq_ok h
  obtain ⟨h4, _⟩ := Except.seq_ok h
  refine ⟨hsz', ?_, ?_, ?_, ?_⟩
  · intro p hp
    have := hloc (p.1, .reg p.2) (by rw [pairs_regs]; exact List.mem_map_of_mem hp)
    exact regFits_of_locOk this.1 this.2
  · intro k j hk
    cases hok : ops[k]? with
    | none => simp [hok] at hk
    | some o =>
      simp only [hok, Option.map_some, Option.some.injEq] at hk
      have hkl : k < ops.size := by
        rcases Array.getElem?_eq_some_iff.mp hok with ⟨hk', _⟩; exact hk'
      have hkr : k < regs.size := by omega
      have hz : (((o, Loc.reg regs[k]), k)) ∈ (ops.zip (regs.map Loc.reg)).toList.zipIdx := by
        apply List.mem_zipIdx_iff_getElem?.mpr
        rw [Array.getElem?_toList, Array.getElem?_zip_eq_some]
        simp [hok, hkr]
      have hc := forM_ok h2 _ hz
      unfold CheckCtx.checkOperand at hc
      obtain ⟨-, hc⟩ := Except.seq_ok hc
      rw [hk] at hc
      simp only at hc
      split at hc
      · rename_i oi li hoi hli
        have := ensure_ok hc
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        simp only [Array.getElem?_map] at hli
        cases hj : regs[j]? with
        | none => simp [hj] at hli
        | some rj =>
          simp only [hj, Option.map_some, Option.some.injEq] at hli
          subst hli
          simp only [Loc.reg.injEq] at this
          simp [Array.getElem?_eq_getElem hkr, this.2]
      · cases hc
  · have : (((ops.zip regs).toList.filter (·.1.isDef)).map (·.2)).map Loc.reg =
        ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.kind == .def)).map (·.2) := by
      rw [pairs_regs, List.filter_map, List.map_map, List.map_map]
      rfl
    exact List.Pairwise.of_map Loc.reg (fun a b h e => h (by rw [e])) (this ▸ hnd)
  · intro p hp hd he q hq hu e
    have hd' : (p.1, Loc.reg p.2) ∈ (ops.zip (regs.map Loc.reg)).toList.filter (·.1.kind == .def) := by
      rw [pairs_regs]
      exact List.mem_filter.mpr ⟨List.mem_map_of_mem hp, by simpa [Operand.isDef] using hd⟩
    have := ensure_ok (forM_ok h4 _ hd')
    have hmem : Loc.reg p.2 ∈ defConflicts ((ops.zip (regs.map Loc.reg)).toList.filter
        (·.1.kind == .use)) (clob.map Loc.reg) p.1.pos := by
      have hpos : p.1.pos = .early := by simpa [Operand.isEarly] using he
      rw [hpos]
      simp only [defConflicts, List.mem_append, List.mem_map]
      left
      refine ⟨(q.1, Loc.reg q.2), ?_, by simp [e]⟩
      rw [pairs_regs]
      exact List.mem_filter.mpr ⟨List.mem_map_of_mem hq, by simpa [Operand.isUse] using hu⟩
    simp only [Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false,
      beq_iff_eq] at this
    exact this _ hmem rfl

/-! ## Memory accesses -/

/-- The 64-bit value of a GPR operand (`sp` is register 31 as a base, `xzr` reads 0). -/
def regX (s : Arm.ArmState) : Reg → BitVec 64
  | .x n => Arm.r (.GPR (rnum n)) s
  | .sp => spOf s
  | _ => 0

/-- The effective address of an (unfinalised) addressing mode for an access of `bytes`
bytes. -/
def _root_.Backend.AMode.addr (ctx : FnCtx) (m : AMode) (bytes : Nat) (s : Arm.ArmState) : BitVec 64 :=
  match m with
  | .regOffset rn off => regX s rn + BitVec.ofInt 64 off
  | .spOffset off => spOf s + BitVec.ofInt 64 off
  | .fpOffset off => regX s (.x 29) + BitVec.ofInt 64 off
  | .slotOffset off => spOf s + BitVec.ofInt 64 (off + ctx.slotBase)
  | .unscaled rn off => regX s rn + BitVec.ofInt 64 off
  | .unsignedOffset rn off => regX s rn + BitVec.ofNat 64 off
  | .regReg rn rm => regX s rn + regX s rm
  | .regScaled rn rm => regX s rn + regX s rm <<< log2 bytes
  | .regScaledExtended rn rm e =>
    regX s rn + Arm.extend_reg (regX s rm) (Arm.decode_reg_extend e.bits) (log2 bytes)
  | .regExtended rn rm e =>
    regX s rn + Arm.extend_reg (regX s rm) (Arm.decode_reg_extend e.bits) 0
  | .spPreIndexed off => spOf s + BitVec.ofInt 64 off
  | .spPostIndexed _ => spOf s
  | .incomingArg _ => 0

/-- Memory accesses `(address, bytes)` of an allocated instruction in state `s`. -/
def _root_.Backend.MInst.accesses (ctx : FnCtx) : MInst → Arm.ArmState → List (BitVec 64 × Nat)
  | .load op _ m _, s => [(m.addr ctx op.bytes s, op.bytes)]
  | .store op _ m _, s => [(m.addr ctx op.bytes s, op.bytes)]
  | .loadAcquire ty _ rn _, s | .storeRelease ty _ rn _, s => [(regX s rn, ty.bytes)]
  | _, _ => []

/-- Every memory access of `i` in state `s` avoids the frame addresses `F`. -/
def AccessOk (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (s : Arm.ArmState) : Prop :=
  ∀ p ∈ i.accesses ctx s, Avoids F p.2 p.1

/-! ## The semantics -/

/-- What the function's code relies on outside itself: callees (`call d args w`: the results
and the world after the call; `d = some name` for `bl name`, `none` for `blr`, whose target
address is the first argument), link-time symbol addresses (`sym name addend`), and for
`tls_value` (agent/stack-tls-proof; one thread, whose instance of a thread-local variable is
its link-time symbol) the thread pointer `tp` (`TPIDR_EL0`) and the condition flags the TLSDESC
call of symbol `n` leaves from world `w` (`tlsFlags n w`: the resolver may change them). -/
structure ExtSem where
  call : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState)
  sym : String → Int → BitVec 64
  tp : BitVec 64
  tlsFlags : String → Arm.ArmState → Arm.PState

/-! ## Covered forms -/

/-- The extend kinds of an encodable extended-register addressing mode. -/
def extOk (e : ExtendOp) : Prop := e = .uxtw ∨ e = .uxtx ∨ e = .sxtw ∨ e = .sxtx

instance (e : ExtendOp) : Decidable (extOk e) := by unfold extOk; infer_instance

/-- The forms `csem` gives an explicit meaning (control flow, calls, symbols, `Args`/`Rets`, the
LL/SC loops); every other form is `straightSem`. -/
def _root_.Backend.MInst.isCtl : MInst → Bool
  | .call .. | .args .. | .rets .. | .loadExtNameGot .. | .loadExtNameNear .. | .jump ..
  | .condBr .. | .testBitAndBranch .. | .trapIf .. | .udf .. | .emitIsland .. | .jtSequence ..
  | .tryCall .. | .atomicRmwLoop .. | .atomicCasLoop .. | .elfTlsGetAddr .. => true
  | _ => false

/-- `aluRRImmLogic` ops the emitter expands. -/
def logicOpOk : ALUOp → Bool
  | .orr | .and | .andS | .eor | .orrNot | .andNot | .eorNot => true
  | _ => false

/-- `aluRRImmShift` ops the emitter expands. -/
def shiftOpOk : ALUOp → Bool
  | .lsr | .asr | .lsl | .extr => true
  | _ => false

/-- The bitmask immediate `v` (at `is64`) has an encoding (`bitmaskEnc?`) that Arm's
`DecodeBitMasks` at width `M` decodes to `e` (with `N = 0` for a 32-bit instruction). -/
def bitmaskOk (M : Nat) (is64 : Bool) (v : Nat) (e : BitVec M) : Bool :=
  match bitmaskEnc? is64 v with
  | none => false
  | some (N, immr, imms) =>
    match Arm.decode_bit_masks N imms immr true M with
    | none => false
    | some (wm, _) => (is64 || N == 0#1) && wm == e

/-- The logical immediate of `aluRRImmLogic op sz _ _ imm` as the emitter encodes it (the
inverted value for `orn`/`bic`/`eon`, the low 32 bits at 32 bits) decodes to the operand
`ispec` states. A per-instruction check (translation validation of `bitmaskEnc?`). -/
def logicImmOk (op : ALUOp) (sz : OperandSize) (imm : ImmLogic) : Bool :=
  match op, sz with
  | .orrNot, .size32 | .andNot, .size32 | .eorNot, .size32 =>
    bitmaskOk 32 false (mask64 imm.invert.value % 2 ^ 32) (~~~(BitVec.ofNat 32 imm.value))
  | .orrNot, .size64 | .andNot, .size64 | .eorNot, .size64 =>
    bitmaskOk 64 true (mask64 imm.invert.value) (~~~(BitVec.ofNat 64 imm.value))
  | _, .size32 => bitmaskOk 32 false (mask64 imm.value % 2 ^ 32) (BitVec.ofNat 32 imm.value)
  | _, .size64 => bitmaskOk 64 true (mask64 imm.value) (BitVec.ofNat 64 imm.value)

/-- The covered addressing modes of a load/store of `bytes` bytes (`amodeAddr`'s forms). -/
def memOk (bytes : Nat) : AMode → Bool
  | .slotOffset _ | .spOffset _ | .fpOffset _ => true
  | .unscaled (.vreg _ .int) off => decide (-256 ≤ off ∧ off < 256)
  | .unsignedOffset (.vreg _ .int) off => decide (off % bytes = 0 ∧ off / bytes < 4096)
  | .regReg (.vreg _ .int) (.vreg _ .int) | .regScaled (.vreg _ .int) (.vreg _ .int) => true
  | .regScaledExtended (.vreg _ .int) (.vreg _ .int) e | .regExtended (.vreg _ .int) (.vreg _ .int) e =>
    decide (extOk e)
  | _ => false

instance (ty : CTy) : Decidable (AtomTy ty) := by unfold AtomTy; infer_instance

/-- **The covered straight-line forms.** A zero-register destination is register 31 in the
encoding, which the immediate and extended-register `add`/`sub` and the logical-immediate forms
read as `sp` unless they set the flags: those are covered only as `adds`/`subs`/`ands`. A logical
immediate is covered when its encoding decodes back to it (`logicImmOk`). -/
def FormOk (_ctx : FnCtx) : MInst → Bool
  | .aluRRR _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) => true
  | .aluRRR _ _ (.vreg _ .int) .xzr (.vreg _ .int) => true
  | .aluRRR _ _ .xzr (.vreg _ .int) (.vreg _ .int) => true
  | .aluRRR _ _ (.vreg _ .int) (.vreg _ .int) .xzr => true
  | .aluRRR _ _ .xzr (.vreg _ .int) .xzr => true
  | .aluRRRR _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) => true
  | .aluRRRR _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) .xzr => true
  | .aluRRImm12 _ _ (.vreg _ .int) (.vreg _ .int) _ => true
  | .aluRRImm12 op _ .xzr (.vreg _ .int) _ => op == .addS || op == .subS
  | .aluRRImmLogic op sz (.vreg _ .int) (.vreg _ .int) imm => logicOpOk op && logicImmOk op sz imm
  | .aluRRImmLogic op sz .xzr (.vreg _ .int) imm => op == .andS && logicImmOk op sz imm
  | .aluRRImmShift op _ (.vreg _ .int) (.vreg _ .int) _ => shiftOpOk op
  | .aluRRRShift _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) _ => true
  | .aluRRRShift _ _ .xzr (.vreg _ .int) (.vreg _ .int) _ => true
  | .aluRRRShift _ _ (.vreg _ .int) .xzr (.vreg _ .int) _ => true
  | .aluRRRExtend _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) _ => true
  | .aluRRRExtend op _ .xzr (.vreg _ .int) (.vreg _ .int) _ => op == .addS || op == .subS
  | .bitRR _ _ (.vreg _ .int) (.vreg _ .int) => true
  | .mov _ (.vreg _ .int) (.vreg _ .int) => true
  | .movWide _ (.vreg _ .int) _ _ => true
  | .movK (.vreg _ .int) (.vreg _ .int) _ _ => true
  | .extend (.vreg _ .int) (.vreg _ .int) _ _ _ => true
  | .bitfieldMove _ _ (.vreg _ .int) (.vreg _ .int) _ _ => true
  | .cset (.vreg _ .int) _ => true
  | .csel (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) _ => true
  | .ccmp _ (.vreg _ .int) (.vreg _ .int) _ _ => true
  | .ccmpImm _ (.vreg _ .int) _ _ _ => true
  | .movToFpu (.vreg _ .float) (.vreg _ .int) _ => true
  | .movFromVec (.vreg _ .int) (.vreg _ .float) _ _ => true
  | .vecMisc _ (.vreg _ .float) (.vreg _ .float) _ => true
  | .vecLanes _ (.vreg _ .float) (.vreg _ .float) _ => true
  | .vecRRR _ (.vreg _ .float) (.vreg _ .float) (.vreg _ .float) _ => true
  | .load op (.vreg _ .int) m _ => op != .fpuLoad128 && memOk op.bytes m
  | .store op (.vreg _ .int) m _ => op != .fpuStore128 && memOk op.bytes m
  | .loadAddr (.vreg _ .int) (.slotOffset _) => true
  | .aluRRImmLogic op sz (.vreg _ .int) .xzr imm => logicOpOk op && logicImmOk op sz imm
  -- `csetm` (`bmask`), `dmb ish` (`fence`), `ldar`/`stlr`
  | .csetm (.vreg _ .int) _ => true
  | .fence => true
  | .loadAcquire ty (.vreg _ .int) (.vreg _ .int) _ => decide (AtomTy ty)
  | .storeRelease ty (.vreg _ .int) (.vreg _ .int) _ => decide (AtomTy ty)
  | _ => false

/-- The number of use operands. -/
def useCount (ops : Array Operand) : Nat := (ops.toList.filter (·.isUse)).length

/-- The instances on which `csem` is the Arm run of the canonical allocation: a covered form
(`FormOk`) applied to as many values as it has use operands. -/
def csemWF (ctx : FnCtx) (i : MInst) (uses : List CV) : Bool :=
  FormOk ctx i && match i.operands with
    | .ok ops => uses.length == useCount ops
    | .error _ => false

open Classical in
/-- A straight-line instruction: the Arm run of its canonical allocation (which must end
without error, with the program unchanged). -/
noncomputable def straightSem (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (uses : List CV)
    (w : Arm.ArmState) : Option (List CV × Arm.ArmState × Ctl) :=
  match i.operands with
  | .error _ => none
  | .ok ops =>
    match i.assign (canonRegs ops) with
    | .error _ => none
    | .ok ic =>
      if AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w) then
        match execMInst ctx env0 ic (placeUses ops (canonRegs ops) uses w) with
        | some t' =>
          if Arm.r .ERR t' = .None ∧ t'.program = w.program then
            some (defVals ops (canonRegs ops) t', t', .next)
          else none
        | none => none
      else none

/-- The condition of a `CondBrKind` on the use values and the world (flags). -/
def _root_.Backend.CondBrKind.holds (k : CondBrKind) (uses : List CV) (w : Arm.ArmState) : Bool :=
  match k, uses with
  | .cond c, _ => Arm.ConditionHolds c.bits w
  | .zero _ sz, [a] => if sz.is64 then lo64 a == 0 else (lo64 a).setWidth 32 == 0
  | .notZero _ sz, [a] => if sz.is64 then lo64 a != 0 else (lo64 a).setWidth 32 != 0
  | _, _ => false

/-- The specification fallback of `csem` (worlds with an error or a misaligned `sp`, forms
not covered by `FormOk`): `ispec`, extended by the memory forms as `MemRefines` states them
(slot offsets at slot base `sb`). -/
def mspec (sb : Nat) : Sem := fun i uses w =>
  match i, uses with
  | .load op (.vreg _ .int) am _, us =>
    if op = .fpuLoad128 then none
    else (amodeAddr sb am op.bytes us w).map fun a => ([ofX (loadVal op a w)], w, .next)
  | .store op (.vreg _ .int) am _, v :: us =>
    if op = .fpuStore128 then none
    else (amodeAddr sb am op.bytes us w).map fun a =>
      ([], Arm.write_mem_bytes op.bytes a ((lo64 v).setWidth (op.bytes * 8)) w, .next)
  | .loadAddr (.vreg _ .int) (.slotOffset off), [] =>
    some ([ofX (spOf w + BitVec.ofInt 64 (off + sb))], w, .next)
  | .loadAcquire ty (.vreg _ .int) (.vreg _ .int) _, [u] =>
    if AtomTy ty then some ([ofX ((Arm.read_mem_bytes ty.bytes (lo64 u) w).setWidth 64)], w, .next)
    else none
  | .storeRelease ty (.vreg _ .int) (.vreg _ .int) _, [u, v] =>
    if AtomTy ty then
      some ([], Arm.write_mem_bytes ty.bytes (lo64 u) ((lo64 v).setWidth (ty.bytes * 8)) w, .next)
    else none
  | i, us => ispec i us w

open Classical in
/-- The meaning of an LL/SC loop: its body (`ldaxr` … `stlxr`, without the loop label and the
back edge) run once on the world with the use values in the fixed use registers (`regs`), when
the access avoids the frame addresses `F` and the run ends without error, with the program
unchanged: in the single-threaded Arm model the exclusive store succeeds (`stlxr`'s status
register is 0, so the `cbnz` back edge is not taken; `docs/decisions/arm-model.md`). The defs
are read back from their fixed registers (x27, then the scratch registers, whose values the
allocated-code semantics havocs, `MInst.keptDefs`). -/
noncomputable def loopSem (F : BitVec 64 → Prop) (ty : CTy) (a : CV) (body : List Line)
    (regs : List Reg) (uses : List CV) (defs : List Reg) (w : Arm.ArmState) :
    Option (List CV × Arm.ArmState × Ctl) :=
  if AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧ Arm.r .ERR w = .None then
    match execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w) with
    | some t' =>
      if Arm.r .ERR t' = .None ∧ t'.program = w.program then some (defs.map (regVal t'), t', .next)
      else none
    | none => none
  else none

open Classical in
/-- **The concrete instruction semantics.** -/
noncomputable def csem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : ISem CV Arm.ArmState :=
  fun i uses w =>
  match i with
  | .call info =>
    (X.call (match info.dest with | .sym n => some n | .reg _ => none) uses w).map
      fun p => (p.1, p.2, .next)
  -- the call of a `try_call`, returning normally (the only way `Clif.run` resumes after it):
  -- the callee's results (`X.call`), then values for the def registers beyond them (the
  -- exception payload registers x0/x1 that are not return registers, unconstrained on a normal
  -- return: the allocated-code semantics havocs them there, `havocFrom`, so these values from
  -- the callee's world are never compared with the machine's), and the normal-return successor
  -- (the last, number `ti.handlers.length`)
  | .tryCall info ti =>
    (X.call (match info.dest with | .sym n => some n | .reg _ => none) uses w).map
      fun p => (p.1 ++ (info.defs.drop p.1.length).map (fun d => regVal p.2 d.1), p.2,
        .goto ti.handlers.length)
  | .args ds => some (ds.map (fun p => regVal w p.2), w, .next)
  | .rets _ => some ([], w, .ret)
  | .loadExtNameGot _ n => some ([ofX (X.sym n 0)], w, .next)
  | .loadExtNameNear _ n off => some ([ofX (X.sym n off)], w, .next)
  -- `tls_value` (one thread): the variable's address (its link-time symbol) in the first def,
  -- the thread pointer (`mrs tmp, tpidr_el0`) in the second, the flags as the TLSDESC call
  -- leaves them
  | .elfTlsGetAddr n _ _ => some ([ofX (X.sym n 0), ofX X.tp], Arm.write_pstate (X.tlsFlags n w) w, .next)
  | .jump _ => some ([], w, .goto 0)
  | .condBr _ _ k => some ([], w, .goto (if k.holds uses w then 0 else 1))
  | .testBitAndBranch k _ _ _ bit =>
    match uses with
    | [a] => some ([], w, .goto (if ((lo64 a).getLsbD bit == (k == .nz)) then 0 else 1))
    | _ => none
  | .trapIf k _ => some ([], w, if k.holds uses w then .halt else .next)
  | .udf _ => some ([], w, .halt)
  | .emitIsland _ => some ([], w, .next)
  | .jtSequence _ ts _ _ _ =>
    -- `b.hs default` on the flags of the preceding bounds check, else the table entry of the
    -- index's low 32 bits. The temporaries' values are unspecified (dead after the branch).
    match uses with
    | [a] =>
      if Arm.ConditionHolds Cond.hs.bits w then some ([ofX 0, ofX 0], w, .goto 0)
      else
        let i := ((lo64 a).setWidth 32).toNat
        if i < ts.length then some ([ofX 0, ofX 0], w, .goto (i + 1)) else none
    | _ => none
  -- the LL/SC loops, once through their body: `atomic_rmw`'s `ldaxr; op; stlxr`;
  -- `atomic_cas`'s `ldaxr; cmp`, then (equal values: `b.ne` not taken) the `stlxr`
  -- (on a world with an error, the specification: the old value, the store)
  | .atomicRmwLoop ty op fl _ _ _ _ _ =>
    match uses with
    | [u, x] =>
      if Arm.r .ERR w = .None then
        loopSem F ty u (rmwLoopBody ty.bits op fl) [.x 25, .x 26] [u, x] [.x 27, .x 24, .x 28] w
      else if AtomTy ty ∧ Avoids F ty.bytes (lo64 u) then
        let old := Arm.read_mem_bytes ty.bytes (lo64 u) w
        some ([ofX (old.setWidth 64), ofX 0, ofX 0], Arm.write_mem_bytes ty.bytes (lo64 u)
          (Clif.Sem.atomicRmw op.clif old ((lo64 x).setWidth (ty.bytes * 8))) w, .next)
      else none
    | _ => none
  | .atomicCasLoop ty fl _ _ _ _ _ =>
    match uses with
    | [u, e, x] =>
      if Arm.r .ERR w = .None then
        match loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x]
            [.x 27, .x 24] w with
        | some (outs, t1, _) =>
          if Arm.ConditionHolds Cond.ne.bits t1 then some (outs, t1, .next)
          else loopSem F ty u [.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode] [] []
            [.x 27, .x 24] t1
        | none => none
      else if AtomTy ty ∧ Avoids F ty.bytes (lo64 u) then
        let old := Arm.read_mem_bytes ty.bytes (lo64 u) w
        some ([ofX (old.setWidth 64), ofX 0],
          if old = (lo64 e).setWidth (ty.bytes * 8) then
            Arm.write_mem_bytes ty.bytes (lo64 u) ((lo64 x).setWidth (ty.bytes * 8)) w
          else w, .next)
      else none
    | _ => none
  | i => if csemWF ctx i uses = true ∧ Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w then
      straightSem F ctx i uses w
    else mspec ctx.slotBase i uses w

theorem csem_of_wf {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    (h : i.isCtl = false) (hw : csemWF ctx i uses = true) {w : Arm.ArmState}
    (he : Arm.r .ERR w = .None) (ha : Arm.CheckSPAlignment w) :
    csem F ctx X i uses w = straightSem F ctx i uses w := by
  cases i <;> first | (simp [csem, hw, he, ha]; done) | cases h

/-- `csem` of a straight-line form: the canonical run on a well-formed, error-free, aligned
world, else the specification fallback. -/
theorem csem_straight {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (h : i.isCtl = false) (uses : List CV) (w : Arm.ArmState) :
    csem F ctx X i uses w =
      if csemWF ctx i uses = true ∧ Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w then
        straightSem F ctx i uses w
      else mspec ctx.slotBase i uses w := by
  cases i <;> first | rfl | cases h

theorem len_filter_zip : ∀ (L : List Operand) (R : List Reg), L.length = R.length →
    ((L.zip R).filter (fun p => p.1.isUse)).length = (L.filter (·.isUse)).length
  | [], _, _ => rfl
  | a :: L, [], h => by simp at h
  | a :: L, r :: R, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have := len_filter_zip L R h
    simp only [List.zip_cons_cons, List.filter_cons]
    split <;> simp_all

theorem useVals_length (ops : Array Operand) (regs : Array Reg) (h : regs.size = ops.size)
    (s : Arm.ArmState) : (useVals ops regs s).length = useCount ops := by
  simp only [useVals, useCount, List.length_map, Array.toList_zip]
  exact len_filter_zip _ _ (by simp [h])

theorem csem_useVals {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {ops : Array Operand}
    (hops : i.operands = .ok ops) (hfo : FormOk ctx i = true) (hctl : i.isCtl = false)
    {regs : Array Reg} (h : regs.size = ops.size) (s : Arm.ArmState) {w : Arm.ArmState}
    (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) :
    csem F ctx X i (useVals ops regs s) w = straightSem F ctx i (useVals ops regs s) w :=
  csem_of_wf hctl (by simp [csemWF, hfo, hops, useVals_length ops regs h]) he hal

/-! ## Reduction of `OperandsSound` to `Corr` -/

/-- The per-form obligation: the allocated instruction `mk regs`, run on `s`, corresponds to
the canonical one run on the canonical state built from a world `w` of `s`. -/
def Corr (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (ops : Array Operand)
    (mk : Array Reg → MInst) : Prop :=
  ∀ (regs : Array Reg) (s w t' : Arm.ArmState), AllocOk ops regs → SameWorld F s w →
    Arm.CheckSPAlignment s →
    AccessOk F ctx (mk (canonRegs ops)) (placeUses ops (canonRegs ops) (useVals ops regs s) w) →
    execMInst ctx env0 (mk (canonRegs ops)) (placeUses ops (canonRegs ops) (useVals ops regs s) w) =
      some t' → Arm.r .ERR t' = .None →
    ∃ s', execMInst ctx env (mk regs) s = some s' ∧ SameWorld F s' t' ∧ FrameKeep F s s' ∧
      defVals ops regs s' = defVals ops (canonRegs ops) t' ∧
      ∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        regVal s' r = regVal s r

theorem mem_zip_map {α β : Type} {f : α → β} :
    ∀ {L : List α} {p : α × β}, p ∈ L.zip (L.map f) → p.2 = f p.1
  | [], _, h => by simp at h
  | a :: L, p, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_zip_map h

theorem canonRegs_size (ops : Array Operand) : (canonRegs ops).size = ops.size := by
  simp [canonRegs]

/-- **`Corr` gives `OperandsSound`** for a straight-line instruction without clobbers. -/
theorem os_of_corr {F : BitVec 64 → Prop} {ctx : FnCtx} {env : Env} {X : ExtSem} {i : MInst}
    {ops : Array Operand} (hops : i.operands = .ok ops) (mk : Array Reg → MInst)
    (hmk : ∀ regs : Array Reg, regs.size = ops.size → i.assign regs = .ok (mk regs))
    (hfo : FormOk ctx i = true) (hctl : i.isCtl = false) (hcl : i.clobbers = [])
    (hc : Corr F ctx env ops mk) :
    OperandsSound F (execMInst ctx env) (csem F ctx X) i := by
  intro c wh ops' regs i' s w outs w' hops' hst hasg hw hal herr hsem
  rw [hops] at hops'
  cases hops'
  have ha := allocOk_of_checkStatic hst
  rw [hmk regs ha.size] at hasg
  cases hasg
  rw [csem_useVals hops hfo hctl ha.size s (by rw [← herr]; exact (hw.1 .ERR (by simp [Masked])).symm)
    (by simpa [Arm.CheckSPAlignment, Arm.read_gpr, (hw.1 (.GPR 31#5) (by simp [Masked])).symm]
      using hal)] at hsem
  simp only [straightSem, hops, hmk _ (canonRegs_size ops)] at hsem
  split at hsem
  · rename_i hacc
    split at hsem
    · rename_i t' ht
      split at hsem
      · rename_i herr
        simp only [Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, -⟩ := hsem
        obtain ⟨s', hs', hW, hK, hD, hO⟩ := hc regs s w t' ha hw hal hacc ht herr.1
        refine ⟨s', hs', hW, hK, ?_, fun r hr hnd _ => hO r hr hnd, fun r hr => by simp [hcl] at hr⟩
        intro p hp
        rw [defRegs, ← hD, defVals] at hp
        exact (mem_zip_map hp).symm
      · simp at hsem
    · simp at hsem
  · simp at hsem

/-- What a defined straight-line step gives: control `next`, a world without error, the same
program. -/
theorem straightSem_some {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} {uses : List CV}
    {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState} {ctl : Ctl}
    (h : straightSem F ctx i uses w = some (outs, w', ctl)) :
    ctl = .next ∧ Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold straightSem at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · rename_i herr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl, rfl⟩ := h
            exact ⟨rfl, herr.1, herr.2⟩
          · cases h
        · cases h
      · cases h

/-! ## Tactics -/

/-- `FormOk` of a concrete covered form. -/
syntax "fo_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| fo_tac) => `(tactic| first
    | rfl
    | (simp_all [FormOk, memOk, extOk, logicOpOk, shiftOpOk]; done)
    | (simp_all [FormOk, memOk, extOk, logicOpOk, shiftOpOk]; omega))

theorem regs1 {regs : Array Reg} (h : regs.size = 1) : ∃ a, regs = #[a] := by
  rcases regs with ⟨_ | ⟨a, _ | ⟨_, _⟩⟩⟩ <;> simp at h
  exact ⟨a, rfl⟩

theorem regs2 {regs : Array Reg} (h : regs.size = 2) : ∃ a b, regs = #[a, b] := by
  rcases regs with ⟨_ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, rfl⟩

theorem regs3 {regs : Array Reg} (h : regs.size = 3) : ∃ a b c, regs = #[a, b, c] := by
  rcases regs with ⟨_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, rfl⟩

theorem regs4 {regs : Array Reg} (h : regs.size = 4) : ∃ a b c d, regs = #[a, b, c, d] := by
  rcases regs with ⟨_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, rfl⟩

end Backend.Proof

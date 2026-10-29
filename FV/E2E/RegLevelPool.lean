import FV.E2E.RegLevelBranch
import FV.E2E.RegLevelCall
import FV.Backend.Proof.RelaxLayout
import FV.Backend.Proof.EncodeBranch
import FV.E2E.RegLevelReadsIn

/-!
# The literal-pool load on the machine (#565)

`fpuLoad sz rd (.const v)` (the pool rule of `constant_f64`) is the `ldr s/d, <entry>` of the
constant-pool entry of `v` (`AMode.Const`: the entry's `u64` value). `csem` gives it the entry's
value (`poolVal`) without reading the world; the machine reads the entry from the function's
code, which every state of the activation holds (`StRel.code`, from the ABI entry's `code` and kept
by every step):

* `poolLines_entry`, `RL.poolEntry`: every entry a literal load of the emitted body names is laid
  out in the pool after the body, as its label followed by its two little-endian words;
* `RL.poolRead`: in a state holding the code words, the bytes at the entry's label are `v`'s;
* `poolExec`, `os_poolLoad`: the operand-view obligation against `poolExec` (the def gets
  `poolVal`, the pc advances by 4), for every state;
* `RL.exec_poolLoad`: at the line of the literal load, in a state holding the code words, the
  line's `ldr (literal)` (as the layout encodes it, `R.envOf j`) runs as `poolExec`;
* `realizes_poolLoad`: the `op`/`next` case of `Realizes` for the literal load, an instance of
  `realizes_op_coreX`, its one state `GoodX` (D2: the load reads two `.data` lines, `RL.ReadOk`).
-/

namespace Backend.Proof

open Backend E2E

/-! ## The pool's layout -/

/-- **Every entry of the pool is laid out** as its label followed by its two little-endian words. -/
theorem poolLines_entry {v : Nat} : ∀ {ns : List Nat} {off : Nat}, v ∈ ns →
    ∃ i, (poolLines ns off)[i]? = some (.label (.const v)) ∧
      (poolLines ns off)[i + 1]? = some (.data (v % 2 ^ 32)) ∧
      (poolLines ns off)[i + 2]? = some (.data (v / 2 ^ 32 % 2 ^ 32))
  | [], _, h => by cases h
  | n :: ns, off, h => by
    generalize hpad : (if off % 8 == 0 then ([] : List Line) else [Line.data 0]) = pad
    have e : poolLines (n :: ns) off =
        pad ++ ([.label (.const n), .data (n % 2 ^ 32), .data (n / 2 ^ 32 % 2 ^ 32)] ++
          poolLines ns (off + 4 * pad.length + 8)) := by
      rw [← hpad]; simp [poolLines]
    rw [e]
    by_cases hv : v = n
    · subst hv
      refine ⟨pad.length, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_right (by omega)]; simp
      · rw [List.getElem?_append_right (by omega)]; simp
      · rw [List.getElem?_append_right (by omega)]; simp
    · obtain ⟨i, h1, h2, h3⟩ := poolLines_entry (ns := ns) (off := off + 4 * pad.length + 8)
        (by simpa [hv] using h)
      refine ⟨pad.length + 3 + i, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega)]
        simpa [show pad.length + 3 + i - pad.length - 3 = i by omega] using h1
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega)]
        simpa [show pad.length + 3 + i + 1 - pad.length - 3 = i + 1 by omega] using h2
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega)]
        simpa [show pad.length + 3 + i + 2 - pad.length - 3 = i + 2 by omega] using h3

/-- **The entry of a literal load is in the function's code**: the line of the load's entry
label, followed by the entry's two words. -/
theorem RL.poolEntry {R : RL} (hR : R.Wf) {j : Nat} {sz : ScalarSize} {rd : Reg} {v : Nat}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins (.fpuLoadLit sz rd (.const v)) t)) :
    ∃ jl, R.L[jl]? = some (.label (.const v)) ∧ R.L[jl + 1]? = some (.data (v % 2 ^ 32)) ∧
      R.L[jl + 2]? = some (.data (v / 2 ^ 32 % 2 ^ 32)) := by
  obtain ⟨pre, -, hl, -, -⟩ := emitFunc_unfold hR.emit
  generalize hB : relaxLines (relaxOf pre.toList) pre.toList = B at hl
  have hL : R.L = B ++ poolLines (poolUses B) (B.foldl (· + ·.size) 0) := by
    simp only [RL.L, hl, List.toList_toArray]
  rw [hL] at hj ⊢
  -- the load is a line of the body (the pool has no instruction line)
  have hjB : j < B.length := by
    refine Nat.lt_of_not_le fun hn => ?_
    rw [List.getElem?_append_right hn] at hj
    rcases poolLines_mem (List.mem_of_getElem? hj) with ⟨w, h⟩ | ⟨n, -, h⟩ <;> cases h
  rw [List.getElem?_append_left hjB] at hj
  have hv : v ∈ poolUses B := mem_foldl_poolStep_lit (List.mem_of_getElem? hj)
  obtain ⟨i, h1, h2, h3⟩ := poolLines_entry (off := B.foldl (· + ·.size) 0) hv
  refine ⟨B.length + i, ?_, ?_, ?_⟩
  · rw [List.getElem?_append_right (by omega)]; simpa using h1
  · rw [List.getElem?_append_right (by omega)]; simpa [Nat.add_assoc] using h2
  · rw [List.getElem?_append_right (by omega)]; simpa [Nat.add_assoc] using h3

/-! ## Reading the entry -/

theorem read_mem_bytes_succ_toNat (n : Nat) (a : BitVec 64) (s : Arm.ArmState) :
    (Arm.read_mem_bytes (n + 1) a s).toNat =
      (Arm.read_mem a s).toNat + 2 ^ 8 * (Arm.read_mem_bytes n (a + 1#64) s).toNat := by
  simp only [Arm.read_mem_bytes, BitVec.toNat_cast, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Arm.read_mem a s).isLt, Nat.shiftLeft_eq]
  omega

/-- The bytes `[a, a + m + n)` as a number: the first `m` bytes, then the next `n`. -/
theorem read_mem_bytes_add_toNat (s : Arm.ArmState) : ∀ (m n : Nat) (a : BitVec 64),
    (Arm.read_mem_bytes (m + n) a s).toNat =
      (Arm.read_mem_bytes m a s).toNat +
        2 ^ (8 * m) * (Arm.read_mem_bytes n (a + BitVec.ofNat 64 m) s).toNat
  | 0, n, a => by rw [Nat.zero_add]; simp [Arm.read_mem_bytes]
  | m + 1, n, a => by
    rw [show m + 1 + n = (m + n) + 1 by omega, read_mem_bytes_succ_toNat, read_mem_bytes_succ_toNat,
      read_mem_bytes_add_toNat s m n (a + 1#64)]
    have e : a + 1#64 + BitVec.ofNat 64 m = a + BitVec.ofNat 64 (m + 1) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    rw [e, show 8 * (m + 1) = 8 + 8 * m by omega, Nat.pow_add]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- **An 8-byte pool entry** from its two little-endian words. -/
theorem read_mem_bytes_pool8 {s : Arm.ArmState} {A : BitVec 64} {v : Nat}
    (h1 : Arm.read_mem_bytes 4 A s = BitVec.ofNat 32 (v % 2 ^ 32))
    (h2 : Arm.read_mem_bytes 4 (A + BitVec.ofNat 64 4) s = BitVec.ofNat 32 (v / 2 ^ 32 % 2 ^ 32)) :
    Arm.read_mem_bytes 8 A s = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have e := read_mem_bytes_add_toNat s 4 4 A
  rw [h1, h2] at e
  refine e.trans ?_
  simp only [BitVec.toNat_ofNat]
  omega

/-- A `.data` line of the function holds its word in a state holding the code words. -/
theorem RL.read_data {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j d : Nat}
    (hj : R.L[j]? = some (.data d))
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    Arm.read_mem_bytes 4 (R.pcOf j) s = BitVec.ofNat 32 d := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
  simp only [Line.encodeAt, pure, Except.pure, Except.ok.injEq] at hw
  subst hw
  have := hcode _ _ hk
  rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this

/-- The pc of the line after a label line. -/
theorem RL.pcOf_succ_label {R : RL} {j : Nat} {l : Lbl} (hj : R.L[j]? = some (.label l)) :
    R.pcOf (j + 1) = R.pcOf j := by
  simp only [RL.pcOf]
  rw [lineOffset_succ _ _ _ hj]
  rfl

/-- The pc of the line after a `.data` line. -/
theorem RL.pcOf_succ_data {R : RL} {j d : Nat} (hj : R.L[j]? = some (.data d)) :
    R.pcOf (j + 1) = R.pcOf j + 4#64 := by
  simp only [RL.pcOf]
  rw [lineOffset_succ _ _ _ hj, BitVec.add_assoc]
  congr 1
  simp [Line.size, BitVec.ofNat_add]

/-- **The decoded literal load** at its line (`R.envOf j`): an `ldr (literal)` of a SIMD&FP
register whose address, from the line's pc, is the entry's label, which the entry's two words
follow. -/
theorem RL.poolInst {R : RL} (hR : R.Wf) {j : Nat} {sz : ScalarSize} {rd : Reg} {v : Nat}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins (.fpuLoadLit sz rd (.const v)) t))
    {a : Arm.ArmInst} (ha : (Insn.fpuLoadLit sz rd (.const v)).toArmInst (R.envOf j) = .ok a) :
    ∃ jl x, R.L[jl]? = some (.label (.const v)) ∧ R.L[jl + 1]? = some (.data (v % 2 ^ 32)) ∧
      R.L[jl + 2]? = some (.data (v / 2 ^ 32 % 2 ^ 32)) ∧
      a = .LDST (.Reg_literal x) ∧ x.V = 1#1 ∧ Insn.armFields.fpOpc sz = .ok x.opc ∧
      rd.encV = .ok x.Rt ∧
      ∀ u : Arm.ArmState, Arm.r .PC u = R.pcOf j → Arm.LDST.literal_address x.imm19 u = R.pcOf jl := by
  obtain ⟨jl, h0, h1, h2⟩ := RL.poolEntry hR hj
  obtain ⟨o, hlo, hoff, -⟩ := Insn.toArmInst_pcRel ha (t := .const v) (reach := 2 ^ 20) (align := 4) rfl
  rw [Env.target_of_ne (by simp)] at hlo
  have hl0 := labelOffsets_label hR.lm h0
  simp only [RL.envOf] at hlo hoff
  rw [hlo] at hl0
  cases hl0
  simp only [Insn.toArmInst, map_eq_ok] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  simp only [Insn.armFields, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
  obtain ⟨opc, hopc, imm, -, Rt, hRt, rfl⟩ := hb
  refine ⟨jl, _, h0, h1, h2, rfl, rfl, hopc, hRt, fun u hu => ?_⟩
  simp only [Arm.ArmInst.norm, Arm.ArmInst.pcRelOffset?, Option.some.injEq] at hoff
  simp only [Arm.LDST.literal_address, Arm.read_pc, hu, signExtend_append_zero, hoff]
  simp only [RL.pcOf, RL.L, BitVec.add_assoc]
  rw [ofNat_add_ofInt_sub]

/-- The entry's bytes at its label: the low 4 bytes are `v`'s low word, the 8 bytes are `v`. -/
theorem RL.poolBytes {R : RL} (hR : R.Wf) {s : Arm.ArmState} {jl v : Nat}
    (h1 : R.L[jl + 1]? = some (.data (v % 2 ^ 32)))
    (h2 : R.L[jl + 2]? = some (.data (v / 2 ^ 32 % 2 ^ 32)))
    (hpc : R.pcOf (jl + 1) = R.pcOf jl)
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    Arm.read_mem_bytes 4 (R.pcOf jl) s = BitVec.ofNat 32 v ∧
      Arm.read_mem_bytes 8 (R.pcOf jl) s = BitVec.ofNat 64 v := by
  have r1 := RL.read_data hR h1 hcode
  have r2 := RL.read_data hR h2 hcode
  rw [hpc] at r1
  rw [show jl + 2 = jl + 1 + 1 from rfl, RL.pcOf_succ_data h1, hpc] at r2
  refine ⟨?_, read_mem_bytes_pool8 r1 (by simpa using r2)⟩
  rw [r1]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_mod_of_dvd]

/-! ## The load's effect and its operand-view obligation -/

/-- **The literal-pool load's effect** (#565): the def register gets the entry's value
(`poolVal`), the pc advances by 4. -/
def poolExec : MInst → Arm.ArmState → Option Arm.ArmState
  | .fpuLoad sz (.v n) (.const v) _, s =>
    some (Arm.w .PC (Arm.r .PC s + 4) (Arm.w (.SFP (rnum n)) (poolVal sz v) s))
  | _, _ => none

/-- A register location that passes `locOk` for class `float` is an allocatable V register. -/
theorem locOk_float {c : CheckCtx} {r : Reg} (h : c.locOk (.reg r) .float = true) :
    ∃ n, r = .v n ∧ n < 32 := by
  simp only [CheckCtx.locOk, Loc.cls?, Bool.and_eq_true] at h
  rcases allocatable_cases h.2 with ⟨n, rfl, _⟩ | ⟨n, rfl, hn⟩
  · simp [Reg.realClass?] at h
  · exact ⟨n, rfl, hn⟩

/-- **`OperandsSound` of the literal-pool load** against `poolExec`, for every state. -/
theorem os_poolLoad {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (hi : i.isPoolLoad = true) : OperandsSound F poolExec (csem F ctx X) i := by
  obtain ⟨sz, d, v, fl, rfl⟩ : ∃ sz d v fl, i = .fpuLoad sz (.vreg d .float) (.const v) fl := by
    unfold MInst.isPoolLoad at hi
    split at hi
    · exact ⟨_, _, _, _, rfl⟩
    · cases hi
  intro c wh ops regs i' s w outs w' hops' hst hasg' hw _hal _herr hsem'
  rw [ops_poolLoad sz d v fl] at hops'
  cases hops'
  obtain ⟨r, rfl, rfl⟩ := assign_poolLoad hasg'
  obtain ⟨-, hloc, -, -⟩ := checkStatic_facts hst
  have hr := hloc (⟨d, .float, .def, .late, .reg⟩, .reg r) (by simp)
  obtain ⟨n0, rfl, hn0⟩ := locOk_float hr.1
  obtain ⟨_, -, -, -, he⟩ := csem_pool_some hsem'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) hw)
  · refine ⟨?_, fun a _ => ?_, ?_⟩
    · simp only [spOf]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    · simp [Arm.ArmState.mem_w_eq_mem]
    · rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
  · intro p hp
    simp only [defRegs] at hp
    have : p = ((⟨d, .float, .def, .late, .reg⟩, .v n0), poolVal sz v) := by
      simpa [Operand.isDef] using hp
    subst this
    simp only [regVal]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]
  · intro r' hr' hnd _
    have hmem : ((⟨d, .float, .def, .late, .reg⟩ : Operand), Reg.v n0) ∈
        (#[(⟨d, .float, .def, .late, .reg⟩ : Operand)].zip #[Reg.v n0]).toList := by simp
    have hne : r' ≠ .v n0 := fun e => hnd _ hmem rfl e.symm
    rw [regVal_w (by cases r' <;> simp [Reg.field]), regVal_w]
    rcases allocatable_cases hr' with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
    · simp [Reg.field]
    · simp only [Reg.field, ne_eq, Option.some.injEq, Arm.StateField.SFP.injEq]
      exact rnum_ne (by omega) hn0 (fun e => hne (by rw [e]))
  · intro r' hr'; simp [MInst.clobbers] at hr'

/-! ## The load on the machine -/

/-- **The `ldr (literal)` on the machine**: at the line of a literal load into `v n` (32 or 64
bits), from a state holding the code words, one step of the machine is `poolExec`. -/
theorem RL.step_poolLoad {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {sz : ScalarSize}
    {n v : Nat} {t : Option Clif.TrapCode}
    (hj : R.L[j]? = some (.ins (.fpuLoadLit sz (.v n) (.const v)) t))
    (hsz : sz = .size32 ∨ sz = .size64)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None)
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    R.step s = Arm.w .PC (Arm.r .PC s + 4) (Arm.w (.SFP (rnum n)) (poolVal sz v) s) := by
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl hprog
    hpc herr
  obtain ⟨jl, x, h0, h1, h2, rfl, hV, hopc, hRt, haddr⟩ := RL.poolInst hR hj ha
  obtain ⟨b4, b8⟩ := RL.poolBytes hR h1 h2 (RL.pcOf_succ_label h0) hcode
  simp only [Reg.encV] at hRt
  split at hRt
  · simp only [pure, Except.pure, Except.ok.injEq] at hRt
    simp only [RL.step, hstep, Arm.exec_inst, Arm.LDST.exec_reg_literal, hV, ite_true,
      haddr s hpc, Arm.write_pc, Arm.read_pc, Arm.write_sfp, ← hRt]
    rcases hsz with rfl | rfl <;>
      simp only [Insn.armFields.fpOpc, pure, Except.pure, Except.ok.injEq] at hopc <;>
      simp only [← hopc, b4, b8, poolVal, rnum] <;> rw [← hRt] <;> rfl
  · simp [throw, throwThe, MonadExceptOf.throw] at hRt

/-- **The literal load reads the entry's `.data` words** (D2): every byte it reads, at its own
line's encoding, is a byte of a `.data` line. -/
theorem RL.pool_reads {R : RL} (hR : R.Wf) {j : Nat} {sz : ScalarSize} {rd : Reg} {v : Nat}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins (.fpuLoadLit sz rd (.const v)) t))
    (hsz : sz = .size32 ∨ sz = .size64) {u : Arm.ArmState} (hpc : Arm.r .PC u = R.pcOf j)
    {a : Arm.ArmInst} (ha : (Insn.fpuLoadLit sz rd (.const v)).toArmInst (R.envOf j) = .ok a) :
    ∀ p ∈ E2E.ExecBytes.MemReads a u, ∀ k < p.2, ∃ j' d, R.L[j']? = some (.data d) ∧
      ∃ i < 4, p.1 + BitVec.ofNat 64 k = R.pcOf j' + BitVec.ofNat 64 i := by
  obtain ⟨jl, x, h0, h1, h2, rfl, hV, hopc, -, haddr⟩ := RL.poolInst hR hj ha
  have e1 := RL.pcOf_succ_label h0
  have e2 := RL.pcOf_succ_data h1
  intro p hp k hk
  simp only [E2E.ExecBytes.MemReads, E2E.ExecFrame.literalReads, hV, ite_true, haddr u hpc] at hp
  have hlo : ∀ k < 4, ∃ j' d, R.L[j']? = some (.data d) ∧
      ∃ i < 4, R.pcOf jl + BitVec.ofNat 64 k = R.pcOf j' + BitVec.ofNat 64 i :=
    fun k hk => ⟨jl + 1, _, h1, k, hk, by rw [e1]⟩
  rcases hsz with rfl | rfl <;>
    simp only [Insn.armFields.fpOpc, pure, Except.pure, Except.ok.injEq] at hopc <;>
    simp only [← hopc] at hp
  · change p ∈ [(R.pcOf jl, 4)] at hp
    rw [List.mem_singleton] at hp; subst hp
    exact hlo k hk
  · change p ∈ [(R.pcOf jl, 8)] at hp
    rw [List.mem_singleton] at hp; subst hp
    by_cases h4 : k < 4
    · exact hlo k h4
    · refine ⟨jl + 2, _, h2, k - 4, by simp at hk; omega, ?_⟩
      rw [show jl + 2 = jl + 1 + 1 from rfl, e2, e1, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega

/-- **The literal load's line on the machine**, as the `RunsAs` variants use it: the machine's
step is `poolExec`'s, to the next line, and the state before it satisfies `GoodX` and the
located reads (every guard set). -/
theorem RL.pool_run {R : RL} (hR : R.Wf) {sz : ScalarSize} {n v : Nat} {fl : Clif.MemFlags}
    (hsz : sz = .size32 ∨ sz = .size64) {j : Nat} {T : List Line} {s : Arm.ArmState}
    {m : Loc → CV} {w s' : Arm.ArmState}
    (hd : R.L.drop j = [.ins (.fpuLoadLit sz (.v n) (.const v))] ++ T) (hst : StRel R s m w)
    (hpc : Arm.r .PC s = R.pcOf j)
    (hex : poolExec (.fpuLoad sz (.v n) (.const v) fl) s = some s') :
    R.L[j]? = some (.ins (.fpuLoadLit sz (.v n) (.const v))) ∧ R.step s = s' ∧
      Arm.r .PC s' = R.pcOf (j + 1) ∧ R.GoodX s ∧ ∀ Y, R.ReadsInY Y s := by
  have hj : R.L[j]? = some (.ins (.fpuLoadLit sz (.v n) (.const v))) := drop_get (Z := []) hd
  simp only [poolExec, Option.some.injEq] at hex
  subst hex
  have hstep := RL.step_poolLoad hR hj hsz hst.prog hpc hst.err hst.code
  have hpc' : Arm.r .PC (Arm.w .PC (Arm.r .PC s + 4) (Arm.w (.SFP (rnum n)) (poolVal sz v) s)) =
      Arm.r .PC s + 4 := Arm.r_of_w_same
  refine ⟨hj, hstep, by rw [hpc', hpc, pcOf_succ hj], ?_, fun Y => ?_⟩
  · exact RL.goodX_ofIns hR hj hpc rfl rfl (RL.good_of_sp hst.sp) hst.err hst.prog
      (RL.nextOk_pc4 (by rw [hstep, hpc'])) (RL.readsAt_of_lineE hR hj hpc fun _ a ha p hp k hk => by
        obtain ⟨j', d, hd', i, hi, he⟩ := RL.pool_reads hR hj hsz hpc ha p hp k hk
        exact he ▸ .inr (.inr ⟨j', d, hd', i, hi, rfl⟩))
  · exact RL.readsIn_of_lineE hR hj hpc fun _ a ha p hp k hk => by
      obtain ⟨j', d, hd', i, hi, he⟩ := RL.pool_reads hR hj hsz hpc ha p hp k hk
      exact he ▸ .inr (.inr (.inr ⟨j', d, hd', i, hi, rfl⟩))

/-- The world after the literal-pool load: no error, the program kept. -/
theorem pool_errW {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (hst : StRel R s m w) {sz : ScalarSize} {d v : Nat} {fl : Clif.MemFlags} {us outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl}
    (hsem : R.sem (.fpuLoad sz (.vreg d .float) (.const v) fl) us w = some (outs, w', ctl)) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  obtain ⟨_, -, -, -, he⟩ := csem_pool_some (R.sem_csem hsem)
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  exact ⟨by rw [← hst.world.1 .ERR (by simp [Masked]), hst.err], rfl⟩

/-- The allocated literal-pool load's lines, when `poolExec` runs it. -/
theorem pool_lines {R : RL} {sz : ScalarSize} {d v : Nat} {fl : Clif.MemFlags} {regs : Array Reg}
    {i' : MInst} (hasg : (MInst.fpuLoad sz (.vreg d .float) (.const v) fl).assign regs = .ok i')
    (hex : ∃ (s s' : Arm.ArmState), poolExec i' s = some s') :
    ∃ n, i' = .fpuLoad sz (.v n) (.const v) fl ∧
      (∀ ps, i'.lines R.ctx ps = .ok ([.ins (.fpuLoadLit sz (.v n) (.const v))], ps)) ∧
      (∀ ln ∈ [Line.ins (.fpuLoadLit sz (.v n) (.const v))], ln.plain = true) := by
  obtain ⟨r, rfl, rfl⟩ := assign_poolLoad hasg
  obtain ⟨s, s', hex⟩ := hex
  obtain ⟨n, rfl⟩ : ∃ n, r = .v n := by
    cases r <;> simp [poolExec] at hex
    exact ⟨_, rfl⟩
  exact ⟨n, rfl, fun ps => by simp [MInst.lines, pure, Except.pure],
    fun ln hln => by simp at hln; subst hln; simp [Line.plain, Insn.condTarget?]⟩

/-- `R.sem` of the literal-pool load keeps the world. -/
theorem pool_world {R : RL} {sz : ScalarSize} {d v : Nat} {fl : Clif.MemFlags} {us outs : List CV}
    {w w' : Arm.ArmState} {ctl : Ctl}
    (hsem : R.sem (.fpuLoad sz (.vreg d .float) (.const v) fl) us w = some (outs, w', ctl)) :
    w' = w ∧ ctl = .next := by
  obtain ⟨_, -, -, -, he⟩ := csem_pool_some (R.sem_csem hsem)
  simp only [Prod.mk.injEq] at he
  exact ⟨he.2.1, he.2.2⟩

/-- **The literal-pool load on the machine** (`MStep.op` with control `next`): one step, the
`ldr (literal)` reading the entry from the function's code. -/
theorem realizes_poolLoad {R : RL} (hR : R.Wf) {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hform : i.isPoolLoad = true)
    (hops : i.operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
  obtain ⟨sz, d, v, fl, rfl, hsz32⟩ := isPoolLoad_form hform
  refine realizes_op_coreX hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => poolExec)
    (fun _ => (((os_poolLoad hform).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun _ => True)
    trivial (fun regs i' hasg _ hex _ => ?_) (pool_errW (q_stRel hq) hsem)
  obtain ⟨_, s0, s1, hex⟩ := hex
  obtain ⟨n, rfl, hl, hpl⟩ := pool_lines (R := R) hasg ⟨s0, s1, hex⟩
  refine ⟨_, hl, hpl, fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h,
    fun j T s m w s' hd hst hpc _ hex => ?_⟩
  obtain ⟨-, hs, hpc', hg, -⟩ := RL.pool_run hR hsz32 hd hst hpc hex
  refine ⟨1, by simpa [iterN] using hs, hpc', fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  exact hg

end Backend.Proof

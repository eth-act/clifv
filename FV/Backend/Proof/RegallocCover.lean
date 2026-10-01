import FV.E2E.RegLevelOp
import FV.Backend.Proof.RegallocAtomic
import FV.Backend.Proof.RegallocMemAddr

/-!
# Form coverage (M6 interface between the instruction proofs and the control proofs)

`FormOk ctx i`: a decidable test that the straight-line instruction `i` (vreg operands, as
the lowering emits it) is one of the forms whose `OperandsSound` and `LinesOk` are proven.
`FormsCovered ctx vc`: every instruction of `vc` is a control form (`MInst.isCtl`, handled by
the control proofs) or `FormOk`. It is decided per function (a premise `lean-e2e-check`
checks), not required of the compiler: out-of-scope forms keep compiling.

`formOk_sound`: `FormOk` gives exactly the `OperandsSound`/`LinesOk` premises of
`realizes_op_next`.
-/

namespace Backend.Proof

open Backend E2E

/-- Every instruction of `vc` is a control form or a covered form. -/
def FormsCovered (ctx : FnCtx) (vc : VCode) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vc.blocks[b]? = some vb → vb.insts[k]? = some i →
    i.isCtl = true ∨ FormOk ctx i = true

/-- The executable test. -/
def formsCoveredB (ctx : FnCtx) (vc : VCode) : Bool :=
  vc.blocks.all fun vb => vb.insts.all fun i => i.isCtl || FormOk ctx i

theorem array_all_iff {α : Type} (a : Array α) (p : α → Bool) :
    a.all p = true ↔ ∀ (k : Nat) (x : α), a[k]? = some x → p x = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h k x hk
    obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.1 hk
    exact h k hk'
  · intro h k hk
    exact h k _ (Array.getElem?_eq_getElem hk)

theorem formsCoveredB_iff (ctx : FnCtx) (vc : VCode) :
    formsCoveredB ctx vc = true ↔ FormsCovered ctx vc := by
  unfold formsCoveredB FormsCovered
  rw [array_all_iff]
  constructor
  · intro h b vb k i hb hi
    have := (array_all_iff _ _).1 (h b vb hb) k i hi
    simpa [Bool.or_eq_true] using this
  · intro h b vb hb
    rw [array_all_iff]
    intro k i hi
    simpa [Bool.or_eq_true] using h b vb k i hb hi

instance (ctx : FnCtx) (vc : VCode) : Decidable (FormsCovered ctx vc) :=
  decidable_of_iff _ (formsCoveredB_iff ctx vc)

/-! ## Soundness -/

/-- Invert `MInst.assign` of a form with at most four vreg operands. -/
syntax "assign_inv" ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| assign_inv $h) => `(tactic| (
    rcases regs with ⟨_|⟨_,_|⟨_,_|⟨_,_|⟨_,_|⟨_,_⟩⟩⟩⟩⟩⟩ <;>
    simp [MInst.assign, MInst.visitOperands, AMode.visit, StateT.run, bind, StateT.bind,
      Except.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure,
      Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift] at $h:ident <;>
    subst $h:ident))

/-- A single-line expansion. -/
syntax "one_line" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| one_line) => `(tactic| first
    | exact linesOk_of_oneLine ⟨_, _, fun _ => rfl, rfl, rfl⟩
    | (refine linesOk_of_oneLine ⟨_, _, fun _ => rfl, ?_, ?_⟩ <;> split <;> rfl))

theorem linesOk_extend (ctx : FnCtx) (rd rn : Reg) (sg : Bool) (a b : Nat) :
    LinesOk ctx (.extend rd rn sg a b) := by
  apply linesOk_of_oneLine
  by_cases h1 : (!sg && a == 1) = true
  · exact ⟨_, _, fun ps => by simp only [MInst.lines, h1, if_true]; rfl, rfl, rfl⟩
  by_cases h2 : (!sg && a == 32 && b == 64) = true
  · exact ⟨_, _, fun ps => by simp only [MInst.lines, h1, h2, if_true]; rfl, rfl, rfl⟩
  cases sg
  · exact ⟨_, _, fun ps => by simp only [MInst.lines, h1, h2]; rfl, rfl, rfl⟩
  · exact ⟨_, _, fun ps => by simp only [MInst.lines, h1, h2]; rfl, rfl, rfl⟩

theorem linesOk_logic (ctx : FnCtx) {op : ALUOp} (h : logicOpOk op = true) (sz : OperandSize)
    (rd rn : Reg) (imm : ImmLogic) : LinesOk ctx (.aluRRImmLogic op sz rd rn imm) := by
  cases op <;> simp [logicOpOk] at h <;> one_line

theorem linesOk_shift (ctx : FnCtx) {op : ALUOp} (h : shiftOpOk op = true) (sz : OperandSize)
    (rd rn : Reg) (imm : Nat) : LinesOk ctx (.aluRRImmShift op sz rd rn imm) := by
  cases op <;> simp [shiftOpOk] at h <;> one_line

theorem linesOk_rrrShift (ctx : FnCtx) (op : ALUOp) (sz : OperandSize) (rd rn rm : Reg)
    (sh : ShiftOpAndAmt) : LinesOk ctx (.aluRRRShift op sz rd rn rm sh) := by
  cases op <;> one_line

theorem linesOk_vecMisc (ctx : FnCtx) (op : VecMisc2) (rd rn : Reg) (sz : VectorSize) :
    LinesOk ctx (.vecMisc op rd rn sz) := by
  cases op; one_line

theorem linesOk_vecRRR (ctx : FnCtx) (op : VecALUOp) (rd rn rm : Reg) (sz : VectorSize) :
    LinesOk ctx (.vecRRR op rd rn rm sz) := by
  cases op; one_line

theorem interOk_prefix {env : Env} {pre tail : List Line} {s S : Arm.ArmState}
    (h : StepsOk env pre s S) (he : Arm.r .ERR s = .None) (ht : tail.length ≤ 1) :
    InterOk env (pre ++ tail) s := by
  intro k _ hk s1 hs1
  simp only [List.length_append] at hk
  rw [List.take_append_of_le_length (by omega)] at hs1
  obtain ⟨s2, h2⟩ := StepsOk.take k h
  rw [h2.exec] at hs1
  cases hs1
  exact ⟨h2.err.1.trans he, h2.err.2⟩

theorem mem_loadConst64 {r : Reg} {v : Nat} {ln : Line} (h : ln ∈ loadConst64 r v) :
    ∃ x, ln = .ins x none ∧ x.hooked = false ∧ (Line.ins x none).plain = true := by
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with rfl | ⟨j, _, hj⟩
  · exact ⟨_, rfl, rfl, rfl⟩
  · split at hj
    · cases hj; exact ⟨_, rfl, rfl, rfl⟩
    · cases hj

theorem memFinalize_shape {c : FnCtx} {m m' : AMode} {b : Nat} {pre : List Line}
    (h : memFinalize c m b = .ok (pre, m')) : pre = [] ∨ ∃ v, pre = loadConst64 (.x 16) v := by
  cases m <;> simp only [memFinalize, pure, Except.pure, Except.ok.injEq] at h
  all_goals first | cases h | skip
  all_goals first
    | (left; rfl)
    | ((repeat' split at h) <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
        first | (left; rfl) | exact Or.inr ⟨_, rfl⟩)

theorem memFinalize_ok (c : FnCtx) {m : AMode} (hm : ∀ o, m ≠ .incomingArg o) (b : Nat) :
    ∃ pre m', memFinalize c m b = .ok (pre, m') := by
  cases m <;> first | exact absurd rfl (hm _) | exact ⟨_, _, rfl⟩

theorem linesOk_mem (ctx : FnCtx) (i : MInst) (b : Nat) (m : AMode) (mk : AMode → Insn)
    (t : Option Clif.TrapCode) (hm : ∀ o, m ≠ .incomingArg o) (hx : ∀ m', (mk m').hooked = false)
    (hp : ∀ m', (Line.ins (mk m') t).plain = true)
    (hl : ∀ ps pre m', memFinalize ctx m b = .ok (pre, m') →
      i.lines ctx ps = .ok (pre ++ [.ins (mk m') t], ps)) : LinesOk ctx i := by
  obtain ⟨pre, m', hf⟩ := memFinalize_ok ctx hm b
  have hpl := hp m'
  refine ⟨pre ++ [.ins (mk m') t], fun ps => hl ps pre m' hf, fun ln hln => ?_, fun ln hln => ?_,
    fun env s s' he _ => ?_⟩
  · rcases List.mem_append.1 hln with h | h
    · rcases memFinalize_shape hf with rfl | ⟨v, rfl⟩
      · cases h
      · obtain ⟨x, rfl, hx', -⟩ := mem_loadConst64 h; exact ⟨x, none, rfl, hx'⟩
    · simp at h; exact ⟨_, _, h, hx m'⟩
  · rcases List.mem_append.1 hln with h | h
    · rcases memFinalize_shape hf with rfl | ⟨v, rfl⟩
      · cases h
      · obtain ⟨x, rfl, -, hp⟩ := mem_loadConst64 h; exact hp
    · simp at h; rw [h]; exact hpl
  · rcases memFinalize_shape hf with rfl | ⟨v, rfl⟩
    · exact interOk_prefix (S := s) (by simp [StepsOk]) he (by simp)
    · exact interOk_prefix (steps_loadConst64 env (by omega) v s) he (by simp)

theorem plain_trap (x : Insn) (hx : x.condTarget? = none) (hb : ∀ l, x ≠ .b l) (t : Option Clif.TrapCode) :
    (Line.ins x t).plain = true := by
  cases t <;> cases x <;> simp_all [Line.plain]

theorem linesOk_gen (ctx : FnCtx) (i : MInst) (pre tail : List Line)
    (hl : ∀ ps, i.lines ctx ps = .ok (pre ++ tail, ps))
    (hpre : pre = [] ∨ ∃ v, pre = loadConst64 (.x 16) v) (ht1 : tail.length ≤ 1)
    (ht : ∀ ln ∈ tail, ∃ x t, ln = .ins x t ∧ x.hooked = false ∧ (Line.ins x t).plain = true) :
    LinesOk ctx i := by
  refine ⟨pre ++ tail, hl, fun ln hln => ?_, fun ln hln => ?_, fun env s s' he _ => ?_⟩
  · rcases List.mem_append.1 hln with h | h
    · rcases hpre with rfl | ⟨v, rfl⟩
      · cases h
      · obtain ⟨x, rfl, hx', -⟩ := mem_loadConst64 h; exact ⟨x, none, rfl, hx'⟩
    · obtain ⟨x, t, rfl, hx, -⟩ := ht _ h; exact ⟨x, t, rfl, hx⟩
  · rcases List.mem_append.1 hln with h | h
    · rcases hpre with rfl | ⟨v, rfl⟩
      · cases h
      · obtain ⟨x, rfl, -, hp⟩ := mem_loadConst64 h; exact hp
    · obtain ⟨x, t, rfl, -, hp⟩ := ht _ h; exact hp
  · rcases hpre with rfl | ⟨v, rfl⟩
    · exact interOk_prefix (S := s) (by simp [StepsOk]) he ht1
    · exact interOk_prefix (steps_loadConst64 env (by omega) v s) he ht1

theorem addOff_ok (rd rn : Reg) (k : Int) : (MInst.lines.addOff rd rn k).length ≤ 1 ∧
    ∀ ln ∈ MInst.lines.addOff rd rn k, ∃ x t, ln = .ins x t ∧ x.hooked = false ∧
      (Line.ins x t).plain = true := by
  unfold MInst.lines.addOff
  split
  · split
    · simp
    · simp; exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  · split <;> (simp; exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩)

theorem linesOk_loadAddr_slot (ctx : FnCtx) (rd : Reg) (off : Int) :
    LinesOk ctx (.loadAddr rd (.slotOffset off)) := by
  cases h9 : simm9? (off + ctx.slotBase) with
  | some k =>
    exact linesOk_gen ctx _ [] _ (fun ps => by simp [MInst.lines, memFinalize, h9]) (Or.inl rfl)
      (addOff_ok rd .sp k).1 (addOff_ok rd .sp k).2
  | none =>
    cases hu : uimm12Scaled? (off + ctx.slotBase) 1 with
    | some o =>
      exact linesOk_gen ctx _ [] _ (fun ps => by simp [MInst.lines, memFinalize, h9, hu]) (Or.inl rfl)
        (addOff_ok rd .sp o).1 (addOff_ok rd .sp o).2
    | none =>
      exact linesOk_gen ctx _ _ [.ins (.aluRRRExtend .add true rd .sp (.x 16) .sxtx)]
        (fun ps => by simp [MInst.lines, memFinalize, h9, hu]; rfl) (Or.inr ⟨_, rfl⟩) (by simp)
        (by simp; exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩)

theorem linesOk_load (ctx : FnCtx) (op : LoadOp) (rd : Reg) (m : AMode) (fl : Clif.MemFlags)
    (hm : ∀ o, m ≠ .incomingArg o) : LinesOk ctx (.load op rd m fl) :=
  linesOk_mem ctx _ op.bytes m (fun m' => .load op rd m') fl.trapCode hm (fun _ => rfl)
    (fun _ => plain_trap _ rfl (fun _ h => Insn.noConfusion h) _)
    (fun ps pre m' hf => by simp [MInst.lines, hf])

theorem linesOk_store (ctx : FnCtx) (op : StoreOp) (rd : Reg) (m : AMode) (fl : Clif.MemFlags)
    (hm : ∀ o, m ≠ .incomingArg o) : LinesOk ctx (.store op rd m fl) :=
  linesOk_mem ctx _ op.bytes m (fun m' => .store op rd m') fl.trapCode hm (fun _ => rfl)
    (fun _ => plain_trap _ rfl (fun _ h => Insn.noConfusion h) _)
    (fun ps pre m' hf => by simp [MInst.lines, hf])

/-- The load/store part of `formOk_sound`. -/
syntax "mem_os" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mem_os) => `(tactic| (
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hop, hm⟩ := h
    unfold memOk at hm
    split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
      refine ⟨fun env => ?_, fun regs i' hasg => ?_⟩
    all_goals first
      | (first
          | exact os_load_slot _ _ _ _ _ hop _ _ _
          | exact os_load_sp _ _ _ _ _ hop _ _ _
          | exact os_load_fp _ _ _ _ _ hop _ _ _
          | exact os_load_unscaled _ _ _ _ _ hop _ _ _ hm.1 hm.2 _
          | exact os_load_uoff _ _ _ _ _ hop _ _ _ hm.1 hm.2 _
          | exact os_load_regReg _ _ _ _ _ hop _ _ _ _
          | exact os_load_regScaled _ _ _ _ _ hop _ _ _ _
          | exact os_load_regScaledExtended _ _ _ _ _ hop _ _ _ _ hm _
          | exact os_load_regExtended _ _ _ _ _ hop _ _ _ _ hm _
          | exact os_store_slot _ _ _ _ _ hop _ _ _
          | exact os_store_sp _ _ _ _ _ hop _ _ _
          | exact os_store_fp _ _ _ _ _ hop _ _ _
          | exact os_store_unscaled _ _ _ _ _ hop _ _ _ hm.1 hm.2 _
          | exact os_store_uoff _ _ _ _ _ hop _ _ _ hm.1 hm.2 _
          | exact os_store_regReg _ _ _ _ _ hop _ _ _ _
          | exact os_store_regScaled _ _ _ _ _ hop _ _ _ _
          | exact os_store_regScaledExtended _ _ _ _ _ hop _ _ _ _ hm _
          | exact os_store_regExtended _ _ _ _ _ hop _ _ _ _ hm _)
      | (assign_inv hasg
         all_goals refine ⟨?_, fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h⟩
         all_goals first
           | exact linesOk_load _ _ _ _ _ (fun _ h => AMode.noConfusion h)
           | exact linesOk_store _ _ _ _ _ (fun _ h => AMode.noConfusion h))))

set_option maxHeartbeats 4000000 in
theorem formOk_load {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {op : LoadOp} {d : Nat}
    {m : AMode} {fl : Clif.MemFlags} (h : (op != .fpuLoad128 && memOk op.bytes m) = true) :
    (∀ env, OperandsSound F (execMInst ctx env) (csem F ctx X) (.load op (.vreg d .int) m fl)) ∧
    (∀ regs i', (MInst.load op (.vreg d .int) m fl).assign regs = .ok i' →
      LinesOk ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) := by
  mem_os

set_option maxHeartbeats 4000000 in
theorem formOk_store {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {op : StoreOp} {d : Nat}
    {m : AMode} {fl : Clif.MemFlags} (h : (op != .fpuStore128 && memOk op.bytes m) = true) :
    (∀ env, OperandsSound F (execMInst ctx env) (csem F ctx X) (.store op (.vreg d .int) m fl)) ∧
    (∀ regs i', (MInst.store op (.vreg d .int) m fl).assign regs = .ok i' →
      LinesOk ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) := by
  mem_os

theorem logicOpOk_of_and {op : ALUOp} {b : Bool} (h : (logicOpOk op && b) = true) :
    logicOpOk op = true := by
  simp only [Bool.and_eq_true] at h; exact h.1

theorem logicOpOk_of_andS {op : ALUOp} {b : Bool} (h : ((op == .andS) && b) = true) :
    logicOpOk op = true := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1]; rfl

set_option maxHeartbeats 4000000 in
theorem formOk_sound {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (h : FormOk ctx i = true) :
    (∀ env, OperandsSound F (execMInst ctx env) (csem F ctx X) i) ∧
    (∀ regs i', i.assign regs = .ok i' →
      LinesOk ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) := by
  unfold FormOk at h
  split at h
  rotate_left 32
  · exact formOk_load h
  · exact formOk_store h
  rotate_left
  all_goals (try cases h) <;> refine ⟨fun env => ?_, fun regs i' hasg => ?_⟩
  all_goals first
    | exact os_loadAcquire _ _ _ _ _ (of_decide_eq_true h) _ _ _
    | exact os_storeRelease _ _ _ _ _ (of_decide_eq_true h) _ _ _
    | (first
        | apply os_csetm | apply os_fence | apply os_aluRRR | apply os_aluRRR_rnZ | apply os_aluRRR_rdZ | apply os_aluRRR_rmZ
        | apply os_aluRRR_rdZ_rmZ | apply os_aluRRRR | apply os_aluRRRR_raZ
        | apply os_aluRRImm12 | apply os_aluRRImm12_rdZ | apply os_aluRRImmLogic
        | apply os_aluRRImmLogic_rdZ | apply os_aluRRImmLogic_rnZ | apply os_aluRRImmShift
        | apply os_aluRRRShift
        | apply os_aluRRRShift_rdZ | apply os_aluRRRShift_rnZ | apply os_aluRRRExtend
        | apply os_aluRRRExtend_rdZ | apply os_bitRR | apply os_mov | apply os_movWide
        | apply os_movK | apply os_extend | apply os_bitfieldMove | apply os_cset | apply os_csel
        | apply os_ccmp | apply os_ccmpImm | apply os_movToFpu | apply os_movFromVec
        | apply os_vecMisc | apply os_vecLanes | apply os_vecRRR | apply os_loadAddr_slot) <;>
        assumption
    | (assign_inv hasg
       all_goals refine ⟨?_, fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h⟩
       all_goals first
         | one_line
         | exact linesOk_extend ..
         | exact linesOk_logic _ (logicOpOk_of_and ‹_›) ..
         | exact linesOk_logic _ (logicOpOk_of_andS ‹_›) ..
         | exact linesOk_shift _ ‹_› ..
         | exact linesOk_rrrShift ..
         | exact linesOk_vecMisc ..
         | exact linesOk_vecRRR ..
         | exact linesOk_loadAddr_slot ..
         | exact linesOk_of_oneLine ⟨_, _, fun _ => rfl, rfl,
             plain_trap _ rfl (fun _ h => Insn.noConfusion h) _⟩)

end Backend.Proof

import Lean
import FV.E2E.EmitPreOk
import FV.E2E.EmitCondsDefs
import FV.Backend.Proof.RelaxLayout
import FV.Backend.EmitOk

/-!
# Every instruction of the emitted spill allocation is encodable (V6b)

`emitFunc_spill_encodable`: for in-scope input, every instruction line of
`emitFunc k af` (`af` the lowered spill allocation of the prepared VCode `vcp`) passes
`Insn.encodable` (its non-label operands encode; `FV/Backend/Proof/RelaxLayout.lean`), given the
decided premise `immsOkB vcp` (the immediates instruction selection chose are in the encoder's
ranges: `immOkB`). The general form is `emitFunc_encodable_of`: any allocation with verified
in-states (`AllocChecked`) of a covered VCode (`FormsCovered`).

* Registers: the checker's static checks (`allocChecked_items`, `ItemChk`) give every operand
  register its class (`AllocOk`, `RegFits`: `x0`–`x28` or `v0`–`v31`) and every move's register
  side its class (`checkMove_facts`); `FormOk` puts `xzr` only where the encoding reads it as the
  zero register, `ctlInstOk` makes the tested/defined registers of the control forms int vregs.
* Per form: `formOk_enc` (the straight-line forms, by inverting `MInst.assign`), `ctl_enc` (the
  control forms), `moveInsts_enc` (moves: `slotStoreAt`/`slotLoadAt`/`mov`), `aEnc_prologue`,
  `aEnc_epilogue`; memory operands through `memFinalize_enc`.
* Emission: `blocksLinesE_enc`, then `fallthrough` (`ftList_enc`) and relaxation
  (`relaxLines_enc`) only drop lines, invert conditional branches (`encodable_invertTo`) and add
  `b` (`b_encodable`); the trap lines are `udf` (`trapLines_enc`).
-/

namespace E2E

open Backend Backend.Proof

open Lean Meta in
/-- Destructure every conjunction and existential hypothesis. -/
partial def destrGoal (g : MVarId) : MetaM MVarId := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``And 2 || t.isAppOfArity ``Exists 2 then
      let gs ← g.cases d.fvarId
      if h : gs.size = 1 then return ← destrGoal gs[0].mvarId
  return g

open Lean Elab Tactic in
/-- Destructure every conjunction and existential hypothesis. -/
elab "destr" : tactic => liftMetaTactic fun g => do return [← destrGoal g]

open Lean Meta in
/-- Destructure every conjunction, existential and disjunction hypothesis (several goals). -/
partial def destrAllGoal (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``And 2 || t.isAppOfArity ``Exists 2 || t.isAppOfArity ``Or 2 then
      let gs ← g.cases d.fvarId
      return (← gs.toList.mapM (fun s => destrAllGoal s.mvarId)).flatten
  return [g]

open Lean Elab Tactic in
/-- Destructure every conjunction, existential and disjunction hypothesis. -/
elab "destr_all" : tactic => liftMetaTactic destrAllGoal

open Lean Meta in
/-- Case on every local of one of the types `names`. -/
partial def casesTypes (names : List Name) (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let .const n _ := t then
      if names.contains n then
        let gs ← g.cases d.fvarId
        return (← gs.toList.mapM (fun s => casesTypes names s.mvarId)).flatten
  return [g]

open Lean Elab Tactic in
/-- Case on every `ALUOp` local. -/
elab "cases_op" : tactic => liftMetaTactic (casesTypes [``Backend.ALUOp, ``Backend.OperandSize])

/-! ## Encodability -/

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  if_pos h

theorem encZR_x {n : Nat} (h : n ≤ 30) : (Reg.x n).encZR = .ok (BitVec.ofNat 5 n) := by
  simp [Reg.encZR, h]
theorem encSP_x {n : Nat} (h : n ≤ 30) : (Reg.x n).encSP = .ok (BitVec.ofNat 5 n) := by
  simp [Reg.encSP, h]
theorem encV_v {n : Nat} (h : n ≤ 31) : (Reg.v n).encV = .ok (BitVec.ofNat 5 n) := by
  simp [Reg.encV, h]
theorem encZR_xzr : Reg.xzr.encZR = .ok 31#5 := rfl
theorem encSP_sp : Reg.sp.encSP = .ok 31#5 := rfl

abbrev env0 : Env := ⟨0, fun _ => some 0⟩

theorem encodable_iff {i : Insn} : i.encodable = true ↔ ∃ a, i.armFields env0 = .ok a := by
  unfold Insn.encodable Insn.encode Insn.toArmInst
  cases i.armFields ⟨0, fun _ => some 0⟩ <;> simp [Functor.map, Except.map]

/-- Every instruction line of the expansion of `m` is encodable. -/
def LinesEnc (c : FnCtx) (m : MInst) : Prop :=
  ∀ ps ls ps', m.lines c ps = .ok (ls, ps') → ∀ i t, Line.ins i t ∈ ls → i.encodable = true

theorem linesEnc_one {c : FnCtx} {m : MInst} {x : Insn} {t : Option Clif.TrapCode}
    (h : ∀ ps, m.lines c ps = .ok ([.ins x t], ps)) (hx : x.encodable = true) : LinesEnc c m := by
  intro ps ls ps' hl i t' hm
  rw [h] at hl
  cases hl
  simp only [List.mem_singleton, Line.ins.injEq] at hm
  rw [hm.1]; exact hx

set_option hygiene false in
/-- Decide the encoding of a concrete instruction (registers `.x n` with `n` bounded). -/
macro "enc" : tactic => `(tactic| (
  rw [encodable_iff]
  simp (disch := omega) [Insn.armFields, encZR_x, encSP_x, encV_v, encZR_xzr, encSP_sp, ite_pos', uField, sField,
    bind, Except.bind, pure, Except.pure, ALUOp.addSub?, ALUOp.logic?, OperandSize.is64,
    Env.pcRel, Env.rel, Env.target, VectorSize.qsize, Reg.fp, Reg.lr, Insn.armFields.exclFields,
    throw, throwThe, MonadExceptOf.throw, CTy.bits, LoadOp.fields, StoreOp.fields,
    ldstFields, LoadOp.bytes, StoreOp.bytes, Nat.mod_lt] <;>
  (try simp_all [ALUOp.addSub?, ALUOp.logic?, OperandSize.is64, CTy.bits, immOkB]) <;>
  (repeat' split) <;>
  (try simp_all [ALUOp.addSub?, ALUOp.logic?, OperandSize.is64, CTy.bits, immOkB]) <;> (try omega)))

/-! ## Multi-line expansions -/

/-- A general-purpose register `x0`–`x30`. -/
def GR (r : Reg) : Prop := ∃ n, r = .x n ∧ n ≤ 30

/-- A general-purpose register or `sp`. -/
def SR (r : Reg) : Prop := GR r ∨ r = .sp

/-- A SIMD&FP register. -/
def VR (r : Reg) : Prop := ∃ n, r = .v n ∧ n ≤ 31

theorem gr_x {n : Nat} (h : n ≤ 30) : GR (.x n) := ⟨n, rfl, h⟩

theorem loadConst64_enc {n : Nat} (hn : n ≤ 30) (v : Nat) :
    ∀ i t, Line.ins i t ∈ loadConst64 (.x n) v → i.encodable = true := by
  intro i t h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at h
  rcases h with h | ⟨j, hj, hj'⟩
  · simp only [Line.ins.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have : mask64 v / 2 ^ (16 * 0) % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
    enc
  · split at hj'
    · simp only [Option.some.injEq, Line.ins.injEq] at hj'
      obtain ⟨rfl, -⟩ := hj'
      have : mask64 v / 2 ^ (16 * (j + 1)) % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
      enc
    · cases hj'

/-- A final addressing mode the encoder accepts for an access of `b` bytes. -/
def FinOk (b : Nat) : AMode → Prop
  | .unscaled rn s => SR rn ∧ -256 ≤ s ∧ s < 256
  | .unsignedOffset rn o => SR rn ∧ o % b = 0 ∧ o / b < 4096
  | .regReg rn rm | .regScaled rn rm => SR rn ∧ GR rm
  | .regScaledExtended rn rm e | .regExtended rn rm e => SR rn ∧ GR rm ∧ extOk e
  | _ => False

/-- An addressing mode of an allocated load/store: a frame pseudo-mode or a final one. -/
def MemOk (b : Nat) : AMode → Prop
  | .slotOffset _ | .spOffset _ | .fpOffset _ => True
  | m => FinOk b m

theorem encSP_ok {r : Reg} (h : SR r) : ∃ x, r.encSP = .ok x := by
  rcases h with ⟨n, rfl, hn⟩ | rfl
  · exact ⟨_, by simp [Reg.encSP, hn]; rfl⟩
  · exact ⟨_, rfl⟩

theorem encZR_ok {r : Reg} (h : GR r) : ∃ x, r.encZR = .ok x := by
  obtain ⟨n, rfl, hn⟩ := h
  exact ⟨_, by simp [Reg.encZR, hn]; rfl⟩

theorem encV_ok {r : Reg} (h : VR r) : ∃ x, r.encV = .ok x := by
  obtain ⟨n, rfl, hn⟩ := h
  exact ⟨_, by simp [Reg.encV, hn]; rfl⟩

theorem ldstFields_ok {b : Nat} {m : AMode} (hm : FinOk b m) (size : BitVec 2) (V : BitVec 1)
    (opc : BitVec 2) (Rt : BitVec 5) : ∃ a, ldstFields size V opc b Rt m = .ok a := by
  cases m <;> simp only [FinOk] at hm
  case unscaled rn s =>
    obtain ⟨x, hx⟩ := encSP_ok hm.1
    simp [ldstFields, hx, sField, hm.2.1, hm.2.2, bind, Except.bind, pure, Except.pure]
  case unsignedOffset rn o =>
    obtain ⟨x, hx⟩ := encSP_ok hm.1
    simp [ldstFields, hx, uField, hm.2.1, hm.2.2, bind, Except.bind, pure, Except.pure]
  case regReg rn rm | regScaled rn rm =>
    obtain ⟨x, hx⟩ := encSP_ok hm.1
    obtain ⟨y, hy⟩ := encZR_ok hm.2
    simp [ldstFields, hx, hy, bind, Except.bind, pure, Except.pure]
  case regScaledExtended rn rm e | regExtended rn rm e =>
    obtain ⟨x, hx⟩ := encSP_ok hm.1
    obtain ⟨y, hy⟩ := encZR_ok hm.2.1
    have he := hm.2.2
    unfold extOk at he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [ldstFields, hx, hy, bind, Except.bind, pure, Except.pure]

/-- `mem_finalize`'s final mode of a frame offset. -/
theorem fin_enc {base : Reg} {off : Int} {b : Nat} {pre : List Line} {m' : AMode} (hb : SR base)
    (e : (match simm9? off with
      | some s => ([], AMode.unscaled base s)
      | none => match uimm12Scaled? off b with
        | some o => ([], AMode.unsignedOffset base o)
        | none => (loadConst64 (.x 16) (u64 off), AMode.regExtended base (.x 16) .sxtx)) = (pre, m')) :
    (∀ i t, Line.ins i t ∈ pre → i.encodable = true) ∧ FinOk b m' := by
  split at e
  · rename_i s hs
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    unfold simm9? at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨(fun _ _ h => by cases h), by simp only [FinOk]; exact ⟨hb, by omega, by omega⟩⟩
    · cases hs
  · split at e
    · rename_i o ho
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      unfold uimm12Scaled? at ho
      split at ho
      · rename_i hc
        simp only [Option.some.injEq] at ho; subst ho
        refine ⟨(fun _ _ h => by cases h), ?_⟩
        simp only [FinOk]
        refine ⟨hb, by simpa using hc.2.2, ?_⟩
        rcases Nat.eq_zero_or_pos b with hb0 | hb0
        · subst hb0; simp
        · exact Nat.div_lt_of_lt_mul (by omega)
      · cases ho
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨loadConst64_enc (by decide) _, by simp only [FinOk]; exact ⟨hb, gr_x (by decide), by unfold extOk; simp⟩⟩

theorem memFinalize_enc {c : FnCtx} {m : AMode} {b : Nat} {pre : List Line} {m' : AMode}
    (hm : MemOk b m) (h : memFinalize c m b = .ok (pre, m')) :
    (∀ i t, Line.ins i t ∈ pre → i.encodable = true) ∧ FinOk b m' := by
  unfold memFinalize at h
  cases m <;> simp only [MemOk, pure, Except.pure, Except.ok.injEq] at hm h
  case spOffset off => exact fin_enc (.inr rfl) h
  case fpOffset off => exact fin_enc (.inl (gr_x (by decide))) h
  case slotOffset off => exact fin_enc (.inr rfl) h
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := h; exact ⟨(fun _ _ h => by cases h), hm⟩)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h)
    | exact hm.elim

/-- The register of a load/store: a SIMD&FP register for the 128-bit forms, else a GPR. -/
def LdReg (fp : Bool) (r : Reg) : Prop := if fp then VR r else GR r

theorem rt_ok {fp : Bool} {V : BitVec 1} {rt : Reg} (hV : V = (if fp then 1 else 0))
    (hrt : LdReg fp rt) : ∃ y, (if V == 1 then rt.encV else rt.encZR) = .ok y := by
  subst hV
  cases fp <;> simp only [LdReg] at hrt <;> simp
  · exact encZR_ok hrt
  · exact encV_ok hrt

theorem linesEnc_load {c : FnCtx} {op : LoadOp} {rt : Reg} {m : AMode} {fl : Clif.MemFlags}
    (hrt : LdReg (op == .fpuLoad128) rt) (hm : MemOk op.bytes m) : LinesEnc c (.load op rt m fl) := by
  intro ps ls ps' hl i t hi
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i r hr
  obtain ⟨pre, m'⟩ := r
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  obtain ⟨hpre, hfin⟩ := memFinalize_enc hm hr
  rcases List.mem_append.mp hi with hi | hi
  · exact hpre i t hi
  simp only [List.mem_singleton, Line.ins.injEq] at hi
  obtain ⟨rfl, -⟩ := hi
  rw [encodable_iff]
  rcases hfe : op.fields with ⟨sz, V, opc⟩
  obtain ⟨y, hy⟩ := rt_ok (V := V) (by cases op <;> simp_all [LoadOp.fields]) hrt
  obtain ⟨a, ha⟩ := ldstFields_ok hfin sz V opc y
  refine ⟨a, ?_⟩
  simp only [Insn.armFields, hfe, bind, Except.bind]
  split <;> rename_i hV <;> simp only [hV, ite_true, Bool.false_eq_true, ite_false] at hy <;>
    rw [hy] <;> exact ha

theorem linesEnc_store {c : FnCtx} {op : StoreOp} {rt : Reg} {m : AMode} {fl : Clif.MemFlags}
    (hrt : LdReg (op == .fpuStore128) rt) (hm : MemOk op.bytes m) : LinesEnc c (.store op rt m fl) := by
  intro ps ls ps' hl i t hi
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i r hr
  obtain ⟨pre, m'⟩ := r
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  obtain ⟨hpre, hfin⟩ := memFinalize_enc hm hr
  rcases List.mem_append.mp hi with hi | hi
  · exact hpre i t hi
  simp only [List.mem_singleton, Line.ins.injEq] at hi
  obtain ⟨rfl, -⟩ := hi
  rw [encodable_iff]
  rcases hfe : op.fields with ⟨sz, V, opc⟩
  obtain ⟨y, hy⟩ := rt_ok (V := V) (by cases op <;> simp_all [StoreOp.fields]) hrt
  obtain ⟨a, ha⟩ := ldstFields_ok hfin sz V opc y
  refine ⟨a, ?_⟩
  simp only [Insn.armFields, hfe, bind, Except.bind]
  split <;> rename_i hV <;> simp only [hV, ite_true, Bool.false_eq_true, ite_false] at hy <;>
    rw [hy] <;> exact ha

/-! ## Straight-line forms -/

set_option hygiene false in
/-- Compute the operands and invert the allocation of a concrete form; the allocated registers
become `.x n`/`.v n` with their `RegFits` bounds. -/
macro "inv_op" : tactic => `(tactic| (
  simp (config := {decide := true}) [MInst.operands, MInst.visitOperands, AMode.visit,
    CondBrKind.visit, StateT.run, bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, OpSpec.use,
    OpSpec.def_, OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef, OpSpec.reuseDef,
    throw, throwThe, MonadExceptOf.throw, StateT.lift] at hops
  subst hops
  rcases regs with ⟨_|⟨r0,_|⟨r1,_|⟨r2,_|⟨r3,_|⟨r4,_|⟨r5,_⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [MInst.assign, MInst.visitOperands, AMode.visit, CondBrKind.visit, StateT.run, bind,
      StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, pure,
      StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift] at hasg
  all_goals (
    subst hasg
    have hf := hal.fits
    simp [RegFits, OpSpec.use, OpSpec.def_, OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef,
      OpSpec.reuseDef] at hf
    destr
    subst_vars)))

@[simp] theorem os32 : (OperandSize.size32 == OperandSize.size64) = false := rfl
@[simp] theorem os64 : (OperandSize.size64 == OperandSize.size64) = true := rfl

theorem bitmask_some {M : Nat} {is64 : Bool} {v : Nat} {e : BitVec M} (h : bitmaskOk M is64 v e = true) :
    ∃ r, bitmaskEnc? is64 v = some r := by
  unfold bitmaskOk at h
  split at h
  · cases h
  · exact ⟨_, ‹_›⟩

theorem linesEnc_logic {c : FnCtx} {op : ALUOp} {sz : OperandSize} {rd rn : Reg} {imm : ImmLogic}
    (hop : logicOpOk op = true) (hi : logicImmOk op sz imm = true)
    (hrd : GR rd ∨ (rd = .xzr ∧ op = .andS)) (hrn : GR rn ∨ rn = .xzr) :
    LinesEnc c (.aluRRImmLogic op sz rd rn imm) := by
  cases op <;> simp only [logicOpOk, reduceCtorEq] at hop <;> cases sz <;>
    obtain ⟨⟨N, immr, imms⟩, hb⟩ := bitmask_some hi <;>
    (try simp only [Nat.reducePow, ImmLogic.invert] at hb) <;>
    refine linesEnc_one (fun _ => rfl) ?_ <;> rw [encodable_iff] <;>
    rcases hrd with ⟨n, rfl, hn⟩ | ⟨rfl, hS⟩ <;>
    (try cases hS) <;>
    rcases hrn with ⟨k, rfl, hk⟩ | rfl <;>
    simp (config := {decide := true}) (disch := omega) [Insn.armFields, ALUOp.logic?, hb,
      Reg.encSP, Reg.encZR, ite_eq_left, OperandSize.is64, bind, Except.bind, pure, Except.pure,
      ImmLogic.invert, os32, os64]

theorem linesEnc_extend {c : FnCtx} {a b : Nat} {sg : Bool} {f t : Nat} (ha : a ≤ 30) (hb : b ≤ 30)
    (h : ((!sg && f == 1) || (!sg && f == 32 && t == 64) ||
      decide (f - 1 < (if sg && t > 32 then 64 else 32))) = true) :
    LinesEnc c (.extend (.x a) (.x b) sg f t) := by
  have e1 : bitmaskEnc? false 1 = some (0#1, 0#6, 0#6) := by decide
  by_cases h1 : (!sg && f == 1) = true
  · refine linesEnc_one (fun ps => by simp only [MInst.lines, h1, ite_true]; rfl) ?_
    rw [encodable_iff]
    simp (disch := omega) [Insn.armFields, ALUOp.logic?, e1, Reg.encSP, Reg.encZR, ite_eq_left,
      bind, Except.bind, pure, Except.pure]
  by_cases h2 : (!sg && f == 32 && t == 64) = true
  · refine linesEnc_one (fun ps => by simp only [MInst.lines, h1, h2, ite_true]; rfl) ?_
    enc
  simp only [h1, h2, Bool.false_or, decide_eq_true_eq] at h
  cases sg
  · refine linesEnc_one (fun ps => by simp only [MInst.lines, h1, h2]; rfl) ?_
    enc
  · refine linesEnc_one (fun ps => by simp only [MInst.lines, h1, h2]; rfl) ?_
    enc

theorem addOff_enc {rd rn : Reg} {off : Int} (hrd : GR rd) (hrn : SR rn) (ho : -256 ≤ off ∧ off < 4096) :
    ∀ i t, Line.ins i t ∈ MInst.lines.addOff rd rn off → i.encodable = true := by
  intro i t h
  obtain ⟨n, rfl, hn⟩ := hrd
  unfold MInst.lines.addOff at h
  split at h
  · split at h
    · cases h
    · simp only [List.mem_singleton, Line.ins.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rcases hrn with ⟨m, rfl, hm⟩ | rfl <;> enc
  · split at h <;> simp only [List.mem_singleton, Line.ins.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      rcases hrn with ⟨m, rfl, hm⟩ | rfl <;> enc

theorem linesEnc_loadAddr {c : FnCtx} {rd : Reg} {off : Int} (hrd : GR rd) :
    LinesEnc c (.loadAddr rd (.slotOffset off)) := by
  intro ps ls ps' hl i t hi
  simp only [MInst.lines, bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i r hr
  obtain ⟨pre, m'⟩ := r
  obtain ⟨hpre, hfin⟩ := memFinalize_enc (b := 1) (m := .slotOffset off) trivial hr
  simp only at hl
  split at hl
  · rename_i rn rm e
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    rcases List.mem_append.mp hi with hi | hi
    · exact hpre i t hi
    simp only [List.mem_singleton, Line.ins.injEq] at hi
    obtain ⟨rfl, -⟩ := hi
    simp only [FinOk] at hfin
    obtain ⟨⟨k, rfl, hk⟩ | rfl, ⟨j, rfl, hj⟩, -⟩ := hfin <;> obtain ⟨n, rfl, hn⟩ := hrd <;>
      cases e <;> enc
  · rename_i rn o
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    rcases List.mem_append.mp hi with hi | hi
    · exact hpre i t hi
    simp only [FinOk] at hfin
    exact addOff_enc hrd hfin.1 ⟨by omega, by omega⟩ i t hi
  · rename_i rn o
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    rcases List.mem_append.mp hi with hi | hi
    · exact hpre i t hi
    simp only [FinOk] at hfin
    exact addOff_enc hrd hfin.1 ⟨by omega, by have := hfin.2.2; simp at this; omega⟩ i t hi
  · simp [throw, throwThe, MonadExceptOf.throw] at hl

theorem formOk_load_enc {c : FnCtx} {op : LoadOp} {d : Nat} {m : AMode} {fl : Clif.MemFlags}
    {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (h : (op != .fpuLoad128 && memOk op.bytes m) = true)
    (hops : (MInst.load op (.vreg d .int) m fl).operands = .ok ops) (hal : AllocOk ops regs)
    (hasg : (MInst.load op (.vreg d .int) m fl).assign regs = .ok i') : LinesEnc c i' := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hop, hm⟩ := h
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> inv_op <;>
    refine linesEnc_load (by simp [LdReg, hop]; exact gr_x (by omega)) ?_
  all_goals simp_all [MemOk, FinOk, SR, GR, extOk]
  all_goals first | omega | exact ⟨by omega, by omega, of_decide_eq_true hm⟩

theorem formOk_store_enc {c : FnCtx} {op : StoreOp} {d : Nat} {m : AMode} {fl : Clif.MemFlags}
    {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (h : (op != .fpuStore128 && memOk op.bytes m) = true)
    (hops : (MInst.store op (.vreg d .int) m fl).operands = .ok ops) (hal : AllocOk ops regs)
    (hasg : (MInst.store op (.vreg d .int) m fl).assign regs = .ok i') : LinesEnc c i' := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hop, hm⟩ := h
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> inv_op <;>
    refine linesEnc_store (by simp [LdReg, hop]; exact gr_x (by omega)) ?_
  all_goals simp_all [MemOk, FinOk, SR, GR, extOk]
  all_goals first | omega | exact ⟨by omega, by omega, of_decide_eq_true hm⟩

set_option maxHeartbeats 4000000 in
theorem formOk_enc {c cx : FnCtx} {i i' : MInst} {ops : Array Operand} {regs : Array Reg}
    (h : FormOk cx i = true) (himm : immOkB i = true) (hops : i.operands = .ok ops)
    (hal : AllocOk ops regs) (hasg : i.assign regs = .ok i') : LinesEnc c i' := by
  unfold FormOk at h
  split at h
  rotate_left 32
  · exact formOk_load_enc h hops hal hasg
  · exact formOk_store_enc h hops hal hasg
  rotate_left
  all_goals (try cases h)
  all_goals have himm0 := himm
  all_goals simp [immOkB] at himm
  all_goals (try inv_op)
  all_goals first
    | (cases_op <;> first
        | (simp [shiftOpOk] at h; done)
        | (apply linesEnc_one (fun _ => rfl); enc; done))
    | (simp only [Bool.and_eq_true] at h
       exact linesEnc_logic h.1 h.2 (.inl (gr_x (by omega))) (.inl (gr_x (by omega))))
    | (simp only [Bool.and_eq_true] at h
       exact linesEnc_logic h.1 h.2 (.inl (gr_x (by omega))) (.inr rfl))
    | (simp only [Bool.and_eq_true, beq_iff_eq] at h
       obtain ⟨rfl, h2⟩ := h
       exact linesEnc_logic rfl h2 (.inr ⟨rfl, rfl⟩) (.inl (gr_x (by omega))))
    | exact linesEnc_extend (by omega) (by omega) himm0
    | exact linesEnc_loadAddr (gr_x (by omega))
    | (have h' := of_decide_eq_true h
       simp only [AtomTy] at h'
       rcases h' with rfl | rfl | rfl | rfl <;> (apply linesEnc_one (fun _ => rfl); enc; done))



/-! ## Control forms -/

set_option hygiene false in
/-- Expand concrete lines and decide the encoding of each instruction line. -/
macro "lines_fin" : tactic => `(tactic| (
  intro ps ls ps' hl i t hm
  simp [MInst.lines, pure, Except.pure, bind, Except.bind, CondBrKind.insn, rmwLoopLines,
    rmwLoopBody, rmwLoopMid, rmwLoopSext, rmwLoopCmp, rmwLoopStored, casLoopLines, casLoopHead,
    casLoopCmp, throw, throwThe, MonadExceptOf.throw] at hl
  all_goals destr_all
  all_goals subst_vars
  all_goals simp at hm
  all_goals destr_all
  all_goals subst_vars
  all_goals enc))

def Grows {α : Type} (x : StateT (Array Operand) (Except String) α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → ∃ t, s' = s ++ t

theorem grows_pure {α : Type} (a : α) : Grows (pure a : StateT (Array Operand) (Except String) α) := by
  intro s b s' h
  cases h
  exact ⟨#[], by simp⟩

theorem grows_bind {α β : Type} {x : StateT (Array Operand) (Except String) α}
    {f : α → StateT (Array Operand) (Except String) β} (hx : Grows x) (hf : ∀ a, Grows (f a)) :
    Grows (x >>= f) := by
  intro s b s'' h
  rw [StateT.run_bind] at h
  cases hr : x.run s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hr] at h
    obtain ⟨t1, rfl⟩ := hx s a s' hr
    obtain ⟨t2, rfl⟩ := hf a _ b s'' h
    exact ⟨t1 ++ t2, by simp⟩

theorem grows_collect (sp : OpSpec) (r : Reg) : Grows (Driver.collectOp sp r) := by
  intro s a s' h
  cases r
  case vreg n c =>
    simp only [Driver.collectOp, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at h
    cases h
    exact ⟨_, Array.push_eq_append⟩
  all_goals
    simp only [Driver.collectOp] at h
    split at h
    · cases h
    · cases h
      exact ⟨#[], by simp⟩

theorem grows_mapM {α β : Type} {F : α → StateT (Array Operand) (Except String) β}
    (h : ∀ a, Grows (F a)) : ∀ l : List α, Grows (l.mapM F)
  | [] => grows_pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact grows_bind (h a) fun _ => grows_bind (grows_mapM h l) fun _ => grows_pure _

set_option hygiene false in
macro "grows_tac" : tactic => `(tactic| repeat' (first
  | exact grows_pure _
  | exact grows_collect _ _
  | refine grows_bind ?_ ?_
  | refine grows_mapM ?_ _
  | intro ⟨_, _⟩
  | intro _))

set_option hygiene false in
macro "post_tac" : tactic => `(tactic| repeat' (first
  | exact putPost_pure rfl
  | refine putPost_bind ?_
  | intro _))

/-- The first operand of an indirect call is its target. -/
theorem call_op0 {t : Nat} {cl : RegClass} {us ds : List (Reg × Reg)} {ops : Array Operand}
    (h : (MInst.call ⟨.reg (.vreg t cl), us, ds⟩).operands = .ok ops) :
    ops[0]? = some ⟨t, cl, .use, .early, .reg⟩ := by
  rw [Driver.operands_eq, visit_call_eq, StateT.run_map] at h
  cases hr : (callVisit Driver.collectOp ⟨.reg (.vreg t cl), us, ds⟩).run #[] with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    simp only [Functor.map, Except.map, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    unfold callVisit at hr
    simp only [bind_assoc, pure_bind] at hr
    rw [StateT.run_bind] at hr
    have h0 : (Driver.collectOp OpSpec.use (.vreg t cl)).run #[] =
        .ok (.vreg t cl, #[⟨t, cl, .use, .early, .reg⟩]) := rfl
    rw [h0] at hr
    simp only [bind, Except.bind] at hr
    have hg : ∀ {β : Type} (x : StateT (Array Operand) (Except String) β), Grows x →
        ∀ q, x.run #[⟨t, cl, .use, .early, .reg⟩] = .ok q → q.2[0]? = some ⟨t, cl, .use, .early, .reg⟩ := by
      intro β x hx q hq
      obtain ⟨t', ht⟩ := hx _ _ _ hq
      rw [ht, Array.getElem?_append_left (by simp)]
      rfl
    refine hg _ ?_ _ hr
    grows_tac

theorem callVisit_put {info ic : CallInfo} {regs : Array Reg} {k k' : Nat}
    (h : (callVisit (putOp regs) info).run k = .ok (ic, k')) :
    (∀ n, info.dest = .sym n → ic.dest = .sym n) ∧
    (∀ t cl, info.dest = .reg (.vreg t cl) → ∃ r0, regs[k]? = some r0 ∧ ic.dest = .reg r0) := by
  obtain ⟨dest, us, ds⟩ := info
  unfold callVisit at h
  simp only [bind_assoc, pure_bind] at h
  cases dest with
  | sym n =>
    refine ⟨fun n' e => ?_, (fun _ _ e => by cases e)⟩
    cases e
    refine (fun {x : StateT Nat (Except String) CallInfo} (hp : PutPost x (fun ic => ic.dest = .sym n))
      (h : x.run k = .ok (ic, k')) => hp _ _ _ h) ?_ h
    post_tac
  | reg r =>
    refine ⟨(fun _ e => by cases e), fun t cl e => ?_⟩
    cases e
    rw [StateT.run_bind] at h
    cases h0 : regs[k]? with
    | none =>
      have : (putOp regs OpSpec.use (.vreg t cl)).run k = .error "fewer allocations than operands" := by
        simp [putOp, StateT.run, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
          StateT.get, set, StateT.set, pure, StateT.pure, Except.pure, h0, throw, throwThe,
          MonadExceptOf.throw, StateT.lift]
      rw [this] at h; cases h
    | some r0 =>
      have : (putOp regs OpSpec.use (.vreg t cl)).run k = .ok (r0, k + 1) := by
        simp [putOp, StateT.run, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
          StateT.get, set, StateT.set, pure, StateT.pure, Except.pure, h0]
      rw [this] at h
      simp only [bind, Except.bind] at h
      refine ⟨r0, rfl, (fun {x : StateT Nat (Except String) CallInfo}
        (hp : PutPost x (fun ic => ic.dest = .reg r0)) (h : x.run (k + 1) = .ok (ic, k')) => hp _ _ _ h) ?_ h⟩
      post_tac

/-- The allocated call: same symbol, or the allocated target register. -/
theorem assign_call {info : CallInfo} {regs : Array Reg} {i' : MInst}
    (h : (MInst.call info).assign regs = .ok i') :
    ∃ ic, i' = .call ic ∧ (∀ n, info.dest = .sym n → ic.dest = .sym n) ∧
      (∀ t cl, info.dest = .reg (.vreg t cl) → ∃ r0, regs[0]? = some r0 ∧ ic.dest = .reg r0) := by
  rw [assign_eq, visit_call_eq, StateT.run_map] at h
  simp only [bind, Except.bind, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i p hp
  split at hp
  · cases hp
  rename_i q hq
  simp only [Except.ok.injEq] at hp
  subst hp
  split at h
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨h1, h2⟩ := callVisit_put (k := 0) (k' := q.2) (by rw [hq])
  exact ⟨q.1, rfl, h1, h2⟩

theorem linesEnc_call {c : FnCtx} {ic : CallInfo} (h : ∀ r, ic.dest = .reg r → GR r) :
    LinesEnc c (.call ic) := by
  obtain ⟨d, us, ds⟩ := ic
  cases d with
  | sym n => exact linesEnc_one (fun _ => rfl) (by enc)
  | reg r =>
    obtain ⟨n, rfl, hn⟩ := h r rfl
    exact linesEnc_one (fun _ => rfl) (by enc)

theorem linesEnc_tryCall {c : FnCtx} {ic : CallInfo} {ti : TryInfo} (h : ∀ r, ic.dest = .reg r → GR r) :
    LinesEnc c (.tryCall ic ti) := by
  obtain ⟨d, us, ds⟩ := ic
  cases d with
  | sym n => lines_fin
  | reg r =>
    obtain ⟨n, rfl, hn⟩ := h r rfl
    lines_fin

theorem fits_at {ops : Array Operand} {regs : Array Reg} (hal : AllocOk ops regs) {j : Nat}
    {o : Operand} {r : Reg} (ho : ops[j]? = some o) (hr : regs[j]? = some r) : RegFits o r := by
  apply hal.fits (o, r)
  rw [Array.toList_zip]
  apply List.mem_iff_getElem?.mpr
  exact ⟨j, by rw [List.getElem?_zip_eq_some]; simpa using ⟨ho, hr⟩⟩

/-- The target of an allocated indirect call with an int vreg target is a GPR. -/
theorem call_dest_gr {info ic : CallInfo} {ops : Array Operand} {regs : Array Reg}
    (himm : (match info.dest with | .sym _ => true | .reg r => r.isVregInt) = true)
    (hops : (MInst.call info).operands = .ok ops) (hal : AllocOk ops regs)
    (h1 : ∀ n, info.dest = .sym n → ic.dest = .sym n)
    (h2 : ∀ t cl, info.dest = .reg (.vreg t cl) → ∃ r0, regs[0]? = some r0 ∧ ic.dest = .reg r0) :
    ∀ r, ic.dest = .reg r → GR r := by
  obtain ⟨d, us, ds⟩ := info
  intro r hr
  cases d with
  | sym n => rw [h1 n rfl] at hr; cases hr
  | reg x =>
    obtain ⟨t, rfl⟩ := vregInt_eq himm
    obtain ⟨r0, h0, hd⟩ := h2 t .int rfl
    rw [hd] at hr; cases hr
    have hf := fits_at hal (call_op0 hops) h0
    simp only [RegFits] at hf
    obtain ⟨⟨n, rfl, hn, -⟩, -⟩ := hf
    exact gr_x (by omega)

theorem putPost_args (regs : Array Reg) (ds : List (Reg × Reg)) :
    PutPost (MInst.visitOperands (putOp regs) (.args ds)) (fun m => ∃ ds, m = .args ds) := by
  simp only [MInst.visitOperands]
  exact putPost_bind fun _ => putPost_pure ⟨_, rfl⟩

theorem putPost_rets (regs : Array Reg) (us : List (Reg × Reg)) :
    PutPost (MInst.visitOperands (putOp regs) (.rets us)) (fun m => ∃ us, m = .rets us) := by
  simp only [MInst.visitOperands]
  exact putPost_bind fun _ => putPost_pure ⟨_, rfl⟩

theorem linesEnc_rmw {c : FnCtx} {ty : CTy} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags}
    (hb : ((ty.bits = 8 ∨ ty.bits = 16) ∨ ty.bits = 32) ∨ ty.bits = 64) :
    LinesEnc c (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)) := by
  intro ps ls ps' hl i t hm
  have e : (MInst.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)).lines c ps =
      .ok (rmwLoopLines ty.bits op fl (.loop ps.aloop), { ps with aloop := ps.aloop + 1 }) := by
    simp [MInst.lines, pure, Except.pure]
  rw [e] at hl
  simp only [Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  generalize ty.bits = bits at hb hm
  rcases hb with ((rfl | rfl) | rfl) | rfl <;> cases op <;>
    simp [rmwLoopLines, rmwLoopBody, rmwLoopMid, rmwLoopSext, rmwLoopCmp, rmwLoopStored] at hm <;>
    destr_all <;> subst_vars <;> enc

theorem linesEnc_cas {c : FnCtx} {ty : CTy} {fl : Clif.MemFlags}
    (hb : ((ty.bits = 8 ∨ ty.bits = 16) ∨ ty.bits = 32) ∨ ty.bits = 64) :
    LinesEnc c (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24)) := by
  intro ps ls ps' hl i t hm
  have e : (MInst.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24)).lines c ps =
      .ok (casLoopLines ty.bits fl (.loop ps.aloop) (.loop (ps.aloop + 1)),
        { ps with aloop := ps.aloop + 2 }) := by
    simp [MInst.lines, pure, Except.pure]
  rw [e] at hl
  simp only [Except.ok.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, -⟩ := hl
  generalize ty.bits = bits at hb hm
  rcases hb with ((rfl | rfl) | rfl) | rfl <;>
    simp [casLoopLines, casLoopHead, casLoopCmp] at hm <;>
    destr_all <;> subst_vars <;> enc

theorem linesEnc_tls {c : FnCtx} {nm : String} {w : Nat} (hw : w < 29) :
    LinesEnc c (.elfTlsGetAddr nm (.x 0) (.x w)) := by
  intro ps ls ps' hl i t hm
  by_cases h0 : w = 0
  · subst h0
    simp [MInst.lines, throw, throwThe, MonadExceptOf.throw] at hl
  · have e : (MInst.elfTlsGetAddr nm (.x 0) (.x w)).lines c ps =
        .ok ([.ins (.adrpTlsDesc (.x 0) nm), .ins (.ldrTlsDescLo12 (.x w) (.x 0) nm),
          .ins (.addTlsDescLo12 (.x 0) (.x 0) nm), .ins (.blrTlsDesc (.x w) nm),
          .ins (.mrsTpidrEl0 (.x w)), .ins (.aluRRR .add true (.x 0) (.x 0) (.x w))], ps) := by
      simp [MInst.lines, h0, pure, Except.pure]
    rw [e] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    simp at hm
    destr_all <;> subst_vars <;> enc

set_option maxHeartbeats 8000000 in
/-- **The control forms**: with `ctlInstOk` (the tested and defined registers are int vregs)
and `immOkB`, every allocation the checker accepts expands to encodable lines. -/
theorem ctl_enc {c : FnCtx} {i i' : MInst} {ops : Array Operand} {regs : Array Reg} {b k : Nat}
    (hc : i.isCtl = true) (hok : ctlInstOk b k i = true) (himm : immOkB i = true)
    (hops : i.operands = .ok ops) (hal : AllocOk ops regs) (hasg : i.assign regs = .ok i') :
    LinesEnc c i' := by
  cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hc
  case call info =>
    obtain ⟨ic, rfl, h1, h2⟩ := assign_call hasg
    exact linesEnc_call (call_dest_gr himm hops hal h1 h2)
  case tryCall info ti =>
    obtain ⟨ic, rfl, hc'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
    obtain ⟨ic', e, h1, h2⟩ := assign_call hc'
    cases e
    rw [operands_tryCall_call] at hops
    exact linesEnc_tryCall (call_dest_gr himm hops hal h1 h2)
  case args ds =>
    obtain ⟨_, rfl⟩ := assign_post hasg (putPost_args regs ds)
    intro ps ls ps' h; simp [MInst.lines, throw, throwThe, MonadExceptOf.throw] at h
  case rets us =>
    obtain ⟨_, rfl⟩ := assign_post hasg (putPost_rets regs us)
    intro ps ls ps' h; simp [MInst.lines, throw, throwThe, MonadExceptOf.throw] at h
  case condBr a b' kd =>
    rcases kd with ⟨r, sz⟩ | ⟨r, sz⟩ | cd
    · obtain ⟨n, rfl⟩ := vregInt_eq (by simpa [ctlInstOk] using hok)
      inv_op; lines_fin
    · obtain ⟨n, rfl⟩ := vregInt_eq (by simpa [ctlInstOk] using hok)
      inv_op; lines_fin
    · inv_op; lines_fin
  case trapIf kd code =>
    rcases kd with ⟨r, sz⟩ | ⟨r, sz⟩ | cd
    · obtain ⟨n, rfl⟩ := vregInt_eq (by simpa [ctlInstOk] using hok)
      inv_op; lines_fin
    · obtain ⟨n, rfl⟩ := vregInt_eq (by simpa [ctlInstOk] using hok)
      inv_op; lines_fin
    · inv_op; lines_fin
  case testBitAndBranch kd a b' r bit =>
    obtain ⟨n, rfl⟩ := vregInt_eq (by simpa [ctlInstOk] using hok)
    inv_op; lines_fin
  case loadExtNameGot r nm =>
    obtain ⟨n, rfl⟩ := vregInt_eq (by simpa [ctlInstOk] using hok)
    inv_op; lines_fin
  case loadExtNameNear r nm off =>
    obtain ⟨n, rfl⟩ := vregInt_eq (by simpa [ctlInstOk] using hok)
    inv_op; lines_fin
  case jtSequence d ts ridx t1 t2 =>
    simp only [ctlInstOk, Bool.and_eq_true] at hok
    obtain ⟨⟨h1, h2⟩, h3⟩ := hok
    obtain ⟨n1, rfl⟩ := vregInt_eq h1
    obtain ⟨n2, rfl⟩ := vregInt_eq h2
    obtain ⟨n3, rfl⟩ := vregInt_eq h3
    inv_op; lines_fin
  case atomicRmwLoop ty op fl a o d s1 s2 =>
    simp only [ctlInstOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hok
    obtain ⟨n1, rfl⟩ := vregInt_eq h1
    obtain ⟨n2, rfl⟩ := vregInt_eq h2
    obtain ⟨n3, rfl⟩ := vregInt_eq h3
    obtain ⟨n4, rfl⟩ := vregInt_eq h4
    obtain ⟨n5, rfl⟩ := vregInt_eq h5
    simp only [immOkB, Bool.or_eq_true, beq_iff_eq] at himm
    inv_op
    exact linesEnc_rmw himm
  case atomicCasLoop ty fl a e r d s1 =>
    simp only [ctlInstOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hok
    obtain ⟨n1, rfl⟩ := vregInt_eq h1
    obtain ⟨n2, rfl⟩ := vregInt_eq h2
    obtain ⟨n3, rfl⟩ := vregInt_eq h3
    obtain ⟨n4, rfl⟩ := vregInt_eq h4
    obtain ⟨n5, rfl⟩ := vregInt_eq h5
    simp only [immOkB, Bool.or_eq_true, beq_iff_eq] at himm
    inv_op
    exact linesEnc_cas himm
  case elfTlsGetAddr nm rd tmp =>
    simp only [ctlInstOk, Bool.and_eq_true] at hok
    obtain ⟨h1, h2⟩ := hok
    obtain ⟨n1, rfl⟩ := vregInt_eq h1
    obtain ⟨n2, rfl⟩ := vregInt_eq h2
    inv_op
    exact linesEnc_tls (by omega)
  all_goals (inv_op; lines_fin)

/-! ## Moves -/

theorem ldReg_of_locOk {c : CheckCtx} {r : Reg} {cls : RegClass} (h : c.locOk (.reg r) cls = true) :
    LdReg (cls == .float) r ∧ r.realClass? = some cls := by
  obtain ⟨h1, h2⟩ := locOk_reg h
  refine ⟨?_, h1⟩
  rcases allocatable_cases h2 with ⟨n, rfl, hn, -⟩ | ⟨n, rfl, hn⟩
  · simp only [Reg.realClass?, Option.some.injEq] at h1
    subst h1
    exact gr_x (by omega)
  · simp only [Reg.realClass?, Option.some.injEq] at h1
    subst h1
    exact ⟨n, rfl, by omega⟩

theorem spAddrX16_enc (c : FnCtx) (off : Nat) : ∀ m ∈ spAddrX16 off, LinesEnc c m := by
  intro m hm
  simp [spAddrX16] at hm
  destr_all <;> subst_vars <;> exact linesEnc_one (fun _ => rfl) (by enc)

theorem x16_fin (b : Nat) : FinOk b (.unsignedOffset (.x 16) 0) :=
  ⟨.inl (gr_x (by decide)), by simp, by simp⟩

theorem slotStoreAt_enc {c : FnCtx} {cls : RegClass} {r : Reg} (off : Nat)
    (hr : LdReg (cls == .float) r) : ∀ m ∈ slotStoreAt cls r off, LinesEnc c m := by
  intro m hm
  unfold slotStoreAt at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    cases cls
    · exact linesEnc_store (by simpa [LdReg] using hr) trivial
    · exact linesEnc_store (by simpa [LdReg] using hr) trivial
  · rcases List.mem_append.mp hm with hm | hm
    · exact spAddrX16_enc c off m hm
    · simp only [List.mem_singleton] at hm
      subst hm
      cases cls
      · exact linesEnc_store (by simpa [LdReg] using hr) (x16_fin _)
      · exact linesEnc_store (by simpa [LdReg] using hr) (x16_fin _)

theorem slotLoadAt_enc {c : FnCtx} {cls : RegClass} {r : Reg} (off : Nat)
    (hr : LdReg (cls == .float) r) : ∀ m ∈ slotLoadAt cls r off, LinesEnc c m := by
  intro m hm
  unfold slotLoadAt at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    cases cls
    · exact linesEnc_load (by simpa [LdReg] using hr) trivial
    · exact linesEnc_load (by simpa [LdReg] using hr) trivial
  · rcases List.mem_append.mp hm with hm | hm
    · exact spAddrX16_enc c off m hm
    · simp only [List.mem_singleton] at hm
      subst hm
      cases cls
      · exact linesEnc_load (by simpa [LdReg] using hr) (x16_fin _)
      · exact linesEnc_load (by simpa [LdReg] using hr) (x16_fin _)

/-- **Moves**: a move the checker accepts expands to encodable lines. -/
theorem moveInsts_enc {c : FnCtx} {cc : CheckCtx} {w : String} {fr : RAFrame} {src dst : Loc}
    {l : List AInst} (hchk : cc.checkMove w src dst = .ok ()) (h : fr.moveInsts src dst = .ok l) :
    ∀ m, AInst.inst m ∈ l → LinesEnc c m := by
  obtain ⟨cls, -, hs, hd, -⟩ := checkMove_facts hchk
  intro m hm
  unfold RAFrame.moveInsts at h
  split at h
  · rename_i a b
    obtain ⟨ha, hca⟩ := ldReg_of_locOk hs
    obtain ⟨hb, -⟩ := ldReg_of_locOk hd
    rw [hca] at h
    cases cls
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [List.mem_singleton, AInst.inst.injEq] at hm
      subst hm
      simp only [LdReg] at ha hb
      obtain ⟨n, rfl, hn⟩ := ha
      obtain ⟨n', rfl, hn'⟩ := hb
      exact linesEnc_one (fun _ => rfl) (by enc)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨m', hm', e⟩ := List.mem_map.mp hm
      cases e
      rcases List.mem_append.mp hm' with hm' | hm'
      · exact slotStoreAt_enc _ ha m hm'
      · exact slotLoadAt_enc _ hb m hm'
  · rename_i a m0 _
    obtain ⟨ha, hca⟩ := ldReg_of_locOk hs
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨m', hm', e⟩ := List.mem_map.mp hm
    cases e
    rw [hca] at hm'
    exact slotStoreAt_enc _ ha m hm'
  · rename_i m0 b _
    obtain ⟨hb, hcb⟩ := ldReg_of_locOk hd
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨m', hm', e⟩ := List.mem_map.mp hm
    cases e
    rw [hcb] at hm'
    exact slotLoadAt_enc _ hb m hm'
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Prologue, epilogue, blocks -/

/-- Every instruction line `a` expands to is encodable. -/
def AEnc (c : FnCtx) (af : AFunc) (a : AInst) : Prop :=
  ∀ ps ls ps', ainstLines c af a ps = .ok (ls, ps') → ∀ i t, Line.ins i t ∈ ls → i.encodable = true

theorem imm12_bits {v : Nat} {i : Imm12} (h : Imm12.ofNat? v = some i) : i.bits < 4096 := by
  unfold Imm12.ofNat? at h
  simp only at h
  split at h
  · cases h; simp only; omega
  · split at h
    · rename_i h2
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      show mask64 v / 4096 < 4096
      omega
    · cases h

theorem frameAdj_enc {size : Nat} (op : ALUOp) (hop : op = .add ∨ op = .sub) :
    ∀ i t, Line.ins i t ∈ (if size == 0 then []
      else match Imm12.ofNat? size with
        | some i => [Line.ins (.aluImm12 op true .sp .sp i)]
        | none => loadConst64 (.x 16) size ++ [.ins (.aluRRRExtend op true .sp .sp (.x 16) .uxtx)]) →
      i.encodable = true := by
  intro i t h
  split at h
  · cases h
  · split at h
    · rename_i im him
      have := imm12_bits him
      simp only [List.mem_singleton, Line.ins.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rcases hop with rfl | rfl <;> enc
    · rcases List.mem_append.mp h with h | h
      · exact loadConst64_enc (by decide) _ i t h
      · simp only [List.mem_singleton, Line.ins.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rcases hop with rfl | rfl <;> enc

theorem aEnc_prologue (c : FnCtx) (af : AFunc) : AEnc c af .prologue := by
  intro ps ls ps' h i t hi
  simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  split at hi
  · simp only [prologueLines, List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hi
    rcases hi with (h | h) | h
    · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; enc
    · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; enc
    · exact frameAdj_enc .sub (.inr rfl) i t h
  · cases hi

theorem aEnc_epilogue (c : FnCtx) (af : AFunc) : AEnc c af .epilogueRet := by
  intro ps ls ps' h i t hi
  simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  split at hi
  · simp only [epilogueLines, List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h
    · exact frameAdj_enc .add (.inl rfl) i t h
    · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; enc
    · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; enc
  · simp only [List.mem_singleton, Line.ins.injEq] at hi
    obtain ⟨rfl, -⟩ := hi
    enc

theorem codeLinesE_enc {c : FnCtx} {af : AFunc} : ∀ {code : List AInst} {ps ls ps'},
    (∀ a ∈ code, AEnc c af a) → codeLinesE c af code ps = .ok (ls, ps') →
    ∀ i t, Line.ins i t ∈ ls → i.encodable = true
  | [], ps, ls, ps', _, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro i t hi; cases hi
  | a :: as, ps, ls, ps', hA, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    rename_i r1 h1
    split at h
    · cases h
    rename_i r2 h2
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro i t hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hA a (List.mem_cons_self ..) _ _ _ h1 i t hi
    · exact codeLinesE_enc (fun a' ha' => hA a' (List.mem_cons_of_mem _ ha')) h2 i t hi

theorem blocksLinesE_enc {c : FnCtx} {af : AFunc} : ∀ {bs : List (Label × Array AInst)} {ps ls ps'},
    (∀ x ∈ bs, ∀ a ∈ x.2.toList, AEnc c af a) → blocksLinesE c af bs ps = .ok (ls, ps') →
    ∀ i t, Line.ins i t ∈ ls → i.encodable = true
  | [], ps, ls, ps', _, h => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro i t hi; cases hi
  | (l, code) :: bs, ps, ls, ps', hA, h => by
    simp only [blocksLinesE, bind, Except.bind] at h
    split at h
    · cases h
    rename_i r1 h1
    split at h
    · cases h
    rename_i r2 h2
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro i t hi
    simp only [List.cons_append, List.mem_cons, reduceCtorEq, false_or] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact codeLinesE_enc (hA _ (List.mem_cons_self ..)) h1 i t hi
    · exact blocksLinesE_enc (fun x hx => hA x (List.mem_cons_of_mem _ hx)) h2 i t hi

/-! ## Fall-through and relaxation keep encodability -/

theorem encodable_invertTo {c : Insn} (h : c.encodable = true) (l : Lbl) :
    (c.invertTo l).encodable = true := by
  cases c with
  | bcond cd t =>
    rw [encodable_iff]
    cases l <;> simp [Insn.invertTo, Insn.armFields, Env.pcRel, Env.rel, Env.target, bind, Except.bind,
      pure, Except.pure]
  | cbz nz w rt t =>
    rw [encodable_iff] at h ⊢
    obtain ⟨a, ha⟩ := h
    cases hy : rt.encZR with
    | error e =>
      cases t <;> simp [Insn.armFields, hy, Env.pcRel, Env.rel, Env.target, bind, Except.bind, pure,
        Except.pure] at ha
    | ok y =>
      cases l <;> simp [Insn.invertTo, Insn.armFields, hy, Env.pcRel, Env.rel, Env.target, bind,
        Except.bind, pure, Except.pure]
  | tbz nz rt bit t =>
    rw [encodable_iff] at h ⊢
    obtain ⟨a, ha⟩ := h
    by_cases hb : 64 ≤ bit
    · simp [Insn.armFields, hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ha
    cases hy : rt.encZR with
    | error e =>
      cases t <;> simp [Insn.armFields, hy, hb, Env.pcRel, Env.rel, Env.target, bind, Except.bind, pure,
        Except.pure] at ha
    | ok y =>
      cases l <;> simp [Insn.invertTo, Insn.armFields, hy, hb, Env.pcRel, Env.rel, Env.target, bind,
        Except.bind, pure, Except.pure]
  | _ => exact h

theorem b_encodable (l : Lbl) : (Insn.b l).encodable = true := by
  cases l <;> enc

/-- All instruction lines of `L` are encodable. -/
def AllEnc (L : List Line) : Prop := ∀ i t, Line.ins i t ∈ L → i.encodable = true

theorem allEnc_append {L M : List Line} (h1 : AllEnc L) (h2 : AllEnc M) : AllEnc (L ++ M) := by
  intro i t h
  rcases List.mem_append.mp h with h | h
  · exact h1 i t h
  · exact h2 i t h

theorem ftStep_mem {ln : Line} {n1 n2 : Option Line} {x : Line} (hx : x ∈ (ftStep ln n1 n2).1) :
    x = ln ∨ ∃ c e, ln = .ins c none ∧ x = .ins (c.invertTo e) none := by
  unfold ftStep at hx
  simp only at hx
  repeat' split at hx
  all_goals first
    | (simp only [List.mem_singleton] at hx; subst hx; exact .inr ⟨_, _, rfl, rfl⟩)
    | (simp only [List.mem_singleton] at hx; exact .inl hx)
    | (simp at hx)

theorem ftStep_enc {ln : Line} {n1 n2 : Option Line} (h : AllEnc [ln]) :
    AllEnc (ftStep ln n1 n2).1 := by
  intro i t hi
  rcases ftStep_mem hi with e | ⟨c, e', rfl, e⟩
  · exact h i t (by rw [← e]; exact List.mem_singleton_self _)
  · cases e
    exact encodable_invertTo (h c none (List.mem_singleton_self _)) _

theorem ftList_enc : ∀ (n : Nat) (L : List Line), L.length ≤ n → AllEnc L → AllEnc (ftList L)
  | _, [], _, _ => by rw [ftList]; intro i t h; cases h
  | n, ln :: rest, hn, h => by
    rw [ftList_cons]
    have hpos := ftStep_pos ln rest[0]? rest[1]?
    refine allEnc_append (ftStep_enc (fun i t hi => h i t (by simp at hi ⊢; exact .inl hi))) ?_
    cases n with
    | zero => simp at hn
    | succ n =>
      apply ftList_enc n
      · simp only [List.length_drop, List.length_cons] at hn ⊢; omega
      · intro i t hi
        exact h i t (List.mem_of_mem_drop hi)

theorem relaxLines_enc (far : Lbl → Bool) {L : List Line} (h : AllEnc L) :
    AllEnc (relaxLines far L) := by
  intro i t hi
  simp only [relaxLines, List.mem_flatMap] at hi
  obtain ⟨ln, hln, hi⟩ := hi
  unfold relaxLine at hi
  split at hi
  · rename_i c tl hr
    have hln' : ln = .ins c none := by
      unfold Line.relaxable? at hr
      split at hr
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hr
        obtain ⟨_, -, rfl, -⟩ := hr
        rfl
      · cases hr
    subst hln'
    split at hi
    · simp only [List.mem_cons, List.mem_singleton, Line.ins.injEq, List.not_mem_nil, or_false] at hi
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact encodable_invertTo (h c none hln) _
      · exact b_encodable _
    · simp only [List.mem_singleton] at hi
      rw [← hi] at hln
      exact h i t hln
  · simp only [List.mem_singleton] at hi
    rw [← hi] at hln
    exact h i t hln

theorem trapLines_enc (ts : List (Lbl × Clif.TrapCode)) : AllEnc (trapLines ts) := by
  intro i t hi
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.mem_singleton, Line.ins.injEq,
    reduceCtorEq, false_or, List.not_mem_nil, or_false] at hi
  obtain ⟨_, -, rfl, -⟩ := hi
  enc

/-! ## What the checker established for each item -/

/-- The static checks the checker ran on one item. -/
def ItemChk (c : CheckCtx) (vb : VBlock) : RItem → Prop
  | .move src dst => ∃ w, c.checkMove w src dst = .ok ()
  | .op k allocs => ∀ i, vb.insts[k]? = some i → ∃ w ops, i.operands = .ok ops ∧
      c.checkStatic w ops allocs i.clobbers = .ok ()

theorem runItems_chk {c : CheckCtx} {vb : VBlock} : ∀ {its : List RItem} {next : Nat} {a out : AState},
    c.runItems vb next its a = .ok out → ∀ it ∈ its, ItemChk c vb it
  | [], _, _, _, _ => fun it h => by cases h
  | .move src dst :: its, next, a, out, h => by
    have h' := h
    unfold CheckCtx.runItems at h'
    obtain ⟨-, h'⟩ := Except.seq_ok h'
    obtain ⟨a', h2, h3⟩ := Except.bind_ok h'
    unfold CheckCtx.stepMove at h2
    obtain ⟨hm, -⟩ := Except.seq_ok h2
    intro it hit
    rcases List.mem_cons.mp hit with rfl | hit
    · exact ⟨_, hm⟩
    · exact runItems_chk h3 it hit
  | .op k allocs :: its, next, a, out, h => by
    obtain ⟨-, -, i, ops, a', hi, hops, hst, hrest⟩ := runItems_op h
    intro it hit
    rcases List.mem_cons.mp hit with rfl | hit
    · intro i' hi'
      rw [hi] at hi'
      cases hi'
      exact ⟨_, ops, hops, (stepOp_ok hst).1⟩
    · exact runItems_chk hrest it hit

/-- An allocation with verified in-states (`AllocChecked`, e.g. `checkAlloc`'s acceptance or
the spill allocation's `spillAccepted`) passed the static checks of every item. -/
theorem allocChecked_items {vc : VCode} {rf : RFunc} (h : AllocChecked vc rf) :
    ∃ cc : CheckCtx, ∀ (b : Nat) (vb : VBlock) (items : Array RItem), vc.blocks[b]? = some vb →
      rf.blocks[b]? = some items → ∀ it ∈ items.toList, ItemChk cc vb it := by
  obtain ⟨cc, ins, a0, hc, -⟩ := h
  refine ⟨cc, fun b vb items hvb hit => ?_⟩
  obtain ⟨hb, -⟩ := Array.getElem?_eq_some_iff.mp hvb
  have hv := hc.blocks b hb
  unfold CheckCtx.verifyBlock at hv
  split at hv
  · obtain ⟨out, hr, -⟩ := Except.bind_ok hv
    obtain ⟨vb', items', hvb', hit', hri⟩ := runBlock_ok hr
    rw [hc.vc_eq, hvb] at hvb'
    rw [hc.rf_eq, hit] at hit'
    cases hvb'; cases hit'
    exact runItems_chk hri
  · cases hv

theorem ctlInstOk_of_ctlCheck {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true) {b : Nat}
    {vb : VBlock} {k : Nat} {i : MInst} (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) :
    ctlInstOk b k i = true := by
  unfold ctlCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.1 (vb, b) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hvb))
  simp only [List.all_eq_true] at this
  exact this (i, k) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hi))

theorem immOkB_of {vc : VCode} (h : immsOkB vc = true) {b : Nat} {vb : VBlock} {k : Nat} {i : MInst}
    (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) : immOkB i = true :=
  (array_all_iff _ _).1 ((array_all_iff _ _).1 h b vb hvb) k i hi

/-- The code of one item expands to encodable lines. -/
theorem item_enc {cx c : FnCtx} {af : AFunc} {vc : VCode} {rf : RFunc} {cc : CheckCtx} {b : Nat}
    {vb : VBlock} {it : RItem} {c1 : List AInst}
    (hcov : FormsCovered cx vc) (himm : immsOkB vc = true) (hctl : ctlCheck vc rf = true)
    (hvb : vc.blocks[b]? = some vb) (hchk : ItemChk cc vb it)
    (hc : itemCode (RAFrame.compute vc rf) vb it = .ok c1) : ∀ a ∈ c1, AEnc c af a := by
  cases it with
  | move src dst =>
    obtain ⟨w, hw⟩ := hchk
    have hm := itemCode_move_ok hc
    intro a ha
    cases a with
    | inst m => exact moveInsts_enc hw hm m ha
    | prologue => exact aEnc_prologue c af
    | epilogueRet => exact aEnc_epilogue c af
  | op k allocs =>
    obtain ⟨regs, i, i', rfl, hi, hasg, hcases⟩ := itemCode_op hc
    obtain ⟨w, ops, hops, hst⟩ := hchk i hi
    have hal := allocOk_of_checkStatic hst
    have hL : LinesEnc c i' := by
      have him := immOkB_of himm hvb hi
      cases hct : i.isCtl
      · have hf := (hcov b vb k i hvb hi).resolve_left (by simp [hct])
        exact formOk_enc hf him hops hal hasg
      · exact ctl_enc hct (ctlInstOk_of_ctlCheck hctl hvb hi) him hops hal hasg
    intro a ha
    rcases hcases with ⟨rfl, -, -⟩ | ⟨_, -, rfl⟩ | ⟨_, -, rfl⟩
    · simp only [List.mem_singleton] at ha
      subst ha
      exact hL
    · cases ha
    · simp only [List.mem_singleton] at ha
      subst ha
      exact aEnc_epilogue c af

/-! ## The theorems -/

/-- **Every emitted instruction is encodable** (apart from its label operand), for any
allocation with verified in-states, on a VCode whose instructions are covered forms
(`FormsCovered`) with encodable immediates (`immsOkB`). -/
theorem emitFunc_encodable_of {cx : FnCtx} {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat}
    {fa : FnAsm} (hchk : AllocChecked vc rf) (hcov : FormsCovered cx vc) (himm : immsOkB vc = true)
    (ha : lowerRFunc vc rf = .ok af) (he : emitFunc k af = .ok fa) :
    ∀ i t, Line.ins i t ∈ fa.lines.toList → i.encodable = true := by
  obtain ⟨body, ps, hb, hL, -⟩ := emitFunc_ok he
  obtain ⟨⟨-, -, hsz, hblk⟩, -, hctl⟩ := lowerRFunc_ok ha
  obtain ⟨cc, hitems⟩ := allocChecked_items hchk
  have hA : ∀ x ∈ af.blocks.toList, ∀ a ∈ x.2.toList, AEnc ⟨k, af.slotBase⟩ af a := by
    intro x hx a hax
    obtain ⟨b, hbx⟩ := List.mem_iff_getElem?.mp hx
    rw [Array.getElem?_toList] at hbx
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hbx
    rw [hsz, Array.size_zip] at hlt
    obtain ⟨vb, hvb⟩ : ∃ vb, vc.blocks[b]? = some vb := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨items, hit⟩ : ∃ items, rf.blocks[b]? = some items :=
      ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨code, hcode, hab⟩ := hblk b vb items hvb hit
    rw [hab] at hbx
    cases hbx
    simp only [List.toList_toArray, List.mem_append] at hax
    rcases hax with hax | hax
    · split at hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact aEnc_prologue _ af
      · cases hax
    · obtain ⟨it, hit', c1, hc1, hac⟩ := mem_itemsCode hcode hax
      exact item_enc hcov himm hctl hvb (hitems b vb items hvb hit it hit') hc1 a hac
  rw [hL]
  exact relaxLines_enc _ (allEnc_append (ftList_enc _ _ (Nat.le_refl _) (blocksLinesE_enc hA hb))
    (trapLines_enc _))

/-- **Every instruction of the emitted spill allocation is encodable** (V6b, `Insn.encodable`:
apart from its label operand), for in-scope input whose prepared VCode has encodable immediates
(`immsOkB`, decided by `lean-e2e-check`). -/
theorem emitFunc_spill_encodable {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {k : Nat} {fa : FnAsm}
    (hsub : InSubset p f) (hd : Driver.dominatedB f = true) (hs : Driver.lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (himm : immsOkB vcp = true)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) (he : emitFunc k af = .ok fa) :
    ∀ i t, Line.ins i t ∈ fa.lines.toList → i.encodable = true :=
  emitFunc_encodable_of
    (spillAccepted p f vc vcp hsub (Spill.arityOk_of har) (Driver.dominated_of hd)
      (Driver.lowerScope_of hs) hl hp)
    (Driver.formsCovered_completeB hs hl hp default) himm ha he

end E2E

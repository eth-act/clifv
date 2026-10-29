import FV.Concurrency.VCodeThread
import FV.Backend.Proof.AssignOk

/-!
# The kinds of the memory events of VCode (T2h, #311, layer 1b)

`VCodeThread.cEvs` gives the memory events of a VCode instruction under `csem` (the events of its
canonical run, `ArmInstFoot.instEvs` of each Arm instruction). This file shows they have the kinds
of Cranelift's mapping table `Code.akinds` (`docs/plans/atomics.md` §3e):

* `instEvs_kinds`: an emitted `Insn`'s events have its kind `Code.insnKind` (at most one event;
  none for an instruction without memory kind, `instEvs_none`). Through the encoder's field values
  (`Insn.armFields`): the kind of an Arm instruction's event is a function of its fields
  (`aiKind`, `aiKind_instEvs`), and the fields the encoder chooses give `insnKind`
  (`aiKind_armFields`);
* `linesEvs_kinds`: a straight-line run's event kinds are a sublist of its lines' kinds
  (`Code.kinds`; a run that stops early has fewer events);
* `cEvs_kinds`: **a VCode instruction's event kinds under `csem` are a sublist of `akinds`**
  (`Code.lines_kinds`; the LL/SC loops' body `[acqXR, relXW]`, a failed comparison of the
  `atomic_cas` loop only its `acqXR`); `cEvs_nil`: an instruction without memory kinds (every
  instruction but loads, stores, the atomics and `fence`, under `csem`) has no events.
-/

namespace Concurrency.VCodeEvents

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread Code
open scoped List

/-! ## Instructions without memory events -/

/-- The classes with memory events (loads/stores and barriers). -/
def memCls : ArmInst → Bool
  | .LDST _ => true
  | .BR (.Barrier _) => true
  | _ => false

theorem memCls_norm (a : ArmInst) : memCls a.norm = memCls a := by
  cases a with
  | LDST i => cases i <;> rfl
  | BR i => cases i <;> rfl
  | DPI i => cases i <;> rfl
  | DPR i => cases i <;> rfl
  | DPSFP i => cases i <;> rfl
  | RES i => cases i <;> rfl

theorem instEvs_of_memCls {a : ArmInst} (h : memCls a = false) (s : ArmState) : instEvs a s = [] := by
  cases a with
  | LDST i => cases h
  | BR i => cases i <;> first | rfl | cases h
  | _ => rfl

set_option maxHeartbeats 4000000 in
theorem memCls_armFields (env : Env) (i : Insn) (a : ArmInst) (h : i.armFields env = .ok a)
    (hk : insnKind i = none) : memCls a = false := by
  cases i <;> simp only [insnKind, reduceCtorEq] at hk <;>
    simp only [Insn.armFields, bind, Except.bind, pure, Except.pure] at h <;>
    (repeat' split at h) <;> (try cases h) <;> rfl

/-- **An instruction without memory kind has no events.** -/
theorem instEvs_none {env : Env} {i : Insn} {ai : ArmInst} (h : i.toArmInst env = .ok ai)
    (hk : insnKind i = none) (s : ArmState) : instEvs ai s = [] := by
  unfold Insn.toArmInst at h
  cases ha : i.armFields env with
  | error e => rw [ha] at h; cases h
  | ok a =>
    rw [ha] at h
    simp only [Functor.map, Except.map] at h
    cases h
    exact instEvs_of_memCls (by rw [memCls_norm]; exact memCls_armFields env i a ha hk) s

/-! ## The kind of an instruction's event, from its fields -/

/-- The kind of a single-register load/store's access (`exec_reg_imm_common`'s `memop`). -/
def immK (simd : Bool) (opc : BitVec 2) : AKind :=
  if (if ¬ simd = true ∧ BitVec.lsb opc 1 = 1#1 then 1#1 else BitVec.lsb opc 0) = 0#1 then .plainW
  else .plainR

/-- The kind of every event of an Arm instruction (`none`: it has none). -/
def aiKind : ArmInst → Option AKind
  | .LDST (.Reg_imm_post_indexed i) => some (immK (decide (i.V = 1#1)) i.opc)
  | .LDST (.Reg_unsigned_imm i) => some (immK (decide (i.V = 1#1)) i.opc)
  | .LDST (.Reg_unscaled_imm i) => some (immK (decide (i.VR = 1#1)) i.opc)
  | .LDST (.Reg_pair_pre_indexed i) => some (if i.L = 1#1 then .plainR else .plainW)
  | .LDST (.Reg_pair_post_indexed i) => some (if i.L = 1#1 then .plainR else .plainW)
  | .LDST (.Reg_pair_signed_offset i) => some (if i.L = 1#1 then .plainR else .plainW)
  | .LDST (.Reg_imm_pre_indexed i) => some (immK (decide (i.V = 1#1)) i.opc)
  | .LDST (.Reg_reg_offset i) => some (immK (decide (i.V = 1#1)) i.opc)
  | .LDST (.Reg_exclusive i) => some (exclKind i)
  | .LDST (.Reg_literal _) => some .plainR
  | .BR (.Barrier _) => some .dmb
  | _ => none

/-- All events have kind `K`. -/
def AllK (K : AKind) (evs : List Ev) : Prop := ∀ e ∈ evs, e.k = K

theorem allk_nil (K : AKind) : AllK K [] := fun _ h => absurd h List.not_mem_nil

theorem allk_ite {K : AKind} {c : Prop} [Decidable c] {a b : List Ev} (ha : c → AllK K a)
    (hb : ¬ c → AllK K b) : AllK K (if c then a else b) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact ha h
  · rw [ite_eq_right h]; exact hb h

theorem allk_one {K : AKind} {e : Ev} (h : e.k = K) : AllK K [e] := by
  intro e' he'; simp only [List.mem_singleton] at he'; subst he'; exact h

theorem immEvs_kind (inst : LDST.Reg_imm_cls) (s : ArmState) :
    AllK (immK inst.SIMD? inst.opc) (immEvs inst s) := by
  unfold immEvs
  dsimp only
  repeat' (first | exact allk_nil _ | (apply allk_ite <;> intro h))
  all_goals first
    | exact allk_one (ite_eq_left h).symm
    | exact allk_one (ite_eq_right h).symm

theorem immK_true (opc : BitVec 2) :
    immK true opc = if BitVec.getLsbD opc 0 = true then .plainR else .plainW := by
  have hopc : opc = 0#2 ∨ opc = 1#2 ∨ opc = 2#2 ∨ opc = 3#2 := by bv_omega
  rcases hopc with rfl | rfl | rfl | rfl <;> decide

theorem ldsturEvs_kind (inst : Reg_unscaled_imm_cls) (s : ArmState) :
    AllK (immK true inst.opc) (ldsturEvs inst s) := by
  unfold ldsturEvs
  dsimp only
  rw [immK_true]
  repeat' (first | exact allk_nil _ | (apply allk_ite <;> intro h))
  all_goals first
    | exact allk_one (ite_eq_left h).symm
    | exact allk_one (ite_eq_right h).symm

theorem pairEvs_kind (inst : LDST.Reg_pair_cls) (s : ArmState) :
    AllK (if inst.L? then .plainR else .plainW) (pairEvs inst s) := by
  unfold pairEvs
  dsimp only
  repeat' (first | exact allk_nil _ | (apply allk_ite <;> intro h))
  cases hL : inst.L? <;> exact allk_one rfl

theorem exclEvs_kind (inst : Reg_exclusive_cls) (s : ArmState) :
    AllK (exclKind inst) (exclEvs inst s) := by
  unfold exclEvs
  repeat' (first | exact allk_nil _ | exact allk_one rfl | (apply allk_ite <;> intro h))

theorem literalEvs_kind (inst : Reg_literal_cls) (s : ArmState) :
    AllK .plainR (literalEvs inst s) := by
  unfold literalEvs litEv
  repeat' (first | exact allk_nil _ | exact allk_one rfl | (apply allk_ite <;> intro h))

/-- **Every event of an instruction has the kind its fields give** (`aiKind`). -/
theorem aiKind_instEvs (ai : ArmInst) (s : ArmState) : ∀ e ∈ instEvs ai s, aiKind ai = some e.k := by
  intro e he
  cases ai with
  | LDST i =>
    cases i with
    | Reg_imm_post_indexed i => simp only [aiKind, immEvs_kind _ s e he]
    | Reg_unsigned_imm i => simp only [aiKind, immEvs_kind _ s e he]
    | Reg_imm_pre_indexed i => simp only [aiKind, immEvs_kind _ s e he]
    | Reg_unscaled_imm i =>
      simp only [instEvs] at he
      by_cases hv : i.VR = 1#1
      · rw [ite_eq_left hv] at he
        simp only [aiKind, ldsturEvs_kind _ s e he, hv, decide_true]
      · rw [ite_eq_right hv] at he
        simp only [aiKind, immEvs_kind _ s e he, hv, decide_false]
    | Reg_reg_offset i =>
      simp only [instEvs] at he
      split at he
      · exact absurd he List.not_mem_nil
      · simp only [aiKind, immEvs_kind _ s e he]
    | Reg_pair_pre_indexed i | Reg_pair_post_indexed i | Reg_pair_signed_offset i =>
      simp only [instEvs] at he
      rw [pairEvs_kind _ s e he]
      by_cases hL : i.L = 1#1 <;> simp [aiKind, hL]
    | Reg_exclusive i => simp only [aiKind, exclEvs_kind _ s e he]
    | Reg_literal i => simp only [aiKind, literalEvs_kind _ s e he]
  | BR i =>
    cases i with
    | Barrier i =>
      simp only [instEvs] at he
      split at he
      · simp only [List.mem_singleton] at he; subst he; rfl
      · exact absurd he List.not_mem_nil
    | _ => exact absurd he List.not_mem_nil
  | _ => exact absurd he List.not_mem_nil

theorem aiKind_norm (a : ArmInst) : aiKind a.norm = aiKind a := by
  cases a with
  | LDST i => cases i <;> rfl
  | BR i => cases i <;> rfl
  | DPI i => cases i <;> rfl
  | DPR i => cases i <;> rfl
  | DPSFP i => cases i <;> rfl
  | RES i => cases i <;> rfl

theorem ldstFields_kind {size : BitVec 2} {V : BitVec 1} {opc : BitVec 2} {bytes : Nat}
    {Rt : BitVec 5} {m : AMode} {a : ArmInst} (h : ldstFields size V opc bytes Rt m = .ok a) :
    aiKind a = some (immK (decide (V = 1#1)) opc) := by
  unfold ldstFields at h
  cases m <;> simp only [bind, Except.bind, pure, Except.pure] at h <;>
    (repeat' split at h) <;> (try cases h) <;> rfl

theorem ldstFields_bind_kind {x : Except String (BitVec 5)} {size : BitVec 2} {V : BitVec 1}
    {opc : BitVec 2} {bytes : Nat} {m : AMode} {a : ArmInst}
    (h : (x >>= fun Rt => ldstFields size V opc bytes Rt m) = .ok a) :
    aiKind a = some (immK (decide (V = 1#1)) opc) := by
  cases x with
  | error e => simp only [bind, Except.bind] at h; cases h
  | ok Rt => simp only [bind, Except.bind] at h; exact ldstFields_kind h

theorem ldstFields_bind2_kind {y : Except String (BitVec 2)} {x : Except String (BitVec 5)}
    {V : BitVec 1} {opc : BitVec 2} {bytes : Nat} {m : AMode} {a : ArmInst}
    (h : (y >>= fun size => x >>= fun Rt => ldstFields size V opc bytes Rt m) = .ok a) :
    aiKind a = some (immK (decide (V = 1#1)) opc) := by
  cases y with
  | error e => simp only [bind, Except.bind] at h; cases h
  | ok size => simp only [bind, Except.bind] at h; exact ldstFields_bind_kind h

/-- The kind of `ldr x, [x, #0]` (the GOT and TLS-descriptor loads). -/
theorem immK_ldr : immK (decide ((0 : BitVec 1) = 1#1)) (1 : BitVec 2) = .plainR := by decide

set_option maxHeartbeats 4000000 in
/-- **The encoder's fields give the instruction's kind.** -/
theorem aiKind_armFields {env : Env} {i : Insn} {a : ArmInst} (h : i.armFields env = .ok a)
    {k : AKind} (hk : insnKind i = some k) : aiKind a = some k := by
  cases i <;> simp only [insnKind, reduceCtorEq, Option.some.injEq] at hk <;> subst hk
  case load op rt m =>
    cases op <;> simp only [Insn.armFields, LoadOp.fields] at h <;>
      exact (ldstFields_bind_kind h).trans (by decide)
  case store op rt m =>
    cases op <;> simp only [Insn.armFields, StoreOp.fields] at h <;>
      exact (ldstFields_bind_kind h).trans (by decide)
  case fpuLoad s rt m =>
    simp only [Insn.armFields] at h
    exact (ldstFields_bind2_kind h).trans (by decide)
  case fpuStore s rt m =>
    simp only [Insn.armFields] at h
    exact (ldstFields_bind2_kind h).trans (by decide)
  all_goals
    simp only [Insn.armFields, Insn.armFields.exclFields, bind, Except.bind, pure,
      Except.pure] at h
    (repeat' split at h) <;> (try cases h) <;> first | rfl | (simp only [aiKind, immK_ldr])

/-- **The events of an emitted instruction have its kind** (`Code.insnKind`; at most one). -/
theorem instEvs_kinds {env : Env} {i : Insn} {ai : ArmInst} (h : i.toArmInst env = .ok ai)
    (s : ArmState) : (instEvs ai s).map (·.k) <+ (insnKind i).toList := by
  rcases hk : insnKind i with _ | k
  · rw [instEvs_none h hk]; exact List.nil_sublist _
  · unfold Insn.toArmInst at h
    cases ha : i.armFields env with
    | error e => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      simp only [Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have hK : ∀ e ∈ instEvs a.norm s, e.k = k := fun e he => by
        have := aiKind_instEvs a.norm s e he
        rw [aiKind_norm, aiKind_armFields ha hk, Option.some.injEq] at this
        exact this.symm
      have hl := len_instEvs a.norm s
      generalize instEvs a.norm s = evs at hK hl
      match evs, hl with
      | [], _ => exact List.nil_sublist _
      | [e], _ =>
        simp only [List.map_cons, List.map_nil, Option.toList_some]
        rw [hK e List.mem_cons_self]
        exact List.Sublist.refl _

/-! ## The events of straight-line code and of VCode instructions -/

theorem kinds_ins (i : Insn) (t : Option Clif.TrapCode) (ls : List Line) :
    kinds (.ins i t :: ls) = (insnKind i).toList ++ kinds ls := by
  rcases h : insnKind i with _ | k <;> simp [kinds, lineKind, h]

/-- **A straight-line run's event kinds are a sublist of its lines' kinds.** -/
theorem linesEvs_kinds : ∀ (env : Env) (ls : List Line) (s : ArmState),
    (linesEvs env ls s).map (·.k) <+ kinds ls
  | _, [], _ => List.nil_sublist _
  | env, .ins i t :: ls, s => by
    rw [kinds_ins]
    simp only [linesEvs]
    cases ha : i.toArmInst env with
    | error e => exact List.nil_sublist _
    | ok ai =>
      simp only
      split
      · rw [List.map_append]
        exact (instEvs_kinds ha s).append (linesEvs_kinds _ ls _)
      · exact (instEvs_kinds ha s).trans (List.sublist_append_left _ _)
  | _, .label _ :: _, _ => List.nil_sublist _
  | _, .word _ _ :: _, _ => List.nil_sublist _
  | _, .data _ :: _, _ => List.nil_sublist _

/-- Every successful run of `x` ends with a value meeting `P`. -/
def PutPost {α : Type} (x : StateT Nat (Except String) α) (P : α → Prop) : Prop :=
  ∀ s r s', x.run s = .ok (r, s') → P r

theorem visit_akinds {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : OpSpec → Reg → m Reg) (i : MInst) :
    akinds <$> MInst.visitOperands f i = (fun _ => akinds i) <$> MInst.visitOperands f i := by
  cases i
  case condBr a b k =>
    cases k <;> simp [MInst.visitOperands, CondBrKind.visit, akinds]
  case trapIf k c =>
    cases k <;> simp [MInst.visitOperands, CondBrKind.visit, akinds]
  case call info =>
    rcases info with ⟨dest, us, ds⟩
    cases dest <;> simp [MInst.visitOperands, akinds]
  case tryCall info ti =>
    rcases info with ⟨dest, us, ds⟩
    cases dest <;> simp [MInst.visitOperands, akinds]
  all_goals simp [MInst.visitOperands, akinds]

/-- **Substituting an allocation keeps the kinds.** -/
theorem akinds_assign {i i' : MInst} {regs : Array Reg} (h : i.assign regs = .ok i') :
    akinds i' = akinds i := by
  rw [assign_eq] at h
  have e := congrArg (fun x => StateT.run x 0) (visit_akinds (putOp regs) i)
  simp only [StateT.run_map] at e
  cases hr : (MInst.visitOperands (putOp regs) i).run 0 with
  | error err => simp [hr, bind, Except.bind] at h
  | ok p =>
    rw [hr] at e h
    simp only [bind, Except.bind] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa [Functor.map, Except.map] using e

theorem straightEvs_kinds (ctx : FnCtx) (i : MInst) (uses : List CV) (w : ArmState) :
    (straightEvs ctx i uses w).map (·.k) <+ akinds i := by
  unfold straightEvs
  split
  · split
    · rename_i ic hic
      split
      · rename_i ls ps hls
        rw [← akinds_assign hic, ← lines_kinds ctx ic {} hls]
        exact linesEvs_kinds _ _ _
      · exact List.nil_sublist _
    · exact List.nil_sublist _
  · exact List.nil_sublist _

theorem kinds_rmwLoopBody (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    kinds (rmwLoopBody bits op fl) = [.acqXR, .relXW] := by
  unfold rmwLoopBody
  rw [kinds_append, kinds_append, kinds_rmwLoopMid]
  rfl

theorem kinds_casLoopHead (bits : Nat) (fl : Clif.MemFlags) :
    kinds (casLoopHead bits fl) = [.acqXR] := by
  simp only [casLoopHead, kinds, List.filterMap_cons, List.filterMap_nil, lineKind,
    insnKind_casLoopCmp]
  rfl

theorem kinds_casStore (bits : Nat) (fl : Clif.MemFlags) : kinds (casStore bits fl) = [.relXW] :=
  rfl

theorem loopEvs_kinds (body : List Line) (regs : List Reg) (uses : List CV) (w : ArmState) :
    (loopEvs body regs uses w).map (·.k) <+ kinds body :=
  linesEvs_kinds _ _ _

theorem casEvs_kinds (F : BitVec 64 → Prop) (ty : CTy) (fl : Clif.MemFlags) (u e x : CV)
    (w : ArmState) : (casEvs F ty fl u e x w).map (·.k) <+ [.acqXR, .relXW] := by
  have hh := loopEvs_kinds (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x] w
  rw [kinds_casLoopHead] at hh
  have hh' : (loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x] w).map (·.k) <+
      [.acqXR, .relXW] :=
    hh.trans (List.sublist_append_left ([.acqXR] : List AKind) [.relXW])
  unfold casEvs
  cases loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x] [.x 27, .x 24] w with
  | none => exact hh'
  | some r =>
    obtain ⟨outs, t1, c⟩ := r
    simp only
    split
    · exact hh'
    · rw [List.map_append]
      have hs := loopEvs_kinds (casStore ty.bits fl) [] [] t1
      rw [kinds_casStore] at hs
      exact hh.append hs

/-- **The event kinds of a VCode instruction under `csem` are a sublist of its kinds in
Cranelift's mapping table** (`Code.akinds`). -/
theorem cEvs_kinds (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (uses : List CV)
    (w : ArmState) : (cEvs F ctx i uses w).map (·.k) <+ akinds i := by
  unfold cEvs
  split
  · split
    · refine (loopEvs_kinds _ _ _ _).trans ?_
      rw [kinds_rmwLoopBody]
      exact List.Sublist.refl _
    · exact casEvs_kinds _ _ _ _ _ _ _
    · exact List.nil_sublist _
  · exact straightEvs_kinds ctx i uses w

/-- **Instructions without memory kinds have no events** under `csem`. -/
theorem cEvs_nil {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} (h : akinds i = [])
    (uses : List CV) (w : ArmState) : cEvs F ctx i uses w = [] := by
  have := cEvs_kinds F ctx i uses w
  rw [h, List.sublist_nil, List.map_eq_nil_iff] at this
  exact this

end Concurrency.VCodeEvents

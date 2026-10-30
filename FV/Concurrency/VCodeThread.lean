import FV.Concurrency.ArmInstFoot
import FV.Backend.Proof.RegallocCSem

/-!
# Event semantics of VCode (T2h, #311, layer 1)

The VCode semantics (`Backend.Proof.VStep`) is parametric in an instruction semantics whose world
is an Arm state; the backend's is `csem F ctx X` (`FV/Backend/Proof/RegallocCSem.lean`): a
straight-line instruction is the Arm run of its canonical allocation (`straightSem`), an LL/SC
loop its body run once (`loopSem`), the control forms explicit. This file gives VCode memory
events, the first layer of the discharge of `ProgE2E.Realizes` (`docs/plans/atomics.md` §3e):

* **precise footprints**, sequential: `SAgrees m evs` (each read event holds the bytes of `m`
  after the step's earlier writes), `SFoot`/`OFoot` (a total/partial step reads `s`'s memory
  through its read events and, on every memory holding their bytes, writes exactly its write
  events), `ofoot_seq` (they compose), `sfoot_exec_inst` (every Arm instruction, from
  `ArmInstFoot.footprint_exec_inst`), `ofoot_execLines` (a straight-line run: the events of its
  instructions in order, `linesEvs`);
* **the footprint of a VCode instruction** `IFoot sem i uses w evs`: `sem`'s outcome on any memory
  holding the read events' bytes is the outcome on `w` with the write events applied to that
  memory. `cEvs F ctx i uses w`: the events of `csem` (the canonical run's, `straightEvs`; the
  loop body's, `loopEvs`/`casEvs`; none for the control forms). `ifoot_csem`: **every
  instruction except calls has its precise footprint** (error-free world; a straight-line form in
  `csem`'s canonical domain, `csemWF`, on an aligned world; the TLSDESC flags independent of
  memory, `TlsMemFree`);
* **the VCode thread semantics** `VTStep vc sem ev`: a step whose events are the instruction's
  precise footprint `ev` on the world patched with the read events' bytes (any bytes: the
  environment's writes, `patch`), and which is the VCode step on that world. `vtstep_sc`: against
  the thread's own memory it is a VCode step; `exists_vtstep`: every VCode step of a covered
  instruction is a thread step with `cEvs`.

Non-vacuity: `FV/Concurrency/VCodeThreadWitness.lean` (an `ldar` reading the environment's `5`
while the thread's memory holds `0`).
-/

namespace Concurrency.VCodeThread

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof

/-! ## Sequential agreement, precise footprints -/

/-- The memory after one event (a write writes). -/
def write1 (m : Memory) (e : Ev) : Memory := if e.k.dir = .W then writeM e.n e.addr e.val m else m

/-- **The events read the memory in order**: each read event holds the bytes of the memory after
the step's earlier writes. -/
def SAgrees : Memory → List Ev → Prop
  | _, [] => True
  | m, e :: es => (e.k.dir = .R → readM e.n e.addr m = e.val) ∧ SAgrees (write1 m e) es

theorem applyW_cons (e : Ev) (es : List Ev) (m : Memory) :
    applyW (e :: es) m = applyW es (write1 m e) := rfl

theorem sagrees_append : ∀ {e1 e2 : List Ev} {m : Memory},
    SAgrees m (e1 ++ e2) ↔ SAgrees m e1 ∧ SAgrees (applyW e1 m) e2
  | [], _, _ => by simp [SAgrees, applyW]
  | e :: e1, e2, m => by
    simp only [List.cons_append, SAgrees, applyW_cons]
    rw [sagrees_append]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

theorem applyW_append : ∀ (e1 e2 : List Ev) (m : Memory),
    applyW (e1 ++ e2) m = applyW e2 (applyW e1 m)
  | [], _, _ => rfl
  | _ :: e1, e2, _ => applyW_append e1 e2 _

/-- For at most one event, sequential and simultaneous agreement coincide. -/
theorem sagrees_iff {evs : List Ev} (h : evs.length ≤ 1) (m : Memory) :
    SAgrees m evs ↔ Agrees evs m := by
  match evs, h with
  | [], _ => exact ⟨fun _ => fun _ h => (nomatch h), fun _ => trivial⟩
  | [e], _ =>
    simp only [SAgrees, and_true]
    exact ⟨fun h e' he' hr => by simp only [List.mem_singleton] at he'; subst he'; exact h hr,
      fun h hr => h e List.mem_cons_self hr⟩

/-- **`f` at `s` has the precise footprint `evs`**: the read events read `s`'s memory (in order),
and on every memory holding the read events' bytes, `f` writes exactly the write events and leaves
the registers of `f s`. -/
def SFoot (f : ArmState → ArmState) (s : ArmState) (evs : List Ev) : Prop :=
  SAgrees s.mem evs ∧ ∀ m, SAgrees m evs → f (setMem m s) = setMem (applyW evs m) (f s)

/-- The same for a partial function. -/
def OFoot (g : ArmState → Option ArmState) (s : ArmState) (evs : List Ev) : Prop :=
  SAgrees s.mem evs ∧ ∀ m, SAgrees m evs → g (setMem m s) = (g s).map (setMem (applyW evs m))

theorem sfoot_mem {f : ArmState → ArmState} {s : ArmState} {evs : List Ev} (h : SFoot f s evs) :
    (f s).mem = applyW evs s.mem := by
  have e := h.2 s.mem h.1
  rw [setMem_self] at e
  rw [e]; rfl

/-- **Sequencing**: precise footprints compose. -/
theorem ofoot_seq {f : ArmState → ArmState} {g : ArmState → Option ArmState} {s : ArmState}
    {e1 e2 : List Ev} (h1 : SFoot f s e1) (h2 : OFoot g (f s) e2) :
    OFoot (fun t => g (f t)) s (e1 ++ e2) := by
  refine ⟨sagrees_append.mpr ⟨h1.1, ?_⟩, fun m hm => ?_⟩
  · rw [← sfoot_mem h1]; exact h2.1
  · obtain ⟨hm1, hm2⟩ := sagrees_append.mp hm
    simp only
    rw [h1.2 m hm1, h2.2 _ hm2, applyW_append]

/-- An instruction's footprint as a precise one (`footprint_exec_inst`). -/
theorem len_ite {c : Prop} [Decidable c] {a b : List Ev} (ha : a.length ≤ 1) (hb : b.length ≤ 1) :
    (if c then a else b).length ≤ 1 := by
  split
  · exact ha
  · exact hb

macro "len_tac" : tactic => `(tactic| ((try dsimp only); repeat (first
  | exact Nat.zero_le 1
  | exact Nat.le_refl 1
  | apply len_ite
  | split)))

theorem len_instEvs (ai : ArmInst) (s : ArmState) : (instEvs ai s).length ≤ 1 := by
  cases ai with
  | LDST i =>
    cases i with
    | Reg_exclusive i => simp only [instEvs]; unfold exclEvs; len_tac
    | Reg_literal i => simp only [instEvs]; unfold literalEvs litEv; len_tac
    | Reg_unscaled_imm i => simp only [instEvs]; unfold ldsturEvs immEvs; len_tac
    | Reg_reg_offset i => simp only [instEvs]; unfold immEvs; len_tac
    | Reg_pair_pre_indexed i | Reg_pair_post_indexed i | Reg_pair_signed_offset i =>
      simp only [instEvs]; unfold pairEvs; len_tac
    | _ => simp only [instEvs]; unfold immEvs; len_tac
  | BR i =>
    cases i with
    | Barrier i => simp only [instEvs]; len_tac
    | _ => exact Nat.zero_le 1
  | _ => exact Nat.zero_le 1

/-! ## The events of a straight-line run (`execLines`) -/

/-- The memory events of `execLines env ls s`, in program order. -/
def linesEvs : Env → List Line → ArmState → List Ev
  | _, [], _ => []
  | env, .ins i _ :: ls, s =>
    match i.toArmInst env with
    | .ok ai =>
      if Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64 then
        instEvs ai s ++ linesEvs { env with pc := env.pc + 4 } ls (Arm.exec_inst ai s)
      else instEvs ai s
    | .error _ => []
  | _, _ :: _, _ => []

theorem agrees_nil (m : Memory) : Agrees [] m := fun _ h => nomatch h

theorem agrees_ite {c : Prop} [Decidable c] {a b : List Ev} {m : Memory} (ha : Agrees a m)
    (hb : Agrees b m) : Agrees (if c then a else b) m := by
  split
  · exact ha
  · exact hb

theorem agrees_read {k : AKind} {a : BitVec 64} {n : Nat} {m : Memory} :
    Agrees [⟨k, a, n, readM n a m⟩] m := by
  intro e he _; simp only [List.mem_singleton] at he; subst he; rfl

theorem agrees_write {k : AKind} (hk : k.dir = .W) {a : BitVec 64} {n : Nat} {v : BitVec (n * 8)}
    {m : Memory} : Agrees [⟨k, a, n, v⟩] m := by
  intro e he hr; simp only [List.mem_singleton] at he; subst he; rw [hk] at hr; cases hr

macro "agree_tac" : tactic => `(tactic| ((try dsimp only); repeat (first
  | exact agrees_nil _
  | exact agrees_read
  | exact agrees_write rfl
  | apply agrees_ite
  | split)))

theorem agrees_instEvs (ai : ArmInst) (s : ArmState) : Agrees (instEvs ai s) s.mem := by
  cases ai with
  | LDST i =>
    cases i with
    | Reg_exclusive i =>
      simp only [instEvs, exclEvs]
      by_cases hL : i.L = 1#1
      · simp only [hL, ite_true]; exact agrees_ite (agrees_nil _) agrees_read
      · simp only [hL, ite_false]; exact agrees_ite (agrees_nil _) (agrees_write (exclKind_W hL))
    | Reg_literal i => simp only [instEvs]; unfold literalEvs litEv; agree_tac
    | Reg_unscaled_imm i =>
      simp only [instEvs]; unfold ldsturEvs immEvs; agree_tac
    | Reg_reg_offset i => simp only [instEvs]; unfold immEvs; agree_tac
    | Reg_pair_pre_indexed i | Reg_pair_post_indexed i | Reg_pair_signed_offset i =>
      simp only [instEvs]; unfold pairEvs; agree_tac
    | _ => simp only [instEvs]; unfold immEvs; agree_tac
  | BR i =>
    cases i with
    | Barrier i =>
      simp only [instEvs]
      refine agrees_ite (fun e he hr => ?_) (agrees_nil _)
      simp only [List.mem_singleton] at he; subst he; cases hr
    | _ => exact agrees_nil _
  | _ => exact agrees_nil _

/-- **Every instruction has a precise footprint.** -/
theorem sfoot_exec_inst (ai : ArmInst) (s : ArmState) : SFoot (exec_inst ai) s (instEvs ai s) := by
  have hl := len_instEvs ai s
  refine ⟨(sagrees_iff hl _).mpr (agrees_instEvs ai s), fun m hm => ?_⟩
  have e := footprint_exec_inst ai s m ((sagrees_iff hl _).mp hm)
  rwa [applyR_of_agrees (agrees_instEvs ai s), setMem_self] at e


theorem ofoot_none (s : ArmState) : OFoot (fun _ => none) s [] :=
  ⟨trivial, fun _ _ => rfl⟩

theorem pc_exec_setMem {ai : ArmInst} {s : ArmState} (m : Memory) (h : SFoot (exec_inst ai) s
    (instEvs ai s)) (hm : SAgrees m (instEvs ai s)) :
    Arm.r .PC (exec_inst ai (setMem m s)) = Arm.r .PC (exec_inst ai s) := by
  rw [h.2 m hm, r_setMem]

/-- **A straight-line run has a precise footprint**: the events of its instructions, in order. -/
theorem ofoot_execLines : ∀ (env : Env) (ls : List Line) (s : ArmState),
    OFoot (execLines env ls) s (linesEvs env ls s)
  | _, [], s => ⟨trivial, fun m _ => by simp only [execLines, linesEvs, applyW, Option.map_some]⟩
  | env, .ins i t :: ls, s => by
    simp only [linesEvs]
    cases ha : i.toArmInst env with
    | error e =>
      refine ⟨trivial, fun m _ => ?_⟩
      simp only [execLines, ha, Option.map_none]
    | ok ai =>
      simp only
      have hf := sfoot_exec_inst ai s
      by_cases hpc : Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64
      · simp only [hpc, ite_true]
        have hseq := ofoot_seq hf (ofoot_execLines { env with pc := env.pc + 4 } ls (exec_inst ai s))
        refine ⟨hseq.1, fun m hm => ?_⟩
        have e1 : execLines env (.ins i t :: ls) (setMem m s) =
            execLines { env with pc := env.pc + 4 } ls (exec_inst ai (setMem m s)) := by
          simp only [execLines, ha]
          rw [pc_exec_setMem m hf (sagrees_append.mp hm).1, r_setMem, hpc]; simp only [ite_true]
        have e2 : execLines env (.ins i t :: ls) s =
            execLines { env with pc := env.pc + 4 } ls (exec_inst ai s) := by
          simp only [execLines, ha, hpc, ite_true]
        rw [e1, e2]
        exact hseq.2 m hm
      · simp only [hpc, ite_false]
        refine ⟨hf.1, fun m hm => ?_⟩
        have e1 : execLines env (.ins i t :: ls) (setMem m s) = none := by
          simp only [execLines, ha]
          rw [pc_exec_setMem m hf hm, r_setMem, ite_eq_right hpc]
        have e2 : execLines env (.ins i t :: ls) s = none := by
          simp only [execLines, ha, ite_eq_right hpc]
        rw [e1, e2]; rfl
  | _, .label _ :: _, _ => ⟨trivial, fun _ _ => rfl⟩
  | _, .word _ _ :: _, _ => ⟨trivial, fun _ _ => rfl⟩

/-! ## Register-only accessors -/

theorem setReg_setMem (s : ArmState) (m : Memory) (r : Reg) (v : CV) :
    setReg (setMem m s) r v = setMem m (setReg s r v) := by
  cases r <;> simp only [setReg, w_setMem]

theorem foldl_setReg_setMem : ∀ (ps : List (Reg × CV)) (s : ArmState) (m : Memory),
    ps.foldl (fun s p => setReg s p.1 p.2) (setMem m s) =
      setMem m (ps.foldl (fun s p => setReg s p.1 p.2) s)
  | [], _, _ => rfl
  | p :: ps, s, m => by
    simp only [List.foldl_cons]
    rw [setReg_setMem, foldl_setReg_setMem ps]

theorem placeUses_setMem (ops : Array Operand) (regs : Array Reg) (uses : List CV) (w : ArmState)
    (m : Memory) : placeUses ops regs uses (setMem m w) = setMem m (placeUses ops regs uses w) :=
  foldl_setReg_setMem _ w m

theorem regVal_setMem (s : ArmState) (m : Memory) (r : Reg) : regVal (setMem m s) r = regVal s r := by
  cases r <;> simp only [regVal, r_setMem]

theorem regVal_setMem' (s : ArmState) (m : Memory) : regVal (setMem m s) = regVal s :=
  funext (regVal_setMem s m)

theorem regX_setMem (s : ArmState) (m : Memory) (r : Reg) : regX (setMem m s) r = regX s r := by
  cases r <;> simp only [regX, spOf, r_setMem]

theorem addr_setMem (ctx : FnCtx) (am : AMode) (n : Nat) (s : ArmState) (m : Memory) :
    am.addr ctx n (setMem m s) = am.addr ctx n s := by
  cases am <;> simp only [AMode.addr, regX_setMem, spOf, r_setMem]

theorem accesses_setMem (ctx : FnCtx) (i : MInst) (s : ArmState) (m : Memory) :
    i.accesses ctx (setMem m s) = i.accesses ctx s := by
  cases i <;> simp only [MInst.accesses, addr_setMem, regX_setMem]

theorem accessOk_setMem (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (s : ArmState)
    (m : Memory) : AccessOk F ctx i (setMem m s) ↔ AccessOk F ctx i s := by
  simp only [AccessOk, accesses_setMem]

theorem defVals_setMem (ops : Array Operand) (regs : Array Reg) (s : ArmState) (m : Memory) :
    defVals ops regs (setMem m s) = defVals ops regs s := by
  simp only [defVals, regVal_setMem]

theorem readFlag_setMem (f : PFlag) (s : ArmState) (m : Memory) :
    read_flag f (setMem m s) = read_flag f s := by simp only [read_flag, r_setMem]

theorem condHolds_setMem (c : BitVec 4) (s : ArmState) (m : Memory) :
    Arm.ConditionHolds c (setMem m s) = Arm.ConditionHolds c s := by
  unfold Arm.ConditionHolds; simp only [readFlag_setMem]

theorem holds_setMem (k : CondBrKind) (uses : List CV) (w : ArmState) (m : Memory) :
    k.holds uses (setMem m w) = k.holds uses w := by
  unfold CondBrKind.holds; split <;> simp only [condHolds_setMem]

theorem spAlign_setMem (s : ArmState) (m : Memory) :
    Arm.CheckSPAlignment (setMem m s) = Arm.CheckSPAlignment s := check_sp_sm' m s

theorem err_setMem (s : ArmState) (m : Memory) : Arm.r .ERR (setMem m s) = Arm.r .ERR s :=
  r_setMem _ m s

/-! ## The footprint of an instruction of VCode -/

/-- **The precise footprint of instruction `i` with use values `uses` at world `w`** under the
instruction semantics `sem`: the read events read `w`'s memory (in order), and on every memory
holding the read events' bytes, `sem` has the same outcome except that the world's memory is the
memory with the write events applied. -/
def IFoot (sem : ISem CV ArmState) (i : MInst) (uses : List CV) (w : ArmState) (evs : List Ev) :
    Prop :=
  SAgrees w.mem evs ∧ ∀ m, SAgrees m evs →
    sem i uses (setMem m w) = (sem i uses w).map fun r => (r.1, setMem (applyW evs m) r.2.1, r.2.2)

/-- No event, the semantics does not look at memory. -/
theorem ifoot_nil {sem : ISem CV ArmState} {i : MInst} {uses : List CV} {w : ArmState}
    (h : ∀ m, sem i uses (setMem m w) =
      (sem i uses w).map fun r => (r.1, setMem m r.2.1, r.2.2)) : IFoot sem i uses w [] :=
  ⟨trivial, fun m _ => h m⟩

/-- The events of `loopSem`'s run. -/
def loopEvs (body : List Line) (regs : List Reg) (uses : List CV) (w : ArmState) : List Ev :=
  linesEvs env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w)

theorem loopSem_foot {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line} {regs : List Reg}
    {uses : List CV} {defs : List Reg} {w : ArmState} (m : Memory)
    (hm : SAgrees m (loopEvs body regs uses w)) :
    loopSem F ty a body regs uses defs (setMem m w) = (loopSem F ty a body regs uses defs w).map
      fun r => (r.1, setMem (applyW (loopEvs body regs uses w) m) r.2.1, r.2.2) := by
  unfold loopSem
  unfold loopEvs at hm ⊢
  by_cases hc : AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧ Arm.r .ERR w = .None
  · rw [ite_eq_left (show AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧ Arm.r .ERR (setMem m w) = .None by
      rwa [r_setMem]), ite_eq_left hc]
    rw [foldl_setReg_setMem]
    have hf := ofoot_execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w)
    rw [hf.2 m hm]
    cases execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w) with
    | none => rfl
    | some t' =>
      simp only [Option.map_some]
      split <;> split <;> rename_i h1 h2 <;> simp only [r_setMem, setMem_program] at h1 h2
      · simp only [Option.map_some, regVal_setMem']
      · exact absurd h1 h2
      · exact absurd h2 h1
      · simp only [Option.map_none]
  · rw [ite_eq_right (show ¬ (AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧
      Arm.r .ERR (setMem m w) = .None) by rwa [r_setMem]), ite_eq_right hc]
    rfl

theorem setReg_mem (s : ArmState) (r : Reg) (v : CV) : (setReg s r v).mem = s.mem := by
  cases r <;> simp only [setReg, w_mem]

theorem foldl_setReg_mem : ∀ (ps : List (Reg × CV)) (s : ArmState),
    (ps.foldl (fun s p => setReg s p.1 p.2) s).mem = s.mem
  | [], _ => rfl
  | p :: ps, s => by simp only [List.foldl_cons]; rw [foldl_setReg_mem ps, setReg_mem]

theorem placeUses_mem (ops : Array Operand) (regs : Array Reg) (uses : List CV) (w : ArmState) :
    (placeUses ops regs uses w).mem = w.mem := foldl_setReg_mem _ w

theorem ifoot_loop {body : List Line} {regs : List Reg} {uses : List CV} {w : ArmState} :
    SAgrees w.mem (loopEvs body regs uses w) := by
  have := (ofoot_execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w)).1
  rwa [foldl_setReg_mem] at this

/-- The events of a straight-line instruction: those of its canonical run (`straightSem`). -/
def straightEvs (ctx : FnCtx) (i : MInst) (uses : List CV) (w : ArmState) : List Ev :=
  match i.operands with
  | .ok ops =>
    match i.assign (canonRegs ops) with
    | .ok ic =>
      match ic.lines ctx {} with
      | .ok (ls, _) => linesEvs env0 ls (placeUses ops (canonRegs ops) uses w)
      | .error _ => []
    | .error _ => []
  | .error _ => []

/-- An `if` with any decidability instances, mapped. -/
theorem ite_map {α β : Type} {c c' : Prop} {_ : Decidable c} {_ : Decidable c'} (hc : c ↔ c')
    (f : α → β) {a : Option α} {a' : Option β} (ha : a' = a.map f) :
    (if c then a' else none) = (if c' then a else none).map f := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left (hc.mp h), ha]
  · rw [ite_eq_right h, ite_eq_right (mt hc.mpr h)]; rfl

open Classical in
/-- The tail of `straightSem` after the run. -/
theorem straight_tail {ops : Array Operand} {w t' : ArmState} (m M : Memory) :
    (if Arm.r .ERR (setMem M t') = .None ∧ (setMem M t').program = (setMem m w).program then
      some (defVals ops (canonRegs ops) (setMem M t'), setMem M t', Ctl.next) else none) =
    (if Arm.r .ERR t' = .None ∧ t'.program = w.program then
      some (defVals ops (canonRegs ops) t', t', Ctl.next) else none).map
      fun r => (r.1, setMem M r.2.1, r.2.2) :=
  ite_map (by simp only [r_setMem, setMem_program]) _ (by simp only [Option.map_some, defVals_setMem])

theorem straightSem_foot {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} {uses : List CV}
    {w : ArmState} : IFoot (straightSem F ctx) i uses w (straightEvs ctx i uses w) := by
  unfold straightEvs
  split
  · rename_i ops hops
    split
    · rename_i ic hic
      split
      · rename_i ls ps hls
        have hf := ofoot_execLines env0 ls (placeUses ops (canonRegs ops) uses w)
        refine ⟨by rw [← placeUses_mem ops (canonRegs ops) uses w]; exact hf.1, fun m hm => ?_⟩
        have hx : ∀ t, execMInst ctx env0 ic t = execLines env0 ls t := fun t => by
          simp only [execMInst, hls]
        unfold straightSem
        simp only [hops, hic, hx, placeUses_setMem]
        rw [hf.2 m hm]
        have hacc : AccessOk F ctx ic (placeUses ops (canonRegs ops) uses (setMem m w)) ↔
            AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w) := by
          rw [placeUses_setMem]; exact accessOk_setMem F ctx ic _ m
        refine ite_map hacc _ ?_
        cases execLines env0 ls (placeUses ops (canonRegs ops) uses w) with
        | none => rfl
        | some t' => exact straight_tail m _
      · rename_i e hls
        refine ⟨trivial, fun m _ => ?_⟩
        unfold straightSem
        simp only [hops, hic, execMInst, hls]
        have hacc : AccessOk F ctx ic (placeUses ops (canonRegs ops) uses (setMem m w)) ↔
            AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w) := by
          rw [placeUses_setMem]; exact accessOk_setMem F ctx ic _ m
        exact ite_map hacc _ rfl
    · rename_i e hic
      refine ⟨trivial, fun m _ => ?_⟩
      unfold straightSem; simp only [hops, hic, Option.map_none]
  · rename_i e hops
    refine ⟨trivial, fun m _ => ?_⟩
    unfold straightSem; simp only [hops, Option.map_none]

/-! ## `csem` -/

/-- The `stlxr` line of the `atomic_cas` loop. -/
def casStore (bits : Nat) (fl : Clif.MemFlags) : List Line :=
  [.ins (.stlxr bits (.x 24) (.x 28) (.x 25)) fl.trapCode]

/-- The events of the `atomic_cas` loop's body: the head (`ldaxr; cmp`), then, when the values
are equal, the `stlxr`. -/
noncomputable def casEvs (F : BitVec 64 → Prop) (ty : CTy) (fl : Clif.MemFlags) (u e x : CV)
    (w : ArmState) : List Ev :=
  match loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x] [.x 27, .x 24] w with
  | some (_, t1, _) =>
    if Arm.ConditionHolds Cond.ne.bits t1 then loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
      [u, e, x] w
    else loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x] w ++
      loopEvs (casStore ty.bits fl) [] [] t1
  | none => loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x] w

/-- **The memory events of a VCode instruction under `csem`**: those of its canonical run
(`straightSem`), of the LL/SC loop's body, none for the other control forms. -/
noncomputable def cEvs (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (uses : List CV)
    (w : ArmState) : List Ev :=
  if i.isCtl then
    match i, uses with
    | .atomicRmwLoop ty op fl _ _ _ _ _, [u, x] =>
      loopEvs (rmwLoopBody ty.bits op fl) [.x 25, .x 26] [u, x] w
    | .atomicCasLoop ty fl _ _ _ _ _, [u, e, x] => casEvs F ty fl u e x w
    | _, _ => []
  else straightEvs ctx i uses w

theorem loopSem_mem {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : ArmState} {r : List CV × ArmState × Ctl}
    (h : loopSem F ty a body regs uses defs w = some r) :
    r.2.1.mem = applyW (loopEvs body regs uses w) w.mem := by
  have e := loopSem_foot (F := F) (ty := ty) (a := a) (defs := defs) (body := body) (regs := regs)
    (uses := uses) w.mem ifoot_loop
  rw [setMem_self, h] at e
  simp only [Option.map_some, Option.some.injEq] at e
  rw [e]; rfl

theorem casEvs_foot {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {ty : CTy} {fl : Clif.MemFlags}
    {ra re rx rd rs : Reg} {u e x : CV} {w : ArmState} (he : Arm.r .ERR w = .None) :
    IFoot (csem F ctx X) (.atomicCasLoop ty fl ra re rx rd rs) [u, e, x] w (casEvs F ty fl u e x w) := by
  have hcsem : ∀ m, csem F ctx X (.atomicCasLoop ty fl ra re rx rd rs) [u, e, x] (setMem m w) =
      match loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x] [.x 27, .x 24]
        (setMem m w) with
      | some (outs, t1, _) =>
        if Arm.ConditionHolds Cond.ne.bits t1 then some (outs, t1, .next)
        else loopSem F ty u (casStore ty.bits fl) [] [] [.x 27, .x 24] t1
      | none => none := fun m => by
    simp only [csem, r_setMem, he, ite_true, casStore]
    rfl
  have hcsem0 := hcsem w.mem
  rw [setMem_self] at hcsem0
  unfold casEvs
  generalize hL : loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, e, x]
    [.x 27, .x 24] w = L at hcsem0
  cases L with
  | none =>
    refine ⟨ifoot_loop, fun m hm => ?_⟩
    rw [hcsem, hcsem0, loopSem_foot m hm, hL]; rfl
  | some r =>
    obtain ⟨outs, t1, c⟩ := r
    simp only
    have ht1 := loopSem_mem hL
    simp only at ht1
    by_cases hne : Arm.ConditionHolds Cond.ne.bits t1
    · simp only [hne, ite_true]
      refine ⟨ifoot_loop, fun m hm => ?_⟩
      rw [hcsem, hcsem0, loopSem_foot m hm, hL]
      simp only [Option.map_some, condHolds_setMem, hne, ite_true]
    · simp only [hne]
      refine ⟨sagrees_append.mpr ⟨ifoot_loop, by rw [← ht1]; exact ifoot_loop⟩, fun m hm => ?_⟩
      obtain ⟨hm1, hm2⟩ := sagrees_append.mp hm
      rw [hcsem, hcsem0, loopSem_foot m hm1, hL]
      simp only [Option.map_some, condHolds_setMem, hne, Bool.false_eq_true, ite_false]
      rw [loopSem_foot _ hm2, applyW_append]

theorem rmw_foot {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {ty : CTy} {op : AtomicRmwLoopOp}
    {fl : Clif.MemFlags} {ra rx rd r1 r2 : Reg} {u x : CV} {w : ArmState} (he : Arm.r .ERR w = .None) :
    IFoot (csem F ctx X) (.atomicRmwLoop ty op fl ra rx rd r1 r2) [u, x] w
      (loopEvs (rmwLoopBody ty.bits op fl) [.x 25, .x 26] [u, x] w) := by
  refine ⟨ifoot_loop, fun m hm => ?_⟩
  simp only [csem, r_setMem, he, ite_true]
  exact loopSem_foot m hm

theorem write_pstate_setMem (p : Arm.PState) (s : ArmState) (m : Memory) :
    Arm.write_pstate p (setMem m s) = setMem m (Arm.write_pstate p s) := by
  simp only [Arm.write_pstate, w_setMem]

/-- The memory does not influence the flags the TLSDESC call leaves. -/
def TlsMemFree (X : ExtSem) : Prop := ∀ n m w, X.tlsFlags n (setMem m w) = X.tlsFlags n w

/-- **The control forms without memory access have no event.** -/
theorem ifoot_ctl {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : ArmState} (hX : TlsMemFree X) (hctl : i.isCtl = true)
    (hcall : ∀ info, i ≠ .call info) (htry : ∀ info ti, i ≠ .tryCall info ti)
    (hrmw : ∀ ty op fl a b c d e, i ≠ .atomicRmwLoop ty op fl a b c d e)
    (hcas : ∀ ty fl a b c d e, i ≠ .atomicCasLoop ty fl a b c d e) :
    IFoot (csem F ctx X) i uses w [] := by
  refine ifoot_nil fun m => ?_
  cases i with
  | call info => exact absurd rfl (hcall info)
  | tryCall info ti => exact absurd rfl (htry info ti)
  | atomicRmwLoop => exact (hrmw _ _ _ _ _ _ _ _ rfl).elim
  | atomicCasLoop => exact (hcas _ _ _ _ _ _ _ rfl).elim
  | args ds => simp only [csem, regVal_setMem, Option.map_some]
  | rets us => simp only [csem, Option.map_some]
  | loadExtNameGot rd n => simp only [csem, Option.map_some]
  | loadExtNameNear rd n off => simp only [csem, Option.map_some]
  | elfTlsGetAddr n rd tmp => simp only [csem, hX n m w, write_pstate_setMem, Option.map_some]
  | jump l => simp only [csem, Option.map_some]
  | condBr a b k => simp only [csem, holds_setMem, Option.map_some]
  | testBitAndBranch k a b rn bit =>
    simp only [csem]; split <;> simp only [Option.map_some, Option.map_none]
  | trapIf k c => simp only [csem, holds_setMem, Option.map_some]
  | udf c => simp only [csem, Option.map_some]
  | emitIsland n => simp only [csem, Option.map_some]
  | jtSequence d ts r a b =>
    simp only [csem, condHolds_setMem]
    split
    · split
      · simp only [Option.map_some]
      · split <;> simp only [Option.map_some, Option.map_none]
    · simp only [Option.map_none]
  | _ => simp [MInst.isCtl] at hctl

theorem ifoot_none' {sem : ISem CV ArmState} {i : MInst} {uses : List CV} {w : ArmState}
    (h : ∀ w', sem i uses w' = none) : IFoot sem i uses w [] :=
  ifoot_nil fun m => by rw [h, h]; rfl

/-- **Every VCode instruction except calls has a precise footprint under `csem`** (on an
error-free world; a straight-line form covered by `csem`'s canonical run, `csemWF`, on an aligned
world; the TLSDESC call's flags do not depend on memory). -/
theorem ifoot_csem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : ArmState} (hX : TlsMemFree X) (he : Arm.r .ERR w = .None)
    (hcall : ∀ info, i ≠ .call info) (htry : ∀ info ti, i ≠ .tryCall info ti)
    (hst : i.isCtl = false → csemWF ctx i uses = true ∧ Arm.CheckSPAlignment w) :
    IFoot (csem F ctx X) i uses w (cEvs F ctx i uses w) := by
  unfold cEvs
  by_cases hc : i.isCtl = true
  · simp only [hc, ite_true]
    cases i with
    | atomicRmwLoop ty op fl a b c d e =>
      rcases uses with _ | ⟨u, _ | ⟨x, _ | ⟨y, t⟩⟩⟩
      · exact ifoot_none' fun _ => rfl
      · exact ifoot_none' fun _ => rfl
      · exact rmw_foot he
      · exact ifoot_none' fun _ => rfl
    | atomicCasLoop ty fl a b c d e =>
      rcases uses with _ | ⟨u, _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩⟩
      · exact ifoot_none' fun _ => rfl
      · exact ifoot_none' fun _ => rfl
      · exact ifoot_none' fun _ => rfl
      · exact casEvs_foot he
      · exact ifoot_none' fun _ => rfl
    | _ =>
      exact ifoot_ctl hX hc hcall htry (fun _ _ _ _ _ _ _ _ h => nomatch h)
        (fun _ _ _ _ _ _ _ h => nomatch h)
  · have hc' : i.isCtl = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]
    obtain ⟨hwf, hal⟩ := hst hc'
    have hfoot := straightSem_foot (F := F) (ctx := ctx) (i := i) (uses := uses) (w := w)
    refine ⟨hfoot.1, fun m hm => ?_⟩
    rw [csem_of_wf hc' hwf (by rw [r_setMem]; exact he) (by rw [spAlign_setMem]; exact hal),
      csem_of_wf hc' hwf he hal]
    exact hfoot.2 m hm

/-! ## The event semantics of VCode -/

/-- The world `w` with its memory holding the read events' bytes (the thread's view after the
environment's writes): the read events, in order, stored in `w`'s memory. -/
def patch (evs : List Ev) (w : ArmState) : ArmState := setMem (applyR evs w.mem) w

/-- **One step of a VCode thread with its memory events.** The events are the instruction's
precise footprint (`ev`, e.g. `cEvs` for `csem`) on the thread's world whose memory holds the
read events' bytes (any bytes: the environment's choice); the step is the VCode step on that
world. -/
inductive VTStep (vc : VCode) (sem : ISem CV ArmState)
    (ev : MInst → List CV → ArmState → List Ev) :
    VConf CV ArmState → List Ev → VConf CV ArmState → Prop
  | mk {b k : Nat} {ρ : Nat → CV} {w : ArmState} {vb : VBlock} {i : MInst} {ops : Array Operand}
      {evs : List Ev} {c' : VConf CV ArmState} :
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      evs = ev i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) (patch evs w) →
      IFoot sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) (patch evs w) evs →
      VStep vc sem (.run ⟨b, k, ρ, patch evs w⟩) c' →
      VTStep vc sem ev (.run ⟨b, k, ρ, w⟩) evs c'

theorem patch_of_agrees {evs : List Ev} {w : ArmState} (h : Agrees evs w.mem) : patch evs w = w := by
  unfold patch; rw [applyR_of_agrees h, setMem_self]

/-- **Against SC memory a VCode thread step is a VCode step**: when the read events hold the
bytes of the thread's memory, the patched world is the world. -/
theorem vtstep_sc {vc : VCode} {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    {s : VState CV ArmState} {evs : List Ev} {c' : VConf CV ArmState}
    (h : VTStep vc sem ev (.run s) evs c') (hag : Agrees evs s.w.mem) : VStep vc sem (.run s) c' := by
  cases h with
  | mk _ _ _ _ _ hst => rw [patch_of_agrees hag] at hst; exact hst

/-- **Every step of VCode under `csem` is a thread step with its precise footprint** (`cEvs`),
for the instructions `ifoot_csem` covers, when the events read the world's memory. -/
theorem exists_vtstep {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {b k : Nat} {ρ : Nat → CV} {w : ArmState} {vb : VBlock} {i : MInst} {ops : Array Operand}
    {c' : VConf CV ArmState} (hX : TlsMemFree X) (he : Arm.r .ERR w = .None)
    (hb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hcall : ∀ info, i ≠ .call info) (htry : ∀ info ti, i ≠ .tryCall info ti)
    (hst : i.isCtl = false →
      csemWF ctx i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) = true ∧
        Arm.CheckSPAlignment w)
    (hag : Agrees (cEvs F ctx i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w) w.mem)
    (h : VStep vc (csem F ctx X) (.run ⟨b, k, ρ, w⟩) c') :
    VTStep vc (csem F ctx X) (cEvs F ctx) (.run ⟨b, k, ρ, w⟩)
      (cEvs F ctx i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w) c' := by
  have hp := patch_of_agrees hag
  refine .mk hb hi hops (by rw [hp]) (by rw [hp]; exact ifoot_csem hX he hcall htry hst)
    (by rw [hp]; exact h)

end Concurrency.VCodeThread

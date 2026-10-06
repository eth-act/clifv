import FV.E2E.RegLevelMove
import FV.E2E.ExecReads
import FV.E2E.MoveReads

/-!
# The per-state facts of the M6 runs that the executable machine needs (L3 (c))

`RL.Good` (no return into the activation's own code) is what the linked calls need of every
state of an activation's run before its return. The executable machine of `E2E.ExecBytes`
(the processor on the executable's own words) needs more of each state of the model's run
(`E2E.ExecBytes.StepOkD`); `RL.GoodX` is the register-level form of those facts, proven next to
`RL.Good` in every `realizes_*` case:

* `err`, `prog`: no error, the function's program;
* `line`: the pc is at an instruction line of the function, not inside the TLS sequence past its
  `ldr` (`Insn.tlsTail`: the `add`/`blr` the TLS hook skips);
* `next` (D1): the next state errs, returns to the entry's `x30`, is 4 bytes on, or is at a line
  that does not follow the first word of an `adrp` pair (`Insn.pairFirst`), so the next pc is the
  second word of a pair only after its first word;
* `got` (D4): at the `ldr` of a GOT pair the kept addresses `R.G` hold their entry bytes;
* `blr`: a `blr` reads its target from a register other than `xzr`, and the code words are
  readable as data;
* `reads` (D2): the memory reads (`MemReads`) of the unhooked instruction at the pc are outside
  the kept addresses `R.G` or bytes of the function's jump tables (`RL.ReadOk`), except at the
  loads of move code (`RL.SlotLoadAt`: spill reloads `[sp, #off]`, `[x16]`).
-/

namespace Backend.Proof

open Backend E2E

/-- The first word of an `adrp` pair (its second word, `ldr`/`add`, is the next line). -/
def _root_.Backend.Insn.pairFirst : Insn → Bool
  | .adrpGot .. | .adrp .. => true
  | _ => false

/-- The instructions of the TLS sequence past its `ldr` (the TLS hook runs them). -/
def _root_.Backend.Insn.tlsTail : Insn → Bool
  | .addTlsDescLo12 .. | .blrTlsDesc .. => true
  | _ => false

/-- The pc of `u` is at an instruction line of the activation with instruction `x`. -/
def RL.AtLine (R : RL) (u : Arm.ArmState) (x : Insn) : Prop :=
  ∃ j t, R.L[j]? = some (.ins x t) ∧ Arm.r .PC u = R.pcOf j

/-- **Where the step from `u` to `v` goes** (D1): `v` errs, returns to the entry's `x30`, is 4
bytes on, or is at a line that does not follow the first word of an `adrp` pair. -/
def RL.NextOk (R : RL) (u v : Arm.ArmState) : Prop :=
  Arm.r .ERR v ≠ .None ∨ Arm.r .PC v = xreg 30 R.s0 ∨ Arm.r .PC v = Arm.r .PC u + 4 ∨
    ∃ j, Arm.r .PC v = R.pcOf (j + 1) ∧ ∀ x t, R.L[j]? = some (.ins x t) → x.pairFirst = false

/-- The calls of `vc` through a register call through an integer vreg (`LinkSys.Ok.blrRegs`), so
that the allocation never gives them `xzr`. -/
def _root_.Backend.VCode.DestsInt (vc : VCode) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (info : CallInfo), vc.blocks[b]? = some vb →
    (vb.insts[k]? = some (MInst.call info) ∨ ∃ ti, vb.insts[k]? = some (MInst.tryCall info ti)) →
    ∀ (r : Reg), info.dest = CallDest.reg r → ∃ t, r = Reg.vreg t .int

/-- **The premise of the callee contract at a call state `u`** of the activation: the
antecedent of the operand-view obligation (`CallSoundCtlG`, `OperandsSoundCtlAtI`) that
`realizes_call`/`realizes_tryCall` pass to the contract (`CalleeOkG.os`, `CalleeTryOkG`) for the
allocated call (`call`, or the call of a `try_call`) whose code is at the pc. The linking layer
turns it into the facts of the callee's run. -/
def RL.CallPre (R : RL) (u : Arm.ArmState) : Prop :=
  ∃ (ctx : FnCtx) (i : MInst) (ctl : Ctl),
    (∃ info : CallInfo, (∃ (b : Nat) (vb : VBlock) (k : Nat), R.vc.blocks[b]? = some vb ∧
        (vb.insts[k]? = some (MInst.call info) ∨ ∃ ti, vb.insts[k]? = some (MInst.tryCall info ti))) ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti)) ∧
    R.K ≤ (spOf u).toNat ∧ (∀ a, StackBelow R.K (spOf u) a → R.F a) ∧
    (∀ a, R.G a → u.mem a = R.s0.mem a) ∧
    ∃ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
      (w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState),
      i.operands = .ok ops ∧ c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () ∧
      i.assign regs = .ok i' ∧ CallAt R.fa R.base (Arm.r .PC u) i' ∧
      SameWorld R.F u w ∧ Arm.CheckSPAlignment u ∧ Arm.r .ERR u = .None ∧
      csemV R.gv R.F ctx R.X i (useVals ops regs u) w = some (outs, w', ctl)

/-- **A byte the activation's run may read** (D2): outside the kept addresses `G`, or a byte of
one of its data (`.word`) lines, the jump tables. -/
def RL.ReadOk (R : RL) (a : BitVec 64) : Prop :=
  ¬ R.G a ∨ ∃ j tg bs, R.L[j]? = some (.word tg bs) ∧ ∃ i < 4, a = R.pcOf j + BitVec.ofNat 64 i

/-- **D2 at `u`**: the memory reads of the unhooked instruction at the pc are `ReadOk`. -/
def RL.ReadsAt (R : RL) (u : Arm.ArmState) : Prop :=
  ∀ j x t, R.L[j]? = some (.ins x t) → Arm.r .PC u = R.pcOf j → x.hooked = false →
    ∀ env a, x.toArmInst env = .ok a → ∀ p ∈ E2E.ExecBytes.MemReads a u, ∀ k < p.2,
      R.ReadOk (p.1 + BitVec.ofNat 64 k)

/-- The pc of `u` is at a load of move code (`Insn.slotLoad`), whose reads stay a hypothesis. -/
def RL.SlotLoadAt (R : RL) (u : Arm.ArmState) : Prop :=
  ∃ j x t, R.L[j]? = some (.ins x t) ∧ Arm.r .PC u = R.pcOf j ∧ x.slotLoad = true

/-- **The per-state facts of the activation's run** that the executable machine needs (module
doc). -/
structure RL.GoodX (R : RL) (u : Arm.ArmState) : Prop where
  good : R.Good u
  err : Arm.r .ERR u = .None
  prog : u.program = R.fb.program R.base
  /-- the pc is at an instruction line, not in the TLS sequence past its `ldr` -/
  line : ∃ x, R.AtLine u x ∧ x.tlsTail = false
  /-- D1 -/
  next : R.NextOk u (R.step u)
  /-- D4: at the `ldr` of a GOT pair the kept addresses hold their entry bytes -/
  got : ∀ rd rn n, R.AtLine u (.ldrGotLo12 rd rn n) → ∀ a, R.G a → u.mem a = R.s0.mem a
  /-- a `blr`: not through `xzr` (when the calls through a register are through int vregs), and
  the code words are readable as data -/
  blr : ∀ x, R.AtLine u (.blr x) → (R.vc.DestsInt → x ≠ .xzr) ∧ ∀ k w, R.fb.words[k]? = some w →
    Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) u = w
  /-- a call (`bl`, `blr`): the callee contract's premise holds -/
  call : ∀ x, R.AtLine u x → ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) → R.CallPre u
  /-- D2 (but at the loads of move code) -/
  reads : R.ReadsAt u ∨ R.SlotLoadAt u

/-! ## Basic facts -/

/-- Instruction lines at the same pc are the same line. -/
theorem RL.pcOf_inj {R : RL} (hR : R.Wf) {j j' : Nat} {x x' : Insn} {t t' : Option Clif.TrapCode}
    (hj : R.L[j]? = some (.ins x t)) (hj' : R.L[j']? = some (.ins x' t'))
    (he : R.pcOf j = R.pcOf j') : j = j' := by
  simp only [RL.pcOf, RL.L] at he hj hj'
  have hsz : (R.fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hR.layout]; exact hR.fit
  have hl1 := lineOffset_le_size R.fa.lines.toList (j + 1)
  have hl2 := lineOffset_le_size R.fa.lines.toList (j' + 1)
  have hs1 := lineOffset_succ R.fa.lines.toList j _ hj
  have hs2 := lineOffset_succ R.fa.lines.toList j' _ hj'
  simp only [Line.size] at hs1 hs2
  have he2 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he)
  simp only [BitVec.toNat_ofNat] at he2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he2
  exact lineOffset_inj hj hj' he2

/-- One instruction at a pc. -/
theorem RL.atLine_unique {R : RL} (hR : R.Wf) {u : Arm.ArmState} {x x' : Insn}
    (h : R.AtLine u x) (h' : R.AtLine u x') : x = x' := by
  obtain ⟨j, t, hj, hpc⟩ := h
  obtain ⟨j', t', hj', hpc'⟩ := h'
  obtain rfl := RL.pcOf_inj hR hj hj' (hpc.symm.trans hpc')
  rw [hj] at hj'
  cases hj'
  rfl

/-- The instruction line at `pcOf j`. -/
theorem RL.atLine_iff {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    {x' : Insn} : R.AtLine u x' ↔ x' = x :=
  ⟨fun h => RL.atLine_unique hR h ⟨j, t, hj, hpc⟩, fun e => e ▸ ⟨j, t, hj, hpc⟩⟩

/-- `ReadsAt` at an instruction line from the reads of its instruction. -/
theorem RL.readsAt_of_line {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (h : x.hooked = false → ∀ env a, x.toArmInst env = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemReads a u, ∀ k < p.2, R.ReadOk (p.1 + BitVec.ofNat 64 k)) :
    R.ReadsAt u := by
  intro j' x' t' hj' hpc' hh
  obtain rfl := RL.pcOf_inj hR hj hj' (hpc.symm.trans hpc')
  rw [hj] at hj'
  cases hj'
  exact h hh

/-- `ReadsAt` at a line whose instruction is no load. -/
theorem RL.readsAt_noLoad {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.loads = false) : R.ReadsAt u :=
  RL.readsAt_of_line hR hj hpc fun _ _ a ha p hp => by
    rw [Insn.memReads_nil hx ha] at hp; cases hp

/-- `ReadsAt` at a hooked line (the hooks are not the instruction's semantics). -/
theorem RL.readsAt_hooked {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = true) : R.ReadsAt u :=
  RL.readsAt_of_line hR hj hpc fun h => by rw [hx] at h; cases h

/-- A line without an instruction of the TLS sequence past its `ldr`. -/
def _root_.Backend.Line.tailFree : Line → Bool
  | .ins i _ => !i.tlsTail
  | _ => true

theorem loadConst64_tailFree (rd : Reg) (v : Nat) : ∀ ln ∈ loadConst64 rd v, ln.tailFree = true := by
  intro ln h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with rfl | ⟨j, _, hj⟩
  · rfl
  · split at hj
    · simp only [Option.some.injEq] at hj; subst hj; rfl
    · cases hj

theorem memFinalize_tailFree {c : FnCtx} {mm : AMode} {b : Nat} {v : List Line × AMode}
    (h : memFinalize c mm b = .ok v) : ∀ ln ∈ v.1, ln.tailFree = true := by
  intro ln hln
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, throw, throwThe,
    MonadExceptOf.throw, reduceCtorEq] at h <;> subst h
  all_goals first
    | (simp at hln; done)
    | (split at hln
       · simp at hln
       · split at hln
         · simp at hln
         · exact loadConst64_tailFree _ _ _ hln)

theorem rmwLoopMid_tailFree (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ x ∈ rmwLoopMid op bits, x.tlsTail = false := by
  have hc : ∀ op bits, (rmwLoopCmp op bits).tlsTail = false := by
    intro op bits; unfold rmwLoopCmp; split <;> rfl
  have hs : ∀ x ∈ rmwLoopSext bits, x.tlsTail = false := by
    intro x hx; unfold rmwLoopSext at hx; split at hx <;> simp at hx <;> subst hx <;> rfl
  intro x hx
  cases op <;> simp only [rmwLoopMid, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hx
  all_goals first
    | (rcases hx with hx | hx | hx <;> first | exact hs x hx | (subst hx; first | rfl | exact hc _ _))
    | (rcases hx with hx | hx <;> (subst hx; first | rfl | exact hc _ _))
    | (subst hx; rfl)

/-- The lines of an allocated instruction other than `elf_tls_get_addr` hold no instruction of
the TLS sequence past its `ldr`. -/
theorem lines_noTlsTail {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) (hm : ∀ n rd tmp, m ≠ .elfTlsGetAddr n rd tmp) :
    ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false := by
  suffices hs : ∀ ln ∈ ls, ln.tailFree = true by
    intro i t hi
    have := hs _ hi
    simpa [Line.tailFree] using this
  have hmf' : ∀ mm b v, memFinalize c mm b = .ok v → ∀ ln ∈ v.1, ln.tailFree = true :=
    fun _ _ _ hv => memFinalize_tailFree hv
  have hk : ∀ (k : CondBrKind) l, (k.insn l).tlsTail = false := fun k l => by cases k <;> rfl
  have hcas : ∀ bits, (casLoopCmp bits).tlsTail = false := by
    intro bits; unfold casLoopCmp; split <;> rfl
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals (try (exfalso; exact hm _ _ _ rfl))
  all_goals intro ln hln
  all_goals simp [MInst.lines.addOff, rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead] at hln
  all_goals (repeat' (split at hln)) <;> (try simp at hln)
  all_goals first
    | exact hmf' _ _ _ (by assumption) _ hln
    | (rename_i heq; simp [throw, throwThe, MonadExceptOf.throw] at heq; done)
    | (rcases hln with h | h | h | h | h | h | h | h | h <;>
        first
          | exact hmf' _ _ _ (by assumption) _ h
          | rfl
          | (simp only [Line.tailFree, hk, Bool.not_false]; done)
          | (rename_i hx; obtain ⟨-, rfl⟩ := hx; rfl)
          | (subst h; rfl)
          | (subst h; simp only [Line.tailFree, hk, Bool.not_false]; done)
          | (subst h; simp only [Line.tailFree, hcas, Bool.not_false]; done)
          | (obtain ⟨a, ha, rfl⟩ := h
             simp only [Line.tailFree, rmwLoopMid_tailFree _ _ a ha, Bool.not_false]; done)
          | (obtain ⟨a, ha, rfl⟩ := h; rfl)
          | (split at h <;> (try split at h) <;> simp at h <;> subst h <;> rfl))

/-! ## Builders -/

theorem Insn.pairFirst_of_hooked {x : Insn} (h : x.hooked = false) : x.pairFirst = false := by
  cases x <;> simp_all [Insn.hooked, Insn.pairFirst]

theorem RL.nextOk_err {R : RL} {u v : Arm.ArmState} (h : Arm.r .ERR v ≠ .None) : R.NextOk u v :=
  .inl h

theorem RL.nextOk_ret {R : RL} {u v : Arm.ArmState} (h : Arm.r .PC v = xreg 30 R.s0) :
    R.NextOk u v :=
  .inr (.inl h)

theorem RL.nextOk_pc4 {R : RL} {u v : Arm.ArmState} (h : Arm.r .PC v = Arm.r .PC u + 4) :
    R.NextOk u v :=
  .inr (.inr (.inl h))

/-- The next state is at the line after an instruction line other than the first word of an
`adrp` pair. -/
theorem RL.nextOk_succ {R : RL} {u v : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hx : x.pairFirst = false)
    (h : Arm.r .PC v = R.pcOf (j + 1)) : R.NextOk u v :=
  .inr (.inr (.inr ⟨j, h, fun x' t' hj' => by rw [hj] at hj'; cases hj'; exact hx⟩))

/-- The next state is at a label line (a branch target). -/
theorem RL.nextOk_label {R : RL} {u v : Arm.ArmState} {j : Nat} {l : Lbl}
    (hj : R.L[j]? = some (.label l)) (h : Arm.r .PC v = R.pcOf j) : R.NextOk u v := by
  refine .inr (.inr (.inr ⟨j, ?_, fun x' t' hj' => by rw [hj] at hj'; cases hj'⟩))
  rw [h]
  simp only [RL.pcOf]
  rw [lineOffset_succ _ _ _ hj]
  rfl

/-- **`GoodX` at an unhooked instruction line** outside the TLS tail (D2 or a move-code load). -/
theorem RL.goodX_ofInsD {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = false) (htl : x.tlsTail = false) (hgood : R.Good u)
    (herr : Arm.r .ERR u = .None) (hprog : u.program = R.fb.program R.base)
    (hnext : R.NextOk u (R.step u)) (hrd : R.ReadsAt u ∨ R.SlotLoadAt u) : R.GoodX u where
  good := hgood
  err := herr
  prog := hprog
  line := ⟨x, ⟨j, t, hj, hpc⟩, htl⟩
  next := hnext
  got := fun rd rn n h => by
    rw [RL.atLine_iff hR hj hpc] at h; subst h; simp [Insn.hooked] at hx
  blr := fun r h => by
    rw [RL.atLine_iff hR hj hpc] at h; subst h; simp [Insn.hooked] at hx
  call := fun x' h hc => by
    rw [RL.atLine_iff hR hj hpc] at h; subst h
    rcases hc with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> simp [Insn.hooked] at hx
  reads := hrd

/-- **`GoodX` at an unhooked instruction line** outside the TLS tail: `got`/`blr` are vacuous. -/
theorem RL.goodX_ofIns {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = false) (htl : x.tlsTail = false) (hgood : R.Good u)
    (herr : Arm.r .ERR u = .None) (hprog : u.program = R.fb.program R.base)
    (hnext : R.NextOk u (R.step u)) (hrd : R.ReadsAt u) : R.GoodX u where
  good := hgood
  err := herr
  prog := hprog
  line := ⟨x, ⟨j, t, hj, hpc⟩, htl⟩
  next := hnext
  got := fun rd rn n h => by
    rw [RL.atLine_iff hR hj hpc] at h; subst h; simp [Insn.hooked] at hx
  blr := fun r h => by
    rw [RL.atLine_iff hR hj hpc] at h; subst h; simp [Insn.hooked] at hx
  call := fun x' h hc => by
    rw [RL.atLine_iff hR hj hpc] at h; subst h
    rcases hc with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> simp [Insn.hooked] at hx
  reads := .inl hrd

/-- A prefix of a successful straight-line run succeeds. -/
theorem execLines_take : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState} (k : Nat),
    execLines env ls s = some s' → ∃ s1, execLines env (ls.take k) s = some s1
  | _, [], s, _, _, _ => ⟨s, by simp [execLines]⟩
  | _, _ :: _, s, _, 0, _ => ⟨s, by simp [execLines]⟩
  | _, .label _ :: _, _, _, _ + 1, h => by simp [execLines] at h
  | _, .word _ _ :: _, _, _, _ + 1, h => by simp [execLines] at h
  | env, .ins i t :: ls, s, s', k + 1, h => by
    simp only [List.take_succ_cons, execLines] at h ⊢
    split at h
    · rename_i ai hai
      split at h
      · rename_i hpc
        simp only [hpc, ite_true]
        exact execLines_take k h
      · cases h
    · cases h

/-- **The states of a straight-line run** (unhooked instruction lines without the TLS tail),
from a state satisfying `Good`, before its last line's step: `GoodX`. -/
theorem RL.goodX_execLinesG {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h0 : R.Good s) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s R.ReadOk ∨
      ∀ x t, Line.ins x t ∈ ls → x.loads = true → x.slotLoad = true) :
    ∀ i < ls.length, R.GoodX (iterN R.step i s) := by
  intro i hi
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls j s s' hat hhook
    hprog hpc herr hinter hrun
  obtain ⟨ln, hln⟩ : ∃ ln, ls[i]? = some ln := ⟨ls[i], List.getElem?_eq_getElem hi⟩
  have hmem := List.mem_of_getElem? hln
  obtain ⟨x, t, rfl⟩ := execLines_ins hrun _ hmem
  have hj : R.L[j + i]? = some (.ins x t) := hat i _ hln
  have hx := hhook x t hmem
  have hpci : Arm.r .PC (iterN R.step i s) = R.pcOf (j + i) := hpcs i (by omega)
  have hst : ∃ s1, execLines (R.envOf j) (ls.take i) s = some s1 ∧ iterN R.step i s = s1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨s, by simp [execLines], rfl⟩
    · obtain ⟨s1, hs1⟩ := execLines_take i hrun
      have hlen : (ls.take i).length = i := by simp; omega
      have hit := iterN_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit (ls.take i) j s s1
        (fun k ln hk => by
          rw [List.getElem?_take] at hk
          split at hk
          · exact hat k ln hk
          · cases hk)
        (fun i' t' hm => hhook i' t' (List.mem_of_mem_take hm)) hprog hpc herr
        (fun k hk0 hk s2 hs2 => hinter k hk0 (by omega) s2 (by
          rwa [List.take_take, Nat.min_eq_left (by omega)] at hs2)) hs1
      rw [hlen] at hit
      exact ⟨s1, hs1, hit⟩
  obtain ⟨s1, hs1, hit1⟩ := hst
  have hep : Arm.r .ERR (iterN R.step i s) = .None ∧ (iterN R.step i s).program = s.program := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨herr, rfl⟩
    · rw [hit1]
      exact hinter i hi0 hi s1 hs1
  have hgx := fun hrd' => RL.goodX_ofInsD hR hj hpci hx (htail x t hmem) (u := iterN R.step i s)
    (by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact h0
      · exact R.good_execLines hR hat hhook hprog hpc herr hinter hrun i hi0 (by omega))
    hep.1 (hep.2.trans hprog)
    (by
      refine RL.nextOk_succ hj (Insn.pairFirst_of_hooked hx) ?_
      have := hpcs (i + 1) (by omega)
      rw [iterN_add] at this
      exact this) hrd'
  rcases hrd with hrd | hsl
  · exact hgx (.inl (RL.readsAt_of_line hR hj hpci fun _ env a ha => by
      rw [hit1]; exact hrd i x t hln s1 hs1 env a ha))
  · cases hl : x.loads
    · exact hgx (.inl (RL.readsAt_noLoad hR hj hpci hl))
    · exact hgx (.inr ⟨j + i, x, t, hj, hpci, hsl x t hmem hl⟩)

/-- **The states of a straight-line run** (unhooked instruction lines without the TLS tail),
from a state with the body's `sp`, before its last line's step: `GoodX`. -/
theorem RL.goodX_execLines {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s R.ReadOk ∨
      ∀ x t, Line.ins x t ∈ ls → x.loads = true → x.slotLoad = true) :
    ∀ i < ls.length, R.GoodX (iterN R.step i s) :=
  RL.goodX_execLinesG hR hat hhook htail hprog hpc herr (.inr hsp) hinter hrun hrd

theorem prologueLines_tailFree (n : Nat) : ∀ ln ∈ prologueLines n, ln.tailFree = true := by
  intro ln h
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl) | h
  · rfl
  · rfl
  · split at h
    · simp at h
    · split at h
      · simp at h; subst h; rfl
      · rcases List.mem_append.1 h with h | h
        · exact loadConst64_tailFree _ _ _ h
        · simp at h; subst h; rfl

theorem epilogueLines_tailFree (n : Nat) : ∀ ln ∈ epilogueLines n, ln.tailFree = true := by
  intro ln h
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | (rfl | rfl)
  · split at h
    · simp at h
    · split at h
      · simp at h; subst h; rfl
      · rcases List.mem_append.1 h with h | h
        · exact loadConst64_tailFree _ _ _ h
        · simp at h; subst h; rfl
  · rfl
  · rfl

/-- The lines of code without `elf_tls_get_addr` hold no instruction of the TLS sequence past
its `ldr`. -/
theorem codeLinesE_noTlsTail {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      (∀ n rd tmp, AInst.inst (.elfTlsGetAddr n rd tmp) ∉ code) →
      codeLinesE c af code ps = .ok (ls, ps') → ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false
  | [], ps, ps', ls, _, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; simp
  | a :: as, ps, ps', ls, hno, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro i t hln
        rcases List.mem_append.1 hln with hln | hln
        · cases a with
          | inst m =>
            exact lines_noTlsTail hr (fun n rd tmp e => by subst e; exact hno n rd tmp (by simp))
              i t hln
          | prologue =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            split at hln
            · simpa [Line.tailFree] using prologueLines_tailFree _ _ hln
            · simp at hln
          | epilogueRet =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            split at hln
            · simpa [Line.tailFree] using epilogueLines_tailFree _ _ hln
            · simp at hln; rw [hln.1]; rfl
        · exact codeLinesE_noTlsTail as _ _ _ (fun n rd tmp h => hno n rd tmp (by simp [h])) hr2
            i t hln

/-- A one-line instruction is no `elf_tls_get_addr` (six lines). -/
theorem OneLine.not_tls {ctx : FnCtx} {i : MInst} (h : OneLine ctx i) :
    ∀ n rd tmp, i ≠ .elfTlsGetAddr n rd tmp := by
  intro n rd tmp e
  subst e
  obtain ⟨x, t, hl, -, -⟩ := h
  have := hl {}
  simp only [MInst.lines] at this
  split at this
  · simp [throw, throwThe, MonadExceptOf.throw] at this
  · simp [pure, Except.pure] at this

/-- **A move on the machine**: from `Q` at a move item, the machine runs the move's lines and
reaches `Q` at the next item with `MStep.move`'s store. -/
theorem realizes_move {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b : Nat} {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .move src dst :: its, m, w⟩)) :
    ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, upd m dst (m src), w⟩) ∧
      ∀ i < n, R.GoodX (iterN R.step i s) := by
  obtain ⟨j, vb, items, pre, code, ls, ps1, ps2, T, hvb, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  obtain ⟨⟨c, wh, hcm⟩, hLs, hLd, hT, hchk'⟩ := move_facts hit hsplit hchk
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  rw [itemCode_move] at hc1
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  obtain ⟨hvs, -, is, s', rfl, hmi, hex, hmo⟩ := lower_move (R.frameOk hR) R.ctx hcm
    hLs hLd hT hc1 hst.world hst.sp hst.align
  obtain ⟨ls1', hcl, hlen, hins, hpl, hrun, hint, hprog, herr⟩ :=
    run_oneLines R.ctx R.af is s s' (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hst.err
  rw [hcl ps1] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  -- the lines at `j`
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1' ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
  have hat : ∀ k ln, ls1'[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls1', ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩
  have hiter : iterN R.step ls1'.length s = s' :=
    iterN_execLines hR.layout hR.lm hR.fit ls1' j s s' hat
      (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
      (by rw [hst.prog]) (by rw [hpc]; rfl) hst.err (hint _) (hrun _)
  refine ⟨ls1'.length, ⟨j + ls1'.length, vb, items, pre ++ [.move src dst], c2, ls2, ps1, ps2, T, hvb,
    hit, by rw [hsplit]; simp, hchk', hc2, h2, htr, ?_, ?_, ?_⟩, fun i hi => ?_⟩
  rotate_right
  · exact R.goodX_execLines hR hat
      (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
      (codeLinesE_noTlsTail (is.map .inst) ps1 ps1 ls1' (fun n rd tmp h => by
        simp only [List.mem_map] at h
        obtain ⟨a, ha, e⟩ := h
        cases e
        exact (oneLine_of_moveInst R.ctx (hmi _ ha)).not_tls n rd tmp rfl) (hcl ps1))
      (by rw [hst.prog]) hpc hst.err hst.sp (hint _) (hrun _) (.inr fun x t hx hl => by
        obtain ⟨i', hi', ps0, hc⟩ := moveLines_mem (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi))
          (hcl ps1) hx
        exact moveInst_slotLoad R.ctx (hmi i' hi') hc hl) i hi
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · rw [hiter, execLines_pc (hrun ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩), hpc]
    simp only [RL.pcOf, RL.L]
    rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop') hins', BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
  · rw [hiter]
    have hsp' : spOf s' = R.spB := hmo.sp
    have hw' := hmo.world
    refine ⟨move_agree hst.store hvs hLs hmo.store, hw', herr, by rw [hprog, hst.prog], hsp',
      align_of_sp (by rw [hsp', hst.sp]) hst.align, fun hframe => ?_,
      code_frameKeep hR hmo.mem hst.code,
      fun a ha => (hmo.mem a (RL.G_not_slot hR ha)).trans (hst.gkeep a ha)⟩
    rw [← hst.fplr hframe]
    apply read_mem_bytes_congr
    intro k hk
    exact hmo.mem _ (fun o ho => by
      have := fplr_outside hR hframe k hk o ho
      rwa [show R.spB = spOf s by rw [hst.sp]] at this ⊢)

/-! ## The facts of an activation given by its data -/

/-- `RL.GoodX` of the activation with these data (the fields `lm`, `psF` play no role in it). -/
def actGoodX (vc : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) (base : BitVec 64)
    (s0 : Arm.ArmState) (X : ExtSem) (H : ArmHooks) (K : Nat) (G : BitVec 64 → Prop)
    (gv : Nat → String → Prop) (u : Arm.ArmState) : Prop :=
  RL.GoodX ⟨vc, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩ u

theorem RL.GoodX.act {R : RL} {u : Arm.ArmState} (h : R.GoodX u) :
    actGoodX R.vc R.rf R.af R.fa R.fb R.base R.s0 R.X R.H R.K R.G R.gv u :=
  ⟨h.good, h.err, h.prog, h.line, h.next, h.got, h.blr, h.call, h.reads⟩

end Backend.Proof

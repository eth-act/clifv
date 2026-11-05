import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.RegallocOperands
import FV.E2E.RegLevelOp
import FV.Backend.Proof.FormsCoverComplete
import FV.E2E.EmitLabels
import FV.E2E.SpillLower
import FV.E2E.SpillCtlCheck

/-!
# `emitPre` succeeds on the spill allocation (V6b)

`emitPre_spill_ok`: for every in-scope function, the instruction expansion `emitPre` of the
lowered spill allocation succeeds. `emitPre` fails only through `MInst.lines` of an `.inst m` of
the code, so the proof classifies these instructions (`spill_inst_cases`):

* the instructions of a move (`RAFrame.moveInsts`): `mov`, `movz`/`movk`/`add` of `x16`, and
  loads/stores at `[sp, #off]`/`[x16]` — all expand (`moveInsts_total`);
* the allocated form `m` (neither `Args` nor `Rets`, which `lowerRFunc` drops) of an instruction
  `i` of the VCode with the operand registers of `spillLocs` (`op_total`): a covered form
  (`FormOk`, `formOk_sound`'s `LinesOk`) or a control form (`FormsCovered`); the control forms
  expand whatever their registers, except the LL/SC loops and the TLS sequence, whose fixed
  registers `spillLocs` gives (their operands are int vregs by `ctlInstOk`).

`emitPre_of`: `emitPre` succeeds when every instruction expands and every branch target is a
block label (the unsimplified lines then pass `segsOk`/`padsOk`: `segsOk_raw`, `padsOk_raw`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov

/-- `m`'s expansion succeeds from every expansion state. -/
def LinesTotal (c : FnCtx) (m : MInst) : Prop := ∀ ps, ∃ r, m.lines c ps = .ok r

/-- Every successful run of `x` ends with a value meeting `P`. -/
def PutPost {α : Type} (x : StateT Nat (Except String) α) (P : α → Prop) : Prop :=
  ∀ s r s', x.run s = .ok (r, s') → P r

theorem putPost_pure {α : Type} {a : α} {P : α → Prop} (h : P a) :
    PutPost (pure a : StateT Nat (Except String) α) P := by
  intro s r s' e
  cases e
  exact h

theorem putPost_bind {α β : Type} {x : StateT Nat (Except String) α} {f : α → StateT Nat (Except String) β}
    {P : β → Prop} (h : ∀ a, PutPost (f a) P) : PutPost (x >>= f) P := by
  intro s r s' e
  simp only [StateT.run, bind, StateT.bind, Except.bind] at e
  split at e
  · cases e
  · exact h _ _ _ _ e

theorem assign_post {i i' : MInst} {regs : Array Reg} {P : MInst → Prop}
    (h : i.assign regs = .ok i') (hp : PutPost (MInst.visitOperands (putOp regs) i) P) : P i' := by
  rw [assign_eq] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · cases h
      exact hp 0 _ _ hr

theorem linesTotal_call (c : FnCtx) (info : CallInfo) : LinesTotal c (.call info) := by
  intro ps
  obtain ⟨d, u, ds⟩ := info
  cases d <;> exact ⟨_, rfl⟩

/-- The control forms other than the LL/SC loops and the TLS sequence: any allocated form other
than `Args`/`Rets` expands. -/
theorem ctl_post (c : FnCtx) (regs : Array Reg) {i : MInst} (hc : i.isCtl = true)
    (hrmw : ∀ ty op fl a o d s1 s2, i ≠ .atomicRmwLoop ty op fl a o d s1 s2)
    (hcas : ∀ ty fl a e r d s1, i ≠ .atomicCasLoop ty fl a e r d s1)
    (htls : ∀ n rd tmp, i ≠ .elfTlsGetAddr n rd tmp) :
    PutPost (MInst.visitOperands (putOp regs) i)
      (fun m => (∀ ds, m ≠ .args ds) → (∀ us, m ≠ .rets us) → LinesTotal c m) := by
  cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hc
  case atomicRmwLoop => exact absurd rfl (hrmw _ _ _ _ _ _ _ _)
  case atomicCasLoop => exact absurd rfl (hcas _ _ _ _ _ _ _)
  case elfTlsGetAddr => exact absurd rfl (htls _ _ _)
  all_goals
    simp only [MInst.visitOperands]
    repeat' first | (with_reducible apply putPost_bind); intro _ | (with_reducible apply putPost_pure) | split
  all_goals
    intro h1 h2
    first | exact absurd rfl (h1 _) | exact absurd rfl (h2 _) | exact linesTotal_call c _ | (intro ps; exact ⟨_, rfl⟩)

theorem linesTotal_of_linesOk {c : FnCtx} {m : MInst} (h : LinesOk c m) : LinesTotal c m :=
  fun ps => let ⟨_, hl, _⟩ := h; ⟨_, hl ps⟩

theorem formOk_total {c : FnCtx} {i i' : MInst} {regs : Array Reg} (h : FormOk c i = true)
    (hi : i.assign regs = .ok i') : LinesTotal c i' :=
  linesTotal_of_linesOk ((formOk_sound (F := fun _ => True) (X := ⟨fun _ _ _ => none, fun _ _ => 0, 0, fun _ _ => Arm.PState.zero⟩) h).2 regs i' hi).1

theorem vregInt_eq {r : Reg} (h : r.isVregInt = true) : ∃ n, r = .vreg n .int := by
  cases r with
  | vreg n cl => cases cl <;> first | exact ⟨n, rfl⟩ | cases h
  | _ => cases h

theorem unreg_eq {regs xs : Array Reg} (h : regs.map Loc.reg = xs.map Loc.reg) : regs = xs := by
  have := congrArg (Array.map fun l => match l with | Loc.reg r => r | _ => Reg.sp) h
  simpa [Array.map_map, Function.comp_def] using this

theorem rmw_total (c : FnCtx) {ty : CTy} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags}
    {p x d d1 d2 : Nat} {regs : Array Reg} {i' : MInst}
    (hl : ∀ ops, (MInst.atomicRmwLoop ty op fl (.vreg p .int) (.vreg x .int) (.vreg d .int)
        (.vreg d1 .int) (.vreg d2 .int)).operands = .ok ops →
      regs.map Loc.reg = spillLocs ops (MInst.atomicRmwLoop ty op fl (.vreg p .int) (.vreg x .int)
        (.vreg d .int) (.vreg d1 .int) (.vreg d2 .int)).clobbers)
    (ha : (MInst.atomicRmwLoop ty op fl (.vreg p .int) (.vreg x .int) (.vreg d .int)
        (.vreg d1 .int) (.vreg d2 .int)).assign regs = .ok i') : LinesTotal c i' := by
  have hr : regs = #[.x 25, .x 26, .x 27, .x 24, .x 28] :=
    unreg_eq ((hl _ rfl).trans (by simp [spillLocs, fixedRegs, spillPool, OpSpec.fixedUse, OpSpec.fixedDef, MInst.clobbers]))
  subst hr
  have e : (MInst.atomicRmwLoop ty op fl (.vreg p .int) (.vreg x .int) (.vreg d .int)
        (.vreg d1 .int) (.vreg d2 .int)).assign #[.x 25, .x 26, .x 27, .x 24, .x 28] =
      .ok (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)) := rfl
  rw [e] at ha
  cases ha
  intro ps
  simp [MInst.lines]

theorem cas_total (c : FnCtx) {ty : CTy} {fl : Clif.MemFlags}
    {p e x d d1 : Nat} {regs : Array Reg} {i' : MInst}
    (hl : ∀ ops, (MInst.atomicCasLoop ty fl (.vreg p .int) (.vreg e .int) (.vreg x .int)
        (.vreg d .int) (.vreg d1 .int)).operands = .ok ops →
      regs.map Loc.reg = spillLocs ops (MInst.atomicCasLoop ty fl (.vreg p .int) (.vreg e .int)
        (.vreg x .int) (.vreg d .int) (.vreg d1 .int)).clobbers)
    (ha : (MInst.atomicCasLoop ty fl (.vreg p .int) (.vreg e .int) (.vreg x .int)
        (.vreg d .int) (.vreg d1 .int)).assign regs = .ok i') : LinesTotal c i' := by
  have hr : regs = #[.x 25, .x 26, .x 28, .x 27, .x 24] :=
    unreg_eq ((hl _ rfl).trans (by simp [spillLocs, fixedRegs, spillPool, OpSpec.fixedUse, OpSpec.fixedDef, MInst.clobbers]))
  subst hr
  have e : (MInst.atomicCasLoop ty fl (.vreg p .int) (.vreg e .int) (.vreg x .int)
        (.vreg d .int) (.vreg d1 .int)).assign #[.x 25, .x 26, .x 28, .x 27, .x 24] =
      .ok (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24)) := rfl
  rw [e] at ha
  cases ha
  intro ps
  simp [MInst.lines]

theorem tls_total (c : FnCtx) {n : String} {d t : Nat} {regs : Array Reg} {i' : MInst}
    (hl : ∀ ops, (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).operands = .ok ops →
      regs.map Loc.reg = spillLocs ops (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).clobbers)
    (ha : (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).assign regs = .ok i') :
    LinesTotal c i' := by
  have hf : List.filter (fun r => !decide (r = Reg.x 0)) (List.map Reg.x (List.range 16)) =
      .x 1 :: List.map Reg.x (List.range' 2 14) := by decide
  have hr : regs = #[.x 0, .x 1] := unreg_eq ((hl _ rfl).trans (by
    simp [spillLocs, fixedRegs, spillPool, OpSpec.fixedDef, OpSpec.earlyDef, MInst.clobbers, hf]))
  subst hr
  have e : (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).assign #[.x 0, .x 1] =
      .ok (.elfTlsGetAddr n (.x 0) (.x 1)) := rfl
  rw [e] at ha
  cases ha
  intro ps
  simp [MInst.lines]

theorem linesTotal_load (c : FnCtx) (op : LoadOp) (rd : Reg) (m : AMode) (fl : Clif.MemFlags)
    (hm : ∀ o, m ≠ .incomingArg o) : LinesTotal c (.load op rd m fl) :=
  linesTotal_of_linesOk (linesOk_load c op rd m fl hm)

theorem linesTotal_store (c : FnCtx) (op : StoreOp) (rd : Reg) (m : AMode) (fl : Clif.MemFlags)
    (hm : ∀ o, m ≠ .incomingArg o) : LinesTotal c (.store op rd m fl) :=
  linesTotal_of_linesOk (linesOk_store c op rd m fl hm)

theorem spAddrX16_total (c : FnCtx) (off : Nat) : ∀ m ∈ spAddrX16 off, LinesTotal c m := by
  intro m hm
  simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hm
  rcases hm with (rfl | ⟨_, _, rfl⟩) | rfl <;> intro ps <;> exact ⟨_, rfl⟩

theorem slotStoreAt_total (c : FnCtx) (cls : RegClass) (r : Reg) (off : Nat) :
    ∀ m ∈ slotStoreAt cls r off, LinesTotal c m := by
  intro m hm
  unfold slotStoreAt at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    unfold slotStore
    cases cls <;> exact linesTotal_store _ _ _ _ _ (fun _ h => by cases h)
  · rcases List.mem_append.mp hm with h | h
    · exact spAddrX16_total c off m h
    · simp only [List.mem_singleton] at h
      subst h
      cases cls <;> exact linesTotal_store _ _ _ _ _ (fun _ h => by cases h)

theorem slotLoadAt_total (c : FnCtx) (cls : RegClass) (r : Reg) (off : Nat) :
    ∀ m ∈ slotLoadAt cls r off, LinesTotal c m := by
  intro m hm
  unfold slotLoadAt at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    unfold slotLoad
    cases cls <;> exact linesTotal_load _ _ _ _ _ (fun _ h => by cases h)
  · rcases List.mem_append.mp hm with h | h
    · exact spAddrX16_total c off m h
    · simp only [List.mem_singleton] at h
      subst h
      cases cls <;> exact linesTotal_load _ _ _ _ _ (fun _ h => by cases h)

theorem mem_map_inst {ms : List MInst} {m : MInst} (h : AInst.inst m ∈ ms.map AInst.inst) : m ∈ ms := by
  obtain ⟨m', hm', e⟩ := List.mem_map.mp h
  cases e
  exact hm'

/-- **Every instruction of a move expands.** -/
theorem moveInsts_total (c : FnCtx) {fr : RAFrame} {src dst : Loc} {l : List AInst}
    (h : fr.moveInsts src dst = .ok l) : ∀ m, AInst.inst m ∈ l → LinesTotal c m := by
  intro m hm
  unfold RAFrame.moveInsts at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; cases hm
  · cases h; cases hm
  · split at h
    · cases h
      simp only [List.mem_singleton, AInst.inst.injEq] at hm
      subst hm
      intro ps; exact ⟨_, rfl⟩
    · cases h
      rcases List.mem_append.mp (mem_map_inst hm) with h | h
      · exact slotStoreAt_total c _ _ _ m h
      · exact slotLoadAt_total c _ _ _ m h
  · split at h
    · cases h
    · cases h
      exact slotStoreAt_total c _ _ _ m (mem_map_inst hm)
  · split at h
    · cases h
    · cases h
      exact slotLoadAt_total c _ _ _ m (mem_map_inst hm)
  · cases h

/-- **An instruction of the spill allocation expands**: an instruction `i` of the VCode that is a
covered form or a control form meeting `ctlInstOk`, with the operand locations `spillLocs`. -/
theorem op_total {c : FnCtx} {i i' : MInst} {regs : Array Reg} {b k : Nat}
    (hcov : i.isCtl = true ∨ FormOk c i = true) (hctl : ctlInstOk b k i = true)
    (hloc : ∀ ops, i.operands = .ok ops → regs.map Loc.reg = spillLocs ops i.clobbers)
    (hasg : i.assign regs = .ok i') (hna : ∀ ds, i' ≠ .args ds) (hnr : ∀ us, i' ≠ .rets us) :
    LinesTotal c i' := by
  rcases hcov with hc | hf
  · cases i
    case atomicRmwLoop ty op fl a o d s1 s2 =>
      simp only [ctlInstOk, Bool.and_eq_true] at hctl
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hctl
      obtain ⟨_, rfl⟩ := vregInt_eq h1
      obtain ⟨_, rfl⟩ := vregInt_eq h2
      obtain ⟨_, rfl⟩ := vregInt_eq h3
      obtain ⟨_, rfl⟩ := vregInt_eq h4
      obtain ⟨_, rfl⟩ := vregInt_eq h5
      exact rmw_total c hloc hasg
    case atomicCasLoop ty fl a e r d s1 =>
      simp only [ctlInstOk, Bool.and_eq_true] at hctl
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hctl
      obtain ⟨_, rfl⟩ := vregInt_eq h1
      obtain ⟨_, rfl⟩ := vregInt_eq h2
      obtain ⟨_, rfl⟩ := vregInt_eq h3
      obtain ⟨_, rfl⟩ := vregInt_eq h4
      obtain ⟨_, rfl⟩ := vregInt_eq h5
      exact cas_total c hloc hasg
    case elfTlsGetAddr n rd tmp =>
      simp only [ctlInstOk, Bool.and_eq_true] at hctl
      obtain ⟨h1, h2⟩ := hctl
      obtain ⟨_, rfl⟩ := vregInt_eq h1
      obtain ⟨_, rfl⟩ := vregInt_eq h2
      exact tls_total c hloc hasg
    all_goals
      exact assign_post hasg (ctl_post c regs hc (fun _ _ _ _ _ _ _ _ h => by cases h)
        (fun _ _ _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)) hna hnr
  · exact formOk_total hf hasg

/-! ## The code of the spill allocation -/

theorem mem_itemsCode {fr : RAFrame} {vb : VBlock} : ∀ {its : List RItem} {code : List AInst}
    {a : AInst}, itemsCode fr vb its = .ok code → a ∈ code →
      ∃ it ∈ its, ∃ c1, itemCode fr vb it = .ok c1 ∧ a ∈ c1
  | [], code, a, h, ha => by
    simp only [itemsCode, pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases ha
  | it :: its, code, a, h, ha => by
    simp only [itemsCode, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i c1 h1
      split at h
      · cases h
      · rename_i c2 h2
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_append.mp ha with ha | ha
        · exact ⟨it, List.mem_cons_self .., c1, h1, ha⟩
        · obtain ⟨it', hit', c, hc, hac⟩ := mem_itemsCode h2 ha
          exact ⟨it', List.mem_cons_of_mem _ hit', c, hc, hac⟩

theorem itemCode_move_ok {fr : RAFrame} {vb : VBlock} {src dst : Loc} {c1 : List AInst}
    (h : itemCode fr vb (.move src dst) = .ok c1) : fr.moveInsts src dst = .ok c1 := by
  simp only [itemCode, itemStep] at h
  cases hm : fr.moveInsts src dst with
  | error e => rw [hm] at h; cases h
  | ok l =>
    rw [hm] at h
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Except.ok.injEq] at h
    rw [← h]
    simp

/-- **The instructions of the spill allocation's code**: every `.inst m` of block `b` of `af` is
an instruction of a move between a register and a register or a frame slot (`MoveOk`), or the
allocated form `m` (neither `Args` nor `Rets`) of an instruction `i` of block `b` of the VCode, with
the operand registers `regs` that `spillLocs` gives. -/
theorem spill_inst_cases {f : Clif.Function} {vc vcp : VCode} {af : AFunc}
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af)
    {b : Nat} {l : Label} {code : Array AInst} {m : MInst}
    (hb : af.blocks[b]? = some (l, code)) (hm : AInst.inst m ∈ code.toList) :
    ∃ vb, vcp.blocks[b]? = some vb ∧
      ((∃ (src dst : Loc) (ms : List AInst), MoveOk src dst ∧
          (RAFrame.compute vcp (spillAlloc vcp)).moveInsts src dst = .ok ms ∧ AInst.inst m ∈ ms) ∨
       (∃ (kk : Nat) (i : MInst) (regs : Array Reg), vb.insts[kk]? = some i ∧ i.assign regs = .ok m ∧
          (∀ ops, i.operands = .ok ops → regs.map Loc.reg = spillLocs ops i.clobbers) ∧
          (∀ ds, m ≠ .args ds) ∧ (∀ us, m ≠ .rets us))) := by
  have hS := lowerScope_of hs
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hp (prepDomain_of_lower hS hl hS.nonempty)
  obtain ⟨⟨-, -, hsz, hbl⟩, -, -⟩ := lowerRFunc_ok ha
  have hlt : b < (vcp.blocks.zip (spillAlloc vcp).blocks).size := by
    rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hb).1
  rw [Array.size_zip] at hlt
  obtain ⟨vb, hvb⟩ : ∃ vb, vcp.blocks[b]? = some vb :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items, hit⟩ : ∃ items, (spillAlloc vcp).blocks[b]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cd, hcd, hb'⟩ := hbl b vb items hvb hit
  rw [hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  have hm' : AInst.inst m ∈ cd := by
    rcases List.mem_append.mp hm with h | h
    · split at h <;> simp at h
    · exact h
  obtain ⟨it, hitm, c1, hc1, hmc⟩ := mem_itemsCode hcd hm'
  have hok := itemOk_spillAlloc hcfg hvb hit it hitm
  refine ⟨vb, hvb, ?_⟩
  cases it with
  | move src dst => exact .inl ⟨src, dst, c1, hok, itemCode_move_ok hc1, hmc⟩
  | op kk allocs =>
    obtain ⟨regs, i, i', rfl, hi, hasg, hcase⟩ := itemCode_op hc1
    obtain ⟨i0, hi0, hloc⟩ := hok
    rw [hi] at hi0
    cases hi0
    rcases hcase with ⟨rfl, hna, hnr⟩ | ⟨ds, -, rfl⟩ | ⟨us, -, rfl⟩
    · simp only [List.mem_singleton, AInst.inst.injEq] at hmc
      subst hmc
      exact .inr ⟨kk, i, regs, hi, hasg, hloc, hna, hnr⟩
    · cases hmc
    · simp at hmc

/-! ## `emitPre` succeeds when every instruction expands -/

theorem codeLinesE_total {c : FnCtx} {af : AFunc} : ∀ {code : List AInst},
    (∀ a ∈ code, ∀ ps, ∃ r, ainstLines c af a ps = .ok r) →
      ∀ ps, ∃ r, codeLinesE c af code ps = .ok r
  | [], _, ps => ⟨_, rfl⟩
  | a :: as, h, ps => by
    obtain ⟨⟨l1, ps1⟩, h1⟩ := h a (List.mem_cons_self ..) ps
    obtain ⟨⟨l2, ps2⟩, h2⟩ := codeLinesE_total (fun x hx => h x (List.mem_cons_of_mem _ hx)) ps1
    exact ⟨_, by simp only [codeLinesE, bind, Except.bind, h1, h2]; rfl⟩

theorem segsOf_total {c : FnCtx} {af : AFunc} : ∀ (bs : List ((Label × Array AInst) × Nat))
    (ps : PState), (∀ x ∈ bs, ∀ a ∈ x.1.2.toList, ∀ ps, ∃ r, ainstLines c af a ps = .ok r) →
      ∃ r, segsOf c af bs ps = .ok r
  | [], ps, _ => ⟨_, rfl⟩
  | ((l, code), i) :: bs, ps, h => by
    obtain ⟨⟨l1, ps1⟩, h1⟩ := codeLinesE_total (fun a ha => h _ (List.mem_cons_self ..) a
      ((List.dropLast_sublist _).subset ha)) ps
    obtain ⟨⟨l2, ps2⟩, h2⟩ := codeLinesE_total (fun a ha => h _ (List.mem_cons_self ..) a
      (EmitLabels.mem_of_getLast?_toList ha)) ps1
    obtain ⟨⟨l3, ps3⟩, h3⟩ := segsOf_total bs ps2 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨_, by simp only [segsOf, bind, Except.bind, h1, h2, h3]; rfl⟩

/-- The entry block comes first in `emitOrder`. -/
theorem emitOrder_head (af : AFunc) (h : 0 < af.blocks.size) :
    (emitOrder af).head?.map (·.2) = some 0 := by
  obtain ⟨b0, L, hL⟩ : ∃ b0 L, af.blocks.toList = b0 :: L := by
    cases hl : af.blocks.toList with
    | nil => rw [← Array.length_toList, hl] at h; cases h
    | cons b0 L => exact ⟨_, _, rfl⟩
  unfold emitOrder
  rw [hL]
  simp [List.zipIdx_cons]

/-- A last instruction's lines are its unsimplified lines (`RawTerm`). -/
theorem rawTerm_of {c : FnCtx} {af : AFunc} : ∀ (o : Option AInst) {t : List Line} {ps ps' : PState},
    codeLinesE c af o.toList ps = .ok (t, ps') → RawTerm o t
  | none, _, _, _, _ => by simp [RawTerm]
  | some a, t, ps, ps', h => by
    simp only [Option.toList, codeLinesE, bind, Except.bind] at h
    cases a with
    | prologue => simp [RawTerm]
    | epilogueRet => simp [RawTerm]
    | inst m =>
      cases m <;> simp only [RawTerm] <;> try trivial
      all_goals
        simp only [ainstLines, MInst.lines, pure, Except.pure] at h
        simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
          List.append_nil] at h
        first
        | (obtain ⟨rfl, -⟩ := h; rfl)
        | (obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩)

/-- A block label among a line's branch targets is a label it uses. -/
theorem target_used {ln : Line} {l : Label} (h : ln.target? = some (.block l)) :
    Lbl.block l ∈ ln.labelsUsed := by
  cases ln with
  | ins i tc => cases i <;> simp_all [Line.target?, Line.labelsUsed, Insn.pcRelSpec?]
  | word a b => simp_all [Line.target?, Line.labelsUsed]
  | label _ => simp [Line.target?] at h

set_option pp.proofs false in
/-- **`emitPre` succeeds when every instruction expands** and every branch target (and
`try_call` handler) is a block label: then the unsimplified lines pass the emission check
(`segsOk_raw`, `padsOk_raw`), whatever `MachBuffer`'s simplification does. -/
theorem emitPre_of {k : Nat} {af : AFunc}
    (htot : ∀ x ∈ af.blocks.toList, ∀ a ∈ x.2.toList, ∀ ps,
      ∃ r, ainstLines ⟨k, af.slotBase⟩ af a ps = .ok r)
    (hne : 0 < af.blocks.size)
    (ht : ∀ p ∈ af.blocks.toList, ∀ m, AInst.inst m ∈ p.2.toList → ∀ l ∈ m.targets,
      l ∈ af.blocks.toList.map (·.1)) :
    ∃ pre, emitPre k af = .ok pre := by
  have hz : af.blocks.toList.zipIdx.map (·.1) = af.blocks.toList := by
    rw [List.zipIdx_eq_zip_range', List.map_fst_zip (by simp)]
  have hmemO : ∀ x ∈ emitOrder af, x.1 ∈ af.blocks.toList := fun x hx => by
    rw [← hz]; exact List.mem_map.2 ⟨x, (emitOrder_perm af).mem_iff.mp hx, rfl⟩
  obtain ⟨⟨ss, ps⟩, hseg⟩ := segsOf_total (c := ⟨k, af.slotBase⟩) (af := af) (emitOrder af) {}
    (fun x hx a ha ps => htot x.1 (hmemO x hx) a ha ps)
  obtain ⟨hl, -, hss⟩ := segsOf_spec hseg
  -- the segments' labels are the blocks' labels
  have hlabel : ∀ l ∈ af.blocks.toList.map (·.1), ∃ s' ∈ ss, s'.label = l := by
    intro l hl'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl'
    obtain ⟨b, hb⟩ := List.getElem?_of_mem he
    have hm := emitOrder_mem (af := af) (b := b) (by simpa using hb)
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
    have hil : i < ss.length := by rw [hl]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨code, -, -, -, hbi, -⟩ := hss i ss[i] (List.getElem?_eq_getElem hil)
    rw [hi] at hbi
    simp only [Option.some.injEq, Prod.mk.injEq] at hbi
    exact ⟨ss[i], List.getElem_mem hil, by rw [hbi.1]⟩
  -- every segment: its block, its last instruction's raw lines
  have hseg' : ∀ s ∈ ss, ∃ code ps1 ps2, af.blocks[s.idx]? = some (s.label, code) ∧
      codeLinesE ⟨k, af.slotBase⟩ af code.toList.getLast?.toList ps1 = .ok (s.term, ps2) := by
    intro s hs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hs
    obtain ⟨code, -, psm, ps2, hbi, -, e2, -⟩ := hss i s hi
    exact ⟨code, psm, ps2, emitOrder_get (List.mem_of_getElem? hbi), e2⟩
  have h0 : ss.head?.map (·.idx) = some 0 := by
    have hh := emitOrder_head af hne
    cases hss0 : ss with
    | nil =>
      rw [hss0] at hl
      have : emitOrder af = [] := List.length_eq_zero_iff.mp hl.symm
      rw [this] at hh; cases hh
    | cons s0 ss' =>
      obtain ⟨code, -, -, -, hb0, -⟩ := hss 0 s0 (by simp [hss0])
      cases ho : emitOrder af with
      | nil => rw [ho] at hb0; cases hb0
      | cons x0 xs =>
        rw [ho] at hb0 hh
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb0
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hh ⊢
        rw [hb0] at hh
        exact hh
  have hraw : ∀ s ∈ ss, RawTerm (af.blocks[s.idx]?.bind (·.2.back?)) s.term := by
    intro s hs
    obtain ⟨code, ps1, ps2, hb, e2⟩ := hseg' s hs
    rw [hb, Option.bind_some, Array.back?_eq_getElem?]
    have : code[code.size - 1]? = code.toList.getLast? := by
      rw [List.getLast?_eq_getElem?]; simp
    rw [this]
    exact rawTerm_of _ e2
  have hlab : ∀ s ∈ ss, ∀ ln ∈ s.term, ∀ l, ln.target? = some (.block l) →
      ∃ s' ∈ ss, s'.label = l := by
    intro s hs ln hln l htl
    obtain ⟨code, ps1, ps2, hb, e2⟩ := hseg' s hs
    have hbm : (s.label, code) ∈ af.blocks.toList :=
      List.mem_of_getElem? (by simpa using hb : af.blocks.toList[s.idx]? = some _)
    have hc := EmitLabels.code_chunk (T := af.blocks.toList.map (·.1)) _ _ _ _ e2
      (fun m hm l' hl' => ht _ hbm m (EmitLabels.mem_of_getLast?_toList hm) l' hl')
    rcases hc.uses_in (.block l) (EmitLabels.mem_uses.2 ⟨ln, hln, target_used htl⟩) with
      hd | ⟨l', hl', e⟩ | ⟨n, e, -⟩
    · rcases hc.defs_in _ hd with ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
      · cases h
      · cases h
      · cases h
    · cases e; exact hlabel _ hl'
    · cases e
  have hpad : ∀ b ∈ af.blocks.toList, ∀ a ∈ b.2.toList, ∀ info ti, a = .inst (.tryCall info ti) →
      ∀ h ∈ ti.handlers, ∃ s ∈ ss, s.label = h.label := by
    intro b hb a ha info ti e h hh
    subst e
    exact hlabel _ (ht b hb _ ha h.label (by simp [MInst.targets]; exact .inl ⟨h, hh, rfl⟩))
  have hok := segsOk_raw (ps := ps) h0 hraw hlab
  have hpok := padsOk_raw (ps := ps) h0 hraw hlab hpad
  unfold emitPre emitPlan
  simp only [bind, Except.bind, hseg]
  split
  · exact ⟨_, rfl⟩
  · simp only [hok, hpok, Bool.and_self, ite_true, pure, Except.pure, Functor.map, Except.map]
    exact ⟨_, rfl⟩

/-- **`emitPre` succeeds on the spill allocation** of every in-scope function whose prepared
VCode branches only to its blocks (`branchTargetsOkB`, part of `emitCondsB`): every instruction
of its code expands (`MInst.lines`) and the unsimplified lines pass the emission check.
(Premise `htg` added with #553: `emitPlan` now checks the branches' lines, `segsOk`.) -/
theorem emitPre_spill_ok {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode} {af : AFunc}
    (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (htg : branchTargetsOkB vcp = true)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) : ∀ k, ∃ pre, emitPre k af = .ok pre := by
  intro k
  have hcov := formsCovered_completeB hs hl hp ⟨k, af.slotBase⟩
  obtain ⟨hins, vb0, -, hvb0, -⟩ := ctlInsts_pipeline hsub (dominated_of hd) (lowerScope_of hs) hl hp
  obtain ⟨hlab, ht⟩ := lowerRFunc_targets htg
    (Nat.le_of_eq (spillAlloc_size vcp).symm) ha
  refine emitPre_of ?_ ?_ ht
  · intro x hx a ha' ps
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨l, code⟩ := x
    cases a with
    | prologue => exact ⟨_, rfl⟩
    | epilogueRet => exact ⟨_, rfl⟩
    | inst m =>
      obtain ⟨vb, hvb, hcase⟩ := spill_inst_cases hs hl hp ha (by simpa using hb) ha'
      rcases hcase with ⟨src, dst, ms, -, hmv, hmm⟩ | ⟨kk, i, regs, hi, hasg, hloc, hna, hnr⟩
      · exact moveInsts_total _ hmv m hmm ps
      · exact op_total (hcov b vb kk i hvb hi) (hins b vb kk i hvb hi) hloc hasg hna hnr ps
  · have := congrArg List.length hlab
    simp only [List.length_map, Array.length_toList] at this
    rw [this]
    exact Array.size_pos_of_mem (Array.mem_of_getElem? hvb0)

end E2E

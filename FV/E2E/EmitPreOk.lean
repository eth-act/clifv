import FV.E2E.AllocTotal
import FV.E2E.RegLevelOp
import FV.Backend.Proof.FormsCoverComplete

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

`emitPre_of` is the converse of `emitPre_ok`: `emitPre` succeeds when the blocks' lines do.
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

theorem blocksLinesE_total {c : FnCtx} {af : AFunc} : ∀ {bs : List (Label × Array AInst)},
    (∀ x ∈ bs, ∀ a ∈ x.2.toList, ∀ ps, ∃ r, ainstLines c af a ps = .ok r) →
      ∀ ps, ∃ r, blocksLinesE c af bs ps = .ok r
  | [], _, ps => ⟨_, rfl⟩
  | (l, code) :: bs, h, ps => by
    obtain ⟨⟨l1, ps1⟩, h1⟩ := codeLinesE_total (h (l, code) (List.mem_cons_self ..)) ps
    obtain ⟨⟨l2, ps2⟩, h2⟩ := blocksLinesE_total (fun x hx => h x (List.mem_cons_of_mem _ hx)) ps1
    exact ⟨_, by simp only [blocksLinesE, bind, Except.bind, h1, h2]; rfl⟩

set_option pp.proofs false in
/-- `emitPre` succeeds when the blocks' lines do (the converse of `emitPre_ok`). -/
theorem emitPre_of {k : Nat} {af : AFunc}
    (h : ∃ r, blocksLinesE ⟨k, af.slotBase⟩ af af.blocks.toList {} = .ok r) :
    ∃ pre, emitPre k af = .ok pre := by
  cases he : emitPre k af with
  | ok pre => exact ⟨pre, rfl⟩
  | error e =>
    exfalso
    obtain ⟨⟨body, ps⟩, hb⟩ := h
    unfold emitPre at he
    simp only [← Array.forIn_toList] at he
    rw [forIn_except_yield _ _ _ (fun (x : Label × Array AInst) (s : PState × Array Line) =>
      (fun r : List Line × PState => (r.2, s.2.push (.label (.block x.1)) ++ r.1.toArray)) <$>
        codeLinesE ⟨k, af.slotBase⟩ af x.2.toList s.1)] at he
    · rw [blocksLinesE_foldl, hb] at he
      simp only [Functor.map, Except.map, bind, Except.bind, pure, Except.pure] at he
      rw [traps_foldl] at he
      cases he
    · intro x s
      obtain ⟨l, code⟩ := x
      simp only
      rw [forIn_except_yield _ _ _ (fun (a : AInst) (s : PState × Array Line) =>
        (fun r : List Line × PState => (r.2, s.2 ++ r.1.toArray)) <$> ainstLines ⟨k, af.slotBase⟩ af a s.1)]
      · rw [codeLinesE_foldl]
        cases codeLinesE ⟨k, af.slotBase⟩ af code.toList s.1 <;> rfl
      · intro a s
        cases a <;> simp [ainstLines] <;> cases af.frame <;> first | rfl | simp

/-- **`emitPre` succeeds on the spill allocation** of every in-scope function: every instruction
of its code expands (`MInst.lines`). -/
theorem emitPre_spill_ok {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode} {af : AFunc}
    (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) : ∀ k, ∃ pre, emitPre k af = .ok pre := by
  intro k
  have hcov := formsCovered_completeB hs hl hp ⟨k, af.slotBase⟩
  obtain ⟨hins, -⟩ := ctlInsts_pipeline hsub (dominated_of hd) (lowerScope_of hs) hl hp
  apply emitPre_of
  apply blocksLinesE_total
  intro x hx a ha' ps
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

end E2E

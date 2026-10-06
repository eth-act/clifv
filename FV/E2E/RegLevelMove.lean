import FV.E2E.RegLevelSim
import FV.Backend.Proof.RegallocMoves

/-!
# Moves on the machine (M6)

The code of a move (`RAFrame.moveInsts`) consists of one-line instructions (`OneLine`: `mov`,
slot stores and loads below 32 KiB, and beyond it x16's `movz`/`movk`/`add` and the accesses at
`[x16]`); `run_oneLines` turns their `ExecAll` run into
the lines `codeLinesE` produces, run by `execLines` with the intermediate states error-free
(`InterOk`), ready for `iterN_execLines`.
-/

namespace Backend.Proof

open Backend E2E

/-- `i` expands to a single, unhooked, plain instruction line, at every emitter state. -/
def OneLine (ctx : FnCtx) (i : MInst) : Prop :=
  ∃ x t, (∀ ps, i.lines ctx ps = .ok ([.ins x t], ps)) ∧ x.hooked = false ∧
    (Line.ins x t).plain = true

theorem oneLine_mov (ctx : FnCtx) (a b : Nat) : OneLine ctx (.mov .size64 (.x b) (.x a)) :=
  ⟨_, _, fun _ => rfl, rfl, rfl⟩

theorem oneLine_slotStore (ctx : FnCtx) (cls : RegClass) (r : Reg) {off : Nat}
    (h8 : off % 8 = 0) (h16 : cls = .float → off % 16 = 0) (hoff : off < 32768) :
    OneLine ctx (slotStore cls r off) := by
  by_cases h255 : off ≤ 255
  · cases cls <;>
    exact ⟨_, _, fun ps => by
      simp [MInst.lines, slotStore, memFinalize, simm9?, show (off : Int) ≤ 255 by omega]; exact ⟨rfl, rfl⟩,
      rfl, rfl⟩
  · cases cls
    · exact ⟨_, _, fun ps => by
        simp [MInst.lines, slotStore, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
          h8, StoreOp.bytes, show (off : Int) ≤ 32760 by omega]; exact ⟨rfl, rfl⟩, rfl, rfl⟩
    · have := h16 rfl
      exact ⟨_, _, fun ps => by
        simp [MInst.lines, slotStore, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
          this, StoreOp.bytes, show (off : Int) ≤ 65520 by omega]; exact ⟨rfl, rfl⟩, rfl, rfl⟩

theorem oneLine_slotLoad (ctx : FnCtx) (cls : RegClass) (r : Reg) {off : Nat}
    (h8 : off % 8 = 0) (h16 : cls = .float → off % 16 = 0) (hoff : off < 32768) :
    OneLine ctx (slotLoad cls r off) := by
  by_cases h255 : off ≤ 255
  · cases cls <;>
    exact ⟨_, _, fun ps => by
      simp [MInst.lines, slotLoad, memFinalize, simm9?, show (off : Int) ≤ 255 by omega]; exact ⟨rfl, rfl⟩,
      rfl, rfl⟩
  · cases cls
    · exact ⟨_, _, fun ps => by
        simp [MInst.lines, slotLoad, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
          h8, LoadOp.bytes, show (off : Int) ≤ 32760 by omega]; exact ⟨rfl, rfl⟩, rfl, rfl⟩
    · have := h16 rfl
      exact ⟨_, _, fun ps => by
        simp [MInst.lines, slotLoad, memFinalize, simm9?, uimm12Scaled?, show ¬ (off : Int) ≤ 255 by omega,
          this, LoadOp.bytes, show (off : Int) ≤ 65520 by omega]; exact ⟨rfl, rfl⟩, rfl, rfl⟩


theorem oneLine_movz (ctx : FnCtx) (c : MoveWideConst) :
    OneLine ctx (.movWide .movZ (.x 16) c .size64) := ⟨_, _, fun _ => rfl, rfl, rfl⟩

theorem oneLine_movk (ctx : FnCtx) (c : MoveWideConst) :
    OneLine ctx (.movK (.x 16) (.x 16) c .size64) := ⟨_, _, fun _ => rfl, rfl, rfl⟩

theorem oneLine_add_sp_x16 (ctx : FnCtx) :
    OneLine ctx (.aluRRRExtend .add .size64 (.x 16) .sp (.x 16) .sxtx) := ⟨_, _, fun _ => rfl, rfl, rfl⟩

theorem oneLine_store_x16 (ctx : FnCtx) (op : StoreOp) (r : Reg) :
    OneLine ctx (.store op r (.unsignedOffset (.x 16) 0) trustedFlags) :=
  ⟨_, _, fun ps => by simp [MInst.lines, memFinalize]; exact ⟨rfl, rfl⟩, rfl, rfl⟩

theorem oneLine_load_x16 (ctx : FnCtx) (op : LoadOp) (r : Reg) :
    OneLine ctx (.load op r (.unsignedOffset (.x 16) 0) trustedFlags) :=
  ⟨_, _, fun ps => by simp [MInst.lines, memFinalize]; exact ⟨rfl, rfl⟩, rfl, rfl⟩

/-- Running one line that `execMInst` runs to `t`: the step and the rest. -/
theorem execLines_cons_of {env : Env} {x : Insn} {t : Option Clif.TrapCode} {s t0 : Arm.ArmState}
    (h : execLines env [.ins x t] s = some t0) (ls : List Line) :
    execLines env (.ins x t :: ls) s = execLines { env with pc := env.pc + 4 } ls t0 := by
  simp only [execLines] at h ⊢
  split at h
  · rename_i hpc0
    split at h
    · rename_i hpc
      simp only [Option.some.injEq] at h; subst h; simp [hpc0, hpc]
    · cases h
  · cases h

theorem run_oneLines (ctx : FnCtx) (af : AFunc) :
    ∀ (is : List MInst) (s s' : Arm.ArmState), (∀ i ∈ is, OneLine ctx i) → ExecAll ctx is s s' →
      Arm.r .ERR s = .None →
      ∃ ls, (∀ ps, codeLinesE ctx af (is.map .inst) ps = .ok (ls, ps)) ∧ ls.length = is.length ∧
        (∀ ln ∈ ls, ∃ x t, ln = .ins x t ∧ x.hooked = false) ∧ (∀ ln ∈ ls, ln.plain = true) ∧
        (∀ env, execLines env ls s = some s') ∧ (∀ env, InterOk env ls s) ∧
        s'.program = s.program ∧ Arm.r .ERR s' = .None
  | [], s, s', _, h, herr => by
    simp only [ExecAll] at h; subst h
    refine ⟨[], fun ps => rfl, rfl, by simp, by simp, fun env => rfl, fun env k h0 hk => ?_, rfl, herr⟩
    simp at hk
  | i :: is, s, s', hone, h, herr => by
    obtain ⟨t0, hex, hte, htp, hrest⟩ := h
    obtain ⟨x, t, hl, hx, hp⟩ := hone i (by simp)
    have herr0 : Arm.r .ERR t0 = .None := by rw [hte, herr]
    obtain ⟨ls, hc, hlen, hins, hpl, hrun, hint, hprog, herr'⟩ :=
      run_oneLines ctx af is t0 s' (fun j hj => hone j (by simp [hj])) hrest herr0
    have h1 : ∀ env, execLines env [.ins x t] s = some t0 := fun env => by
      have := hex env
      simp only [execMInst, hl] at this
      exact this
    refine ⟨.ins x t :: ls, fun ps => ?_, by simp [hlen], ?_, ?_, fun env => ?_, fun env k h0 hk => ?_,
      hprog.trans htp, herr'⟩
    · simp only [List.map_cons, codeLinesE, ainstLines, hl, hc ps, bind, Except.bind, pure,
        Except.pure, List.singleton_append]
    · intro ln hln
      simp only [List.mem_cons] at hln
      rcases hln with rfl | hln
      · exact ⟨x, t, rfl, hx⟩
      · exact hins ln hln
    · intro ln hln
      simp only [List.mem_cons] at hln
      rcases hln with rfl | hln
      · exact hp
      · exact hpl ln hln
    · rw [execLines_cons_of (h1 env)]; exact hrun _
    · intro s1 hs1
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [List.take_succ_cons] at hs1
      rw [execLines_cons_of (h1 env)] at hs1
      by_cases hk0 : k' = 0
      · subst hk0
        simp only [List.take_zero, execLines, Option.some.injEq] at hs1
        subst hs1
        exact ⟨herr0, htp⟩
      · simp only [List.length_cons] at hk
        obtain ⟨e1, e2⟩ := hint _ k' (by omega) (by omega) s1 hs1
        exact ⟨e1, e2.trans htp⟩

/-- The expansion of an instruction other than `trapIf`/`jtSequence`/the atomic LL/SC loops
does not depend on the emitter state (the loops increment the emit-time label counter). -/
theorem lines_ps (c : FnCtx) (m : MInst) (ps : PState)
    (h1 : ∀ k code, m ≠ .trapIf k code) (h2 : ∀ a b d e f, m ≠ .jtSequence a b d e f)
    (h3 : ∀ ty op fl a o ov s1 s2, m ≠ .atomicRmwLoop ty op fl a o ov s1 s2)
    (h4 : ∀ ty fl a e r ov s, m ≠ .atomicCasLoop ty fl a e r ov s) :
    m.lines c ps = (fun p => (p.1, ps)) <$> m.lines c {} := by
  cases m
  all_goals first
    | (exfalso; exact h1 _ _ rfl)
    | (exfalso; exact h2 _ _ _ _ _ rfl)
    | (exfalso; exact h3 _ _ _ _ _ _ _ _ rfl)
    | (exfalso; exact h4 _ _ _ _ _ _ _ rfl)
    | skip
  all_goals simp only [MInst.lines]
  all_goals (repeat' split) <;> simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
  all_goals (cases memFinalize c _ _ <;> simp only [] <;> (try (rename_i v; rcases v with ⟨a, b⟩; cases b)) <;> rfl)

/-- Not a trap label (body lines never are one: `codeLinesE_noTrap`). -/
def NoTrapLbl (ln : Line) : Prop := ∀ n, ln ≠ .label (.trap n)

theorem loadConst64_ins (rd : Reg) (v : Nat) : ∀ ln ∈ loadConst64 rd v, ∃ i t, ln = .ins i t := by
  intro ln h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with rfl | ⟨j, _, hj⟩
  · exact ⟨_, _, rfl⟩
  · split at hj
    · simp only [Option.some.injEq] at hj; exact ⟨_, _, hj.symm⟩
    · cases hj

theorem lines_noTrap {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : ∀ ln ∈ ls, NoTrapLbl ln := by
  have hmf : ∀ mm b pre am, memFinalize c mm b = .ok (pre, am) → ∀ ln ∈ pre, NoTrapLbl ln := by
    intro mm b pre am hm ln hln n e
    subst e
    unfold memFinalize at hm
    have hfin : ∀ (base : Reg) (off : Int) pre am,
        (match simm9? off with
          | some s => (([] : List Line), AMode.unscaled base s)
          | none => match uimm12Scaled? off b with
            | some o => ([], .unsignedOffset base o)
            | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)) = (pre, am) →
        Line.label (.trap n) ∉ pre := by
      intro base off pre am e hin
      split at e
      · cases e; simp at hin
      · split at e
        · cases e; simp at hin
        · cases e
          obtain ⟨i, t, hi⟩ := loadConst64_ins _ _ _ hin
          cases hi
    split at hm <;> simp only [pure, Except.pure, Except.ok.injEq] at hm <;>
      first | exact hfin _ _ _ _ hm hln | (cases hm; simp at hln) | cases hm
  have hmf' : ∀ mm b v, memFinalize c mm b = .ok v → ∀ ln ∈ v.1, NoTrapLbl ln :=
    fun mm b v hv => hmf mm b v.1 v.2 hv
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals intro ln hln n e; subst e
  all_goals simp [MInst.lines.addOff, rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead] at hln
  all_goals first
    | exact hmf' _ _ _ ‹memFinalize _ _ _ = _› _ hln _ rfl
    | (rcases hln with hln | hln
       · exact hmf' _ _ _ ‹memFinalize _ _ _ = _› _ hln _ rfl
       · first
          | ((repeat' (split at hln)) <;> simp at hln; done)
          | (simp [throw, throwThe, MonadExceptOf.throw] at *; done))

theorem codeLinesE_noTrap {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af code ps = .ok (ls, ps') → ∀ ln ∈ ls, NoTrapLbl ln
  | [], ps, ps', ls, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; simp
  | a :: as, ps, ps', ls, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro ln hln
        rcases List.mem_append.1 hln with hln | hln
        · cases a with
          | inst m => exact lines_noTrap hr ln hln
          | prologue =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            intro n e; subst e
            simp only [prologueLines] at hln
            split at hln
            · have h1 := hln
              simp at h1
              obtain ⟨-, h1⟩ := h1
              split at h1
              · simp at h1
              · rcases List.mem_append.1 h1 with h1 | h1
                · obtain ⟨_, _, h⟩ := loadConst64_ins _ _ _ h1; cases h
                · simp at h1
            · simp at hln
          | epilogueRet =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            intro n e; subst e
            split at hln
            · simp only [epilogueLines, List.mem_append] at hln
              rcases hln with h1 | h1
              · split at h1
                · simp at h1
                · split at h1
                  · simp at h1
                  · rcases List.mem_append.1 h1 with h1 | h1
                    · obtain ⟨_, _, h⟩ := loadConst64_ins _ _ _ h1; cases h
                    · simp at h1
              · simp at h1
            · simp at hln
        · exact codeLinesE_noTrap as _ _ _ hr2 ln hln


/-- What the pipeline and the ABI entry give an activation. -/
structure RL.Wf (R : RL) : Prop where
  check : AllocChecked R.vc R.rf
  alloc : lowerRFunc R.vc R.rf = .ok R.af
  emit : emitFunc R.fa.k R.af = .ok R.fa
  layout : R.fa.layout = .ok R.fb
  lm : labelOffsets R.fa.lines = .ok R.lm
  fit : 4 * R.fb.words.size ≤ 2 ^ 64
  stack : StackAvail R.K R.af R.s0
  /-- `psF` is the emitter's final state -/
  psF : ∃ body, blocksLinesE R.ctx R.af R.af.blocks.toList {} = .ok (body, R.psF)
  /-- the entry state holds the function's program -/
  prog0 : R.s0.program = R.fb.program R.base
  /-- the kept addresses are not in the frame or the callees' dead stack -/
  gfree : ∀ a, R.G a → ¬ StackBelow (frameDrop R.af + R.K) (spv R.s0) a

/-- The activation's frame is laid out correctly (its slots in the frame addresses `frameF`). -/
theorem RL.frameOkF {R : RL} (hR : R.Wf) :
    FrameOk R.fr (Live R.rf) (R.rf.floatMove = true) R.spB
      (frameF R.fr.intBase R.fr.size R.af R.s0) := by
  obtain ⟨⟨hfs, -⟩, hfr, -⟩ := lowerRFunc_ok hR.alloc
  have hlt' : (spv R.s0).toNat < 18446744073709551616 := (spv R.s0).isLt
  have hle : R.fr.size ≤ R.fr.total := compute_size_le_total R.vc R.rf
  have hst := hR.stack.frame.1
  have hst' : R.fr.total + 16 ≤ (spv R.s0).toNat := by rw [hfs] at hst; exact hst
  by_cases h0 : R.fr.total = 0
  · -- empty frame: no live slot has an offset below `size`
    refine frameOk_compute R.vc R.rf R.spB _ (by simp only [RL.fr] at h0 hle; omega) ?_
    intro o _ ho; simp only [RL.fr] at h0 hle; omega
  · have hframe := hfr h0
    have hd : frameDrop R.af = R.fr.total + 16 := by
      simp only [frameDrop, hframe, ite_true, hfs, RL.fr]
    have hsp : R.spB.toNat = (spv R.s0).toNat - (R.fr.total + 16) := by
      simp only [RL.spB, hd]
      have hm : (R.fr.total + 16) % 2 ^ 64 = R.fr.total + 16 := Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_sub_of_le] <;> simp only [BitVec.le_def, BitVec.toNat_ofNat, hm, RL.fr] at * <;> omega
    refine frameOk_compute R.vc R.rf R.spB _ (by simp only [RL.fr] at hsp hle ⊢; omega) ?_
    intro o hlo hhi
    simp only [frameF, ← RL.spB.eq_def]
    have h1 : o < R.fr.total := Nat.lt_of_lt_of_le hhi (compute_size_le_total R.vc R.rf)
    have : (R.spB + BitVec.ofNat 64 o - R.spB).toNat = o := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp; omega
    simp only [RL.spB] at this ⊢
    rw [this]
    exact .inl ⟨hlo, hhi⟩

theorem FrameOk.mono {fr : RAFrame} {D : Loc → Prop} {T : Prop} {sp0 : BitVec 64}
    {F F' : BitVec 64 → Prop} (h : FrameOk fr D T sp0 F) (hF : ∀ a, F a → F' a) :
    FrameOk fr D T sp0 F' :=
  ⟨h.sep, fun l o hl ho k hk => hF _ (h.inF l o hl ho k hk), h.tmpSep,
    fun hT k hk => hF _ (h.tmpF hT k hk)⟩

/-- The activation's frame is laid out correctly (its slots in the frame addresses `R.FK`). -/
theorem RL.frameOkK {R : RL} (hR : R.Wf) :
    FrameOk R.fr (Live R.rf) (R.rf.floatMove = true) R.spB R.FK :=
  (RL.frameOkF hR).mono fun _ h => .inl h

/-- The frame addresses are outside the world. -/
theorem RL.FK_F {R : RL} {a : BitVec 64} (h : R.FK a) : R.F a :=
  h.elim (fun h => .inl (.inl h)) .inr

/-- The callees' dead stack is outside the world. -/
theorem RL.below_F {R : RL} {a : BitVec 64} (h : StackBelow R.K R.spB a) : R.F a := .inl (.inr h)

/-- The activation's slots lie outside the world. -/
theorem RL.frameOk {R : RL} (hR : R.Wf) :
    FrameOk R.fr (Live R.rf) (R.rf.floatMove = true) R.spB R.F :=
  (RL.frameOkK hR).mono fun _ => RL.FK_F

/-- The allocator's slots lie inside the dropped frame. -/
theorem RL.size_le_drop {R : RL} (hR : R.Wf) : R.fr.size ≤ frameDrop R.af := by
  obtain ⟨⟨hfs, -⟩, hfr, -⟩ := lowerRFunc_ok hR.alloc
  have hle : R.fr.size ≤ R.fr.total := compute_size_le_total R.vc R.rf
  by_cases h0 : R.fr.total = 0
  · simp only [RL.fr] at h0 hle ⊢; omega
  · have hframe := hfr h0
    simp only [frameDrop, hframe, ite_true, hfs]
    simp only [RL.fr] at hle ⊢; omega

/-- **The frame is not in the dead stack.** -/
theorem RL.FK_not_below {R : RL} (hR : R.Wf) {a : BitVec 64} (h : R.FK a) :
    ¬ StackBelow R.K R.spB a := by
  rcases h with h | h
  · exact frameF_not_below hR.stack (RL.size_le_drop hR) h
  · rintro ⟨h1, h2⟩
    obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
    simp only [RL.spB] at h1 h2
    rw [hB] at h1 h2
    exact hR.gfree a h ⟨by omega, by omega⟩

/-- The kept addresses are not in the frame's slot area. -/
theorem RL.G_not_slot {R : RL} (hR : R.Wf) {a : BitVec 64} (h : R.G a) :
    ∀ o, o < R.fr.size → a ≠ R.spB + BitVec.ofNat 64 o := by
  intro o ho e
  have hd := RL.size_le_drop hR
  obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
  apply hR.gfree a h
  subst e
  simp only [RL.spB] at hB ⊢
  have : (spv R.s0 - BitVec.ofNat 64 (frameDrop R.af) + BitVec.ofNat 64 o).toNat =
      (spv R.s0).toNat - frameDrop R.af + o := by
    rw [BitVec.toNat_add, hB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_eq_of_lt (by have := (spv R.s0).isLt; omega)
  simp only [StackBelow, this]
  omega

/-- The callees' budget fits below the body's `sp`. -/
theorem RL.K_le {R : RL} (hR : R.Wf) : R.K ≤ R.spB.toNat := by
  obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
  simp only [RL.spB]
  omega

/-- **A call at the body's `sp`**: the callee's contract (`CallSoundCtl` with the activation's
budget) gives the operand-view obligation at the state, keeping the frame `R.FK`. -/
theorem RL.callAt {R : RL} (hR : R.Wf) {exec : MInst → Arm.ArmState → Option Arm.ArmState}
    {sem : ISem CV Arm.ArmState} {i : MInst} {ctl : Ctl} (h : CallSoundCtl R.F R.K exec sem i ctl)
    {s : Arm.ArmState} (hsp : spOf s = R.spB) : OperandsSoundCtlAt R.F R.FK exec sem i ctl s := by
  refine (h s (by rw [hsp]; exact RL.K_le hR) (fun a ha => ?_)).mono fun a ha => ⟨RL.FK_F ha, ?_⟩
  · rw [hsp] at ha; exact RL.below_F ha
  · rw [hsp]; exact RL.FK_not_below hR ha

/-- `RL.callAt` for the contract relative to the kept addresses (`CallSoundCtlG`): the state
keeps `G` (`StRel.gkeep`); the allocated instructions `P` are at the pc. -/
theorem RL.callAtG {R : RL} (hR : R.Wf) {exec : MInst → Arm.ArmState → Option Arm.ArmState}
    {sem : ISem CV Arm.ArmState} {i : MInst} {ctl : Ctl}
    (h : CallSoundCtlG R.F R.K R.G R.s0 (CallAt R.fa R.base) exec sem i ctl)
    {s : Arm.ArmState} (hsp : spOf s = R.spB) (hg : ∀ a, R.G a → s.mem a = R.s0.mem a)
    {P : MInst → Prop} (hpc : ∀ i', P i' → CallAt R.fa R.base (Arm.r .PC s) i') :
    OperandsSoundCtlAtI R.F R.FK P exec sem i ctl s := by
  refine (h s (by rw [hsp]; exact RL.K_le hR) (fun a ha => ?_) hg).mono hpc
    fun a ha => ⟨RL.FK_F ha, ?_⟩
  · rw [hsp] at ha; exact RL.below_F ha
  · rw [hsp]; exact RL.FK_not_below hR ha


theorem mem_blocks_flat {rf : RFunc} {b : Nat} {items : Array RItem} {it : RItem}
    (hb : rf.blocks[b]? = some items) (hi : it ∈ items.toList) :
    it ∈ rf.blocks.foldl (· ++ ·) #[] := by
  have e := Array.foldl_append_eq_append (xs := rf.blocks) (f := id) (ys := (#[] : Array RItem))
  simp only [id] at e
  rw [e]
  simp only [Array.empty_append, Array.mem_flatten, Array.map_id_fun, id]
  exact ⟨items, Array.mem_of_getElem? hb, by simpa using hi⟩

/-- A move of the checked allocated code: checked, between live locations. -/
theorem move_facts {R : RL} {b : Nat} {vb : VBlock} {items : Array RItem} {pre its : List RItem}
    {src dst : Loc} (hit : R.rf.blocks[b]? = some items)
    (hsplit : items.toList = pre ++ .move src dst :: its)
    (hchk : ItemsChecked R vb (.move src dst :: its)) :
    (∃ (c : CheckCtx) (wh : String), c.checkMove wh src dst = .ok ()) ∧
      Live R.rf src ∧ Live R.rf dst ∧
      (∀ a b, src = .reg (.v a) → dst = .reg (.v b) → R.rf.floatMove = true) ∧
      ItemsChecked R vb its := by
  obtain ⟨c, k, a, out, hcr, hcv, hrun⟩ := hchk
  simp only [CheckCtx.runItems, bind, Except.bind] at hrun
  obtain ⟨-, hrun⟩ := Except.seq_ok hrun
  simp only [CheckCtx.stepMove, bind, Except.bind] at hrun
  split at hrun
  · cases hrun
  rename_i a' hsm
  obtain ⟨hcm, -⟩ := Except.seq_ok hsm
  have hmem : RItem.move src dst ∈ R.rf.blocks.foldl (· ++ ·) #[] :=
    mem_blocks_flat hit (by rw [hsplit]; simp)
  obtain ⟨cls, hcls, hs, hd, -⟩ := checkMove_facts hcm
  have live : ∀ l, (l = src ∨ l = dst) → c.locOk l cls = true → Live R.rf l := by
    intro l hl hok
    unfold CheckCtx.locOk at hok
    simp only [Bool.and_eq_true] at hok
    cases l with
    | reg r => trivial
    | save r => trivial
    | stack k' cl =>
      rw [hcr] at hok
      cases cl with
      | int => simpa [Live] using hok.2
      | float =>
        refine ⟨by simpa using hok.2, ?_⟩
        unfold RFunc.floatStack
        rw [Array.any_eq_true']
        refine ⟨_, hmem, ?_⟩
        rcases hl with rfl | rfl <;> simp [RItem.locs]
  refine ⟨⟨c, _, hcm⟩, live _ (.inl rfl) hs, live _ (.inr rfl) hd, fun a b ha hb => ?_,
    ⟨c, k, a', out, hcr, hcv, hrun⟩⟩
  subst ha hb
  unfold RFunc.floatMove
  rw [Array.any_eq_true']
  exact ⟨_, hmem, rfl⟩


theorem oneLine_of_moveInst (ctx : FnCtx) {i : MInst} (h : MoveInst i) : OneLine ctx i := by
  rcases h with ⟨a, b, rfl⟩ | ⟨cls, r, off, h8, h16, hoff, rfl | rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | rfl |
    ⟨op, r, rfl⟩ | ⟨op, r, rfl⟩
  · exact oneLine_mov ctx a b
  · exact oneLine_slotStore ctx cls r h8 h16 hoff
  · exact oneLine_slotLoad ctx cls r h8 h16 hoff
  · exact oneLine_movz ctx c
  · exact oneLine_movk ctx c
  · exact oneLine_add_sp_x16 ctx
  · exact oneLine_store_x16 ctx op r
  · exact oneLine_load_x16 ctx op r

theorem itemCode_move (fr : RAFrame) (vb : VBlock) (src dst : Loc) :
    itemCode fr vb (.move src dst) = fr.moveInsts src dst := by
  unfold itemCode itemStep
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Array.empty_append]
  generalize fr.moveInsts src dst = x
  cases x <;> simp

/-- The fp/lr slot lies above the frame's slot area. -/
theorem fplr_outside {R : RL} (hR : R.Wf) (hframe : R.af.frame = true) :
    ∀ k < 16, ∀ o, o < R.fr.size → spv R.s0 - 16#64 + BitVec.ofNat 64 k ≠ R.spB + BitVec.ofNat 64 o := by
  obtain ⟨⟨hfs, -⟩, -⟩ := lowerRFunc_ok hR.alloc
  have hlt' : (spv R.s0).toNat < 18446744073709551616 := (spv R.s0).isLt
  have hle : R.fr.size ≤ R.fr.total := compute_size_le_total R.vc R.rf
  have hst := hR.stack.frame.1
  have hst' : R.fr.total + 16 ≤ (spv R.s0).toNat := by rw [hfs] at hst; exact hst
  have hd : frameDrop R.af = R.fr.total + 16 := by
    simp only [frameDrop, hframe, ite_true, hfs, RL.fr]
  intro k hk o ho e
  have := congrArg BitVec.toNat e
  simp only [RL.spB, hd] at this
  have hm : (R.fr.total + 16) % 2 ^ 64 = R.fr.total + 16 := Nat.mod_eq_of_lt (by omega)
  rw [hfs] at hst
  simp only [RL.fr] at *
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub_of_le, BitVec.toNat_sub_of_le] at this
  · simp only [BitVec.toNat_ofNat, hm] at this
    rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := o) (by omega)] at this
    have h1 := (spv R.s0).isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · simp only [BitVec.le_def, BitVec.toNat_ofNat, hm]; omega
  · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega

/-- The code lies outside the frame's slot area. -/
theorem code_outside {R : RL} (hR : R.Wf) {a : BitVec 64} (ha : CodeAddr R.s0 a) :
    ∀ o, o < R.fr.size → a ≠ R.spB + BitVec.ofNat 64 o := by
  obtain ⟨⟨hfs, -⟩, hfr, -⟩ := lowerRFunc_ok hR.alloc
  have hlt' : (spv R.s0).toNat < 18446744073709551616 := (spv R.s0).isLt
  have hle : R.fr.size ≤ R.fr.total := compute_size_le_total R.vc R.rf
  have hst := hR.stack.frame.1
  have hap := hR.stack.frame.2 a ha
  intro o ho e
  by_cases h0 : R.fr.total = 0
  · simp only [RL.fr] at h0 hle ho; omega
  have hframe := hfr h0
  have hd : frameDrop R.af = R.fr.total + 16 := by
    simp only [frameDrop, hframe, ite_true, hfs, RL.fr]
  rw [hfs] at hst hap
  simp only [RL.spB, hd, RL.fr] at e hap hst
  rw [e, BitVec.add_comm, BitVec.add_sub_cancel] at hap
  simp only [BitVec.toNat_ofNat] at hap
  simp only [RL.fr] at ho hle
  rw [Nat.mod_eq_of_lt (by omega)] at hap
  omega

/-- The code is kept by a store to the frame's slot area. -/
theorem code_frameKeep {R : RL} (hR : R.Wf) {s s' : Arm.ArmState}
    (hm : ∀ a, (∀ o, o < R.fr.size → a ≠ R.spB + BitVec.ofNat 64 o) → s'.mem a = s.mem a)
    (hc : ∀ k w, R.fb.words[k]? = some w → Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    ∀ k w, R.fb.words[k]? = some w → Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s' = w :=
  code_keep hR.prog0 hc fun a ha => hm a (code_outside hR ha)

/-- **After a line that is no call, no return into the code**: a state at the line after an
instruction line other than `bl`/`blr` satisfies `RL.Good`. -/
theorem RL.good_succ {R : RL} (hR : R.Wf) {j : Nat} {x : Insn} {t : Option Clif.TrapCode}
    (hj : R.L[j]? = some (.ins x t)) (hx : ∀ n, x ≠ .bl n) (hx' : ∀ r, x ≠ .blr r)
    {u : Arm.ArmState} (hpc : Arm.r .PC u = R.pcOf (j + 1)) : R.Good u := by
  left
  rintro ⟨q, ⟨j', i', t', hj', hcall, rfl⟩, he⟩
  rw [hpc] at he
  simp only [RL.pcOf, RL.L] at he hj
  have hsz : (R.fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hR.layout]; exact hR.fit
  have hl1 := lineOffset_le_size R.fa.lines.toList (j + 1)
  have hl2 := lineOffset_le_size R.fa.lines.toList (j' + 1)
  have hs1 := lineOffset_succ R.fa.lines.toList j _ hj
  have hs2 := lineOffset_succ R.fa.lines.toList j' _ hj'
  simp only [Line.size] at hs1 hs2
  rw [BitVec.add_assoc] at he
  have he2 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he)
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h4] at he2
  have he3 : lineOffset R.fa.lines.toList j = lineOffset R.fa.lines.toList j' := by
    rw [hs1] at he2 hl1
    omega
  have := lineOffset_inj hj hj' he3
  subst this
  rw [hj] at hj'
  cases hj'
  rcases hcall with ⟨n, rfl⟩ | ⟨r, rfl⟩
  · exact hx n rfl
  · exact hx' r rfl

/-- A state with the body's `sp` satisfies `RL.Good`. -/
theorem RL.good_of_sp {R : RL} {u : Arm.ArmState} (h : spOf u = R.spB) : R.Good u := .inr h

theorem Insn.not_call_of_hooked {x : Insn} (h : x.hooked = false) :
    (∀ n, x ≠ .bl n) ∧ (∀ r, x ≠ .blr r) :=
  ⟨fun n e => by subst e; simp [Insn.hooked] at h, fun r e => by subst e; simp [Insn.hooked] at h⟩

theorem execLines_ins : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState},
    execLines env ls s = some s' → ∀ ln ∈ ls, ∃ x t, ln = .ins x t
  | _, [], _, _, _, _, h => by simp at h
  | _, .label _ :: _, _, _, h, _, _ => by simp [execLines] at h
  | _, .word _ _ :: _, _, _, h, _, _ => by simp [execLines] at h
  | env, .ins i t :: ls, s, s', h, ln, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨i, t, rfl⟩
    · simp only [execLines] at h
      split at h
      · split at h
        · exact execLines_ins h ln hm
        · cases h
      · cases h

/-- **The states of a straight-line run** (unhooked instruction lines) after its first are no
return into the code. -/
theorem RL.good_execLines {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s') :
    ∀ i, 0 < i → i ≤ ls.length → R.Good (iterN R.step i s) := by
  intro i hi0 hi
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls j s s' hat hhook
    hprog hpc herr hinter hrun i hi
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨ln, hln⟩ : ∃ ln, ls[i']? = some ln := ⟨ls[i'], List.getElem?_eq_getElem (by omega)⟩
  have hj := hat i' ln hln
  obtain ⟨x, t, rfl⟩ := execLines_ins hrun ln (List.mem_of_getElem? hln)
  obtain ⟨hx, hx'⟩ := Insn.not_call_of_hooked (hhook x t (List.mem_of_getElem? hln))
  have hpcs' : Arm.r .PC (iterN R.step (i' + 1) s) = R.pcOf (j + i' + 1) := hpcs
  exact R.good_succ hR (j := j + i') hj hx hx' hpcs'

/-- **A move on the machine**: from `Q` at a move item, the machine runs the move's lines and
reaches `Q` at the next item with `MStep.move`'s store. -/
theorem realizes_move {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b : Nat} {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .move src dst :: its, m, w⟩)) :
    ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, upd m dst (m src), w⟩) ∧
      ∀ i < n, R.Good (iterN R.step i s) := by
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
  have hdrop' : R.L.drop j = ls1' ++ (ftList (ls2 ++ nxtOf R.af b) ++ T) := by
    rw [hdrop, List.append_assoc, ftList_plain_append _ _ hpl hZ, List.append_assoc]
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
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact RL.good_of_sp hst.sp
    · exact R.good_execLines hR hat
        (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
        (by rw [hst.prog]) hpc hst.err (hint _) (hrun _) i hi0 (by omega)
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

end Backend.Proof

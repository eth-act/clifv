import FV.E2E.RegLevelSim
import FV.Backend.Proof.RegallocMoves

/-!
# Moves on the machine (M6)

The code of a move (`RAFrame.moveInsts`) consists of one-line instructions (`OneLine`: `mov`,
slot stores and loads of a frame below 32 KiB); `run_oneLines` turns their `ExecAll` run into
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

/-- The expansion of an instruction other than `trapIf`/`jtSequence` does not depend on the
emitter state. -/
theorem lines_ps (c : FnCtx) (m : MInst) (ps : PState)
    (h1 : ∀ k code, m ≠ .trapIf k code) (h2 : ∀ a b d e f, m ≠ .jtSequence a b d e f) :
    m.lines c ps = (fun p => (p.1, ps)) <$> m.lines c {} := by
  cases m
  all_goals first
    | (exfalso; exact h1 _ _ rfl)
    | (exfalso; exact h2 _ _ _ _ _ rfl)
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
  all_goals simp [MInst.lines.addOff] at hln
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
            split at hln <;> simp [epilogueLines] at hln <;> done
        · exact codeLinesE_noTrap as _ _ _ hr2 ln hln

end Backend.Proof

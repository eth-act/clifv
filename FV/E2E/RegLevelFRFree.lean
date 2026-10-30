import FV.E2E.RegLevelSegAlign

/-!
# The segments of the body run no frame-record line and no `ret` (SEM1 #537, `docs/plans/uninit.md` §5.9, machine lock)

The machine lock of two activations (`BackendTwoRunL`) ignores `x30`; it holds across a line only
when the line is no `ret` (which jumps to `x30`) and no frame-record pair (`stp fp, lr` /
`ldp fp, lr`, which store/load `x30`). Those lines are emitted only by the prologue and the
epilogue (`prologueLines`, `epilogueLines`), never by an allocated instruction (`MInst.lines`).
The segment realising one step of an allocated configuration runs only lines of its own item
(`RL.Inside`), so it runs none of them (`RL.FRFree`).

* `Insn.frLine`, `RL.FRFree`;
* `frLine_lines` (no allocated instruction's lines hold one), `frLine_codeLinesE`;
* `RL.frFree_zero`, `RL.frFree_of`, `RL.frFree_inside`, `RL.frFree_one`.
-/

namespace Backend.Proof

open Backend E2E

/-- **The frame-record pair and `ret`**: the instructions the lock cannot step (any `stp`/`ldp`:
only the frame record's are ever emitted). -/
def _root_.Backend.Insn.frLine : Insn → Bool
  | .ret | .stp .. | .ldp .. => true
  | _ => false

/-- **No state of the run from `s` before step `n` is at a frame-record line or a `ret`** of the
activation. -/
def RL.FRFree (R : RL) (s : Arm.ArmState) (n : Nat) : Prop :=
  ∀ i < n, ∀ x, R.AtLine (iterN R.step i s) x → x.frLine = false

theorem frLine_loadConst64 (rd : Reg) (v : Nat) :
    ∀ x t, Line.ins x t ∈ loadConst64 rd v → x.frLine = false := by
  intro x t h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at h
  rcases h with h | ⟨j, -, h⟩
  · cases h; rfl
  · split at h <;> cases h; rfl

theorem memFinalize_preFR {c : FnCtx} {m : AMode} {n : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m n = .ok (pre, m')) : pre = [] ∨ ∃ v, pre = loadConst64 (.x 16) v := by
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;>
    first
    | exact .inl (Prod.mk.inj h).1.symm
    | exact .inr ⟨_, (Prod.mk.inj h).1.symm⟩

theorem frLine_memFinalize {c : FnCtx} {m : AMode} {n : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m n = .ok (pre, m')) : ∀ x t, Line.ins x t ∈ pre → x.frLine = false := by
  rcases memFinalize_preFR h with rfl | ⟨v, rfl⟩
  · intro x t h; cases h
  · exact frLine_loadConst64 _ _

theorem frLine_rmwLoopCmp (op : AtomicRmwLoopOp) (b : Nat) : (rmwLoopCmp op b).frLine = false := by
  unfold rmwLoopCmp; split <;> rfl

theorem frLine_casLoopCmp (b : Nat) : (casLoopCmp b).frLine = false := by
  unfold casLoopCmp; split <;> rfl

theorem frLine_rmwLoopSext {b : Nat} {a : Insn} (h : a ∈ rmwLoopSext b) : a.frLine = false := by
  unfold rmwLoopSext at h; split at h <;> simp at h <;> (subst h; rfl)

theorem frLine_rmwLoopMid {op : AtomicRmwLoopOp} {b : Nat} {a : Insn} (h : a ∈ rmwLoopMid op b) :
    a.frLine = false := by
  revert h
  cases op <;> simp only [rmwLoopMid, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] <;> intro h <;>
    first
    | (subst h; rfl)
    | (rcases h with h | h <;> first | (subst h; rfl) | (subst h; exact frLine_rmwLoopCmp _ _))
    | (rcases h with h | h | h <;>
        first | exact frLine_rmwLoopSext h | (subst h; rfl) | (subst h; exact frLine_rmwLoopCmp _ _))
    | (rcases h with h | h | h <;> first | (subst h; rfl) | (rcases h with h | h <;> subst h <;> rfl))

theorem frLine_kind (k : CondBrKind) (l : Lbl) : (k.insn l).frLine = false := by
  cases k <;> rfl

theorem throw_ne_okFR {α : Type} (e : String) (v : α) : (throw e : Except String α) ≠ .ok v :=
  fun h => nomatch h

/-- **No allocated instruction's lines hold a frame-record line or a `ret`.** -/
theorem frLine_lines {c : FnCtx} {m : MInst} {ps ps' : Backend.PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : ∀ x t, Line.ins x t ∈ ls → x.frLine = false := by
  cases m <;> simp only [MInst.lines, pure, Except.pure, bind, Except.bind] at h
  all_goals (repeat' split at h)
  all_goals (first | cases h | skip)
  all_goals (try (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h))
  all_goals (try have hpre := frLine_memFinalize ‹memFinalize _ _ _ = _›)
  all_goals (try unfold MInst.lines.addOff)
  all_goals (try split)
  all_goals (try split)
  all_goals (simp only [rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead, List.mem_cons,
    List.mem_append, List.mem_map, List.not_mem_nil, or_false, Line.ins.injEq, reduceCtorEq,
    false_or, List.cons_append, List.nil_append, or_imp, and_imp, forall_and, forall_eq',
    forall_exists_index, implies_true, and_true, true_and, imp_false, not_and])
  all_goals (repeat' apply And.intro)
  all_goals (first
    | rfl
    | exact frLine_kind _ _
    | exact frLine_rmwLoopCmp _ _
    | exact frLine_casLoopCmp _
    | exact hpre
    | (intro x t hx; exact hpre _ _ hx)
    | (intro a ha; exact frLine_rmwLoopMid ha)
    | (intro a ha _; exact frLine_rmwLoopMid ha)
    | (intro x t a ha hx _; rw [← hx]; exact frLine_rmwLoopMid ha)
    | (intro x t l _ hf; exact hf.elim)
    | (intro x t hx; exact hx.elim)
    | (exact absurd ‹throw _ = Except.ok _› (throw_ne_okFR _ _))
    | (intro x t hx _; rw [hx]; first
        | rfl
        | exact frLine_kind _ _
        | exact frLine_casLoopCmp _
        | exact frLine_rmwLoopCmp _ _))

/-- **The lines of a code of `inst` items hold no frame-record line and no `ret`.** -/
theorem frLine_codeLinesE {c : FnCtx} {af : AFunc} {code : List AInst} {ps ps' : Backend.PState}
    {ls : List Line} (hinst : ∀ a ∈ code, ∃ m, a = .inst m)
    (h : codeLinesE c af code ps = .ok (ls, ps')) : ∀ x t, Line.ins x t ∈ ls → x.frLine = false := by
  induction code generalizing ps ls ps' with
  | nil =>
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro x t hx; cases hx
  | cons a as ih =>
    obtain ⟨m, rfl⟩ := hinst a (by simp)
    simp only [ainstLines, codeLinesE, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v hl1
      split at h
      · simp at h
      · rename_i v' hl2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro x t hx
        rcases List.mem_append.1 hx with hx | hx
        · exact frLine_lines hl1 x t hx
        · exact ih (fun b hb => hinst b (List.mem_cons_of_mem _ hb)) hl2 x t hx

theorem RL.frFree_zero (R : RL) (s : Arm.ArmState) : R.FRFree s 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-- **`FRFree` from the lines of the states.** -/
theorem RL.frFree_of {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n : Nat}
    (h : ∀ i < n, ∃ jj x t, R.L[jj]? = some (.ins x t) ∧
      Arm.r .PC (iterN R.step i s) = R.pcOf jj ∧ x.frLine = false) : R.FRFree s n := by
  intro i hi x ⟨j', t', hj', hpc'⟩
  obtain ⟨jj, y, t, hjj, hpc, hy⟩ := h i hi
  obtain rfl := RL.pcOf_inj hR hj' hjj (hpc'.symm.trans hpc)
  rw [hjj] at hj'
  cases hj'
  exact hy

/-- A line of `R.L` in the range of lines `ls` at `j` is a line of `ls`. -/
theorem RL.mem_of_drop {R : RL} {j : Nat} {ls T : List Line} (hd : R.L.drop j = ls ++ T)
    {jj : Nat} {ln : Line} (h : R.L[jj]? = some ln) (h1 : j ≤ jj) (h2 : jj < j + ls.length) :
    ln ∈ ls := by
  have := congrArg (·[jj - j]?) hd
  simp only [List.getElem?_drop, show j + (jj - j) = jj by omega, h] at this
  rw [List.getElem?_append_left (by omega)] at this
  exact List.mem_of_getElem? this.symm

/-- **A segment inside the lines `ls` at `j`** (`RL.Inside` up to `lim ≤ j + ls.length`, the
first state at line `j`) **runs no frame-record line and no `ret`** when `ls` holds none. -/
theorem RL.frFree_inside {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n j lim : Nat}
    {ls T : List Line} (hd : R.L.drop j = ls ++ T) (hlim : lim ≤ j + ls.length)
    (hls : ∀ x t, Line.ins x t ∈ ls → x.frLine = false) (hpc : Arm.r .PC s = R.pcOf j)
    (h0 : 0 < n → j < lim ∧ ∃ x t, R.L[j]? = some (.ins x t)) (hin : R.Inside s n j lim) :
    R.FRFree s n := by
  apply RL.frFree_of hR
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · obtain ⟨hjl, x, t, hj⟩ := h0 hi
    exact ⟨j, x, t, hj, hpc, hls x t (RL.mem_of_drop hd hj (Nat.le_refl _) (by omega))⟩
  · obtain ⟨jj, x, t, h1, h2, h3, h4⟩ := hin i hi0 hi
    exact ⟨jj, x, t, h3, h4, hls x t (RL.mem_of_drop hd h3 (by omega) (by omega))⟩

/-- **A one-step segment at an instruction line `j`** that is no frame-record line or `ret`. -/
theorem RL.frFree_one {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n j : Nat} (hn : n ≤ 1)
    {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hx : x.frLine = false)
    (hpc : Arm.r .PC s = R.pcOf j) : R.FRFree s n :=
  RL.frFree_of hR fun i hi => by
    obtain rfl : i = 0 := by omega
    exact ⟨j, x, t, hj, hpc, hx⟩

theorem frLine_invertTo (l : Lbl) (c : Insn) : (c.invertTo l).frLine = c.frLine := by
  cases c <;> rfl

/-- **Relaxing a line keeps it free of frame-record lines and `ret`.** -/
theorem frLine_relaxLine (far : Lbl → Bool) {ln : Line}
    (h : ∀ x t, ln = .ins x t → x.frLine = false) :
    ∀ y t, Line.ins y t ∈ relaxLine far ln → y.frLine = false := by
  intro y t hy
  unfold relaxLine at hy
  split at hy
  · rename_i c tg hr
    have hln : ln = .ins c none := by
      unfold Line.relaxable? at hr
      split at hr
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hr
        obtain ⟨_, -, rfl, -⟩ := hr
        rfl
      · cases hr
    have hc := h c none hln
    split at hy
    · simp only [List.mem_cons, Line.ins.injEq, List.not_mem_nil, or_false] at hy
      rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [frLine_invertTo]; exact hc
      · rfl
    · rw [List.mem_singleton] at hy
      exact h y t hy.symm
  · rw [List.mem_singleton] at hy
    exact h y t hy.symm

theorem frLine_relaxLines (far : Lbl → Bool) {ls : List Line}
    (h : ∀ x t, Line.ins x t ∈ ls → x.frLine = false) :
    ∀ y t, Line.ins y t ∈ relaxLines far ls → y.frLine = false := by
  intro y t hy
  simp only [relaxLines, List.mem_flatMap] at hy
  obtain ⟨ln, hln, hy⟩ := hy
  exact frLine_relaxLine far (fun x t' e => h x t' (e ▸ hln)) y t hy

/-- The first line of a relaxed instruction line is an instruction line. -/
theorem relaxLine_ins_head (far : Lbl → Bool) (x : Insn) (t : Option Clif.TrapCode) :
    ∃ y t', (relaxLine far (.ins x t))[0]? = some (.ins y t') := by
  unfold relaxLine
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- **A segment of at most one step at the first line of `ls`**, an instruction line. -/
theorem RL.frFree_head {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n j : Nat} (hn : n ≤ 1)
    {ls T : List Line} (hd : R.L.drop j = ls ++ T)
    (hls : ∀ x t, Line.ins x t ∈ ls → x.frLine = false) (hpc : Arm.r .PC s = R.pcOf j)
    (hh : ∃ y t, ls[0]? = some (.ins y t)) : R.FRFree s n := by
  obtain ⟨y, t, hy⟩ := hh
  have hj : R.L[j]? = some (.ins y t) := by
    have := congrArg (·[0]?) hd
    simp only [List.getElem?_drop, Nat.add_zero] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hy).1, hy]
  exact RL.frFree_one hR hn hj (hls y t (List.mem_of_getElem? hy)) hpc

/-- **A straight segment inside its plain lines `ls1`** at `j` runs no frame-record line and no
`ret` when `ls1` holds none. -/
theorem RL.frFree_straight {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n j : Nat} {ls1 : List Line}
    (hT : ∃ T', R.L.drop j = ls1 ++ T') (hpl : ∀ ln ∈ ls1, ln.plain = true)
    (hls : ∀ x t, Line.ins x t ∈ ls1 → x.frLine = false) (hpc : Arm.r .PC s = R.pcOf j)
    (hin : R.Inside s n j (j + ls1.length)) (hn0 : n = 0 ↔ ls1 = []) : R.FRFree s n := by
  obtain ⟨T', hd⟩ := hT
  refine RL.frFree_inside hR hd (Nat.le_refl _) hls hpc (fun h0 => ?_) hin
  have hne : ls1 ≠ [] := fun he => absurd (hn0.mpr he) (by omega)
  obtain ⟨ln, lt, hcons⟩ := List.exists_cons_of_ne_nil hne
  have hj0 : R.L[j]? = some ln := by
    have := congrArg (·[0]?) hd
    simp only [List.getElem?_drop, Nat.add_zero, hcons, List.cons_append,
      List.getElem?_cons_zero] at this
    exact this
  have hpln := hpl ln (by rw [hcons]; exact List.mem_cons_self ..)
  refine ⟨by rw [hcons]; simp, ?_⟩
  cases ln with
  | ins x t => exact ⟨x, t, hj0⟩
  | _ => simp [Line.plain] at hpln

/-- **A one-step segment at a call line** runs no frame-record line and no `ret`. -/
theorem RL.frFree_callSt {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n : Nat} (hn : n ≤ 1)
    (hc : R.CallSt s) : R.FRFree s n := by
  intro i hi x hx
  obtain rfl : i = 0 := by omega
  obtain ⟨y, hy, hyc⟩ := RL.callSt_iff.1 hc
  obtain rfl := RL.atLine_unique hR hx hy
  rcases hyc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

end Backend.Proof

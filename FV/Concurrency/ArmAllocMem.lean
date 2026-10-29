import FV.Concurrency.ArmAllocStraight
import FV.Concurrency.IselMemAux

/-!
# Layer 4b for the memory items of the atomics scope (T2h, #311)

The per-item obligation `ArmAllocThread.ItemSim` (for `RelQ`, `SrcStep`, `Done`, `PrivA`, as
`ArmAllocStraight.itemSim_noev`) at the items with memory events, and the run level for functions
whose items are event-free or of these forms:

* `itemSim_of_op`: without moves, `ItemSim` is its instance at every instruction item with a
  source step; `noev_op`: the event-free items (`itemSim_noev`'s cases);
* `fence_op`: **`dmb ish`** (`fence`): the Arm's one step has the barrier event `dmbEv`, the
  source step's;
* `oneEv_op`: **a straight-line form with one Arm instruction** (`OneEvForm`): the Arm step's
  events on any memory are the canonical run's (**event equality**, `OneEvForm.ev`), and the
  canonical run's pc, error and program do not depend on the memory (`CtlIndep`, so the source
  step exists for every read value: **receptiveness**, `straightSem_one`); the states after
  both, patched with the Arm's read bytes, are related (`q_patch`);
* `ldar_form`, `stlr_form`: **`ldar`** (`loadAcquire`) and **`stlr`** (`storeRelease`) are such
  forms (`exclEvs_regs`: the allocated and the canonical instruction access the address
  register's value, with the data register's bytes for a store; `ctlIndep_excl`);
* `MemScope`: every instruction is event-free (`NoEvForm`, `NoEvScope`'s), `fence`, or a covered
  `ldar`/`stlr`; **`arm_alloc_refines_mem`**: such a function's precise Arm runs from
  `Q`-related states realize runs of the allocated code with `Refines (·=·) (PrivA R) (MonPair
  trT)` up to `Done` (`arm_alloc_refines_noev`'s conclusion);
* `exists_prun_line`: at an unhooked instruction line, every memory gives a precise one-step run
  (`ArmPrecise.exists_precise_step` for the machine `R.step`).
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
open Code VCodeEvents VCodeAddr

/-- The conclusion of `ItemSim` at one configuration (`Term = Done`). -/
abbrev OpOut (R : RL) (t : ArmState × Mon) (c : MConf CV ArmState) (ls : List Lab) : Prop :=
  Done R c ∨
    ItemSimOut Policy.arm R.step (fun _ _ => True) (SrcStep R) (RelQ R) (PrivA R)
      (fun c => c.measure) t c ls ∨
    (∃ evs c' φ, SrcStep R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) ∨ PrivW (PrivA R) (evTr ls)

/-! ## The pc at a line other than `ret` (#473: linked machines)

A linked machine switches programs at a callee's `ret` line; it agrees with `R.step` at every
other line. The item lemmas' `…R` versions record that a run ending inside an item ends at a line
other than `ret` (`OpOutN`), so that layer 4b holds for such machines
(`ArmAllocLinked.itemSim_transfer`). -/

/-- `ls` has no `ret` line. -/
def NoRet (ls : List Line) : Prop := ∀ x t, Line.ins x t ∈ ls → x ≠ .ret

/-- **A state at an instruction line other than `ret`**, not hooked (the machine runs its
instruction there: a linked machine agrees with `R.step`, and the program is kept). -/
def AtNonRet (R : RL) (u : ArmState) : Prop :=
  ∃ j x t, R.fa.lines.toList[j]? = some (.ins x t) ∧ x ≠ .ret ∧ x.hooked = false ∧
    Arm.r .PC u = R.pcOf j

theorem noRet_loadConst64 (rd : Reg) (v : Nat) : NoRet (loadConst64 rd v) := by
  intro x t h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at h
  rcases h with h | ⟨j, -, h⟩
  · cases h; intro h; cases h
  · split at h <;> cases h; intro h; cases h

theorem memFinalize_pre {c : FnCtx} {m : AMode} {n : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m n = .ok (pre, m')) : pre = [] ∨ ∃ v, pre = loadConst64 (.x 16) v := by
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;>
    first
    | exact .inl (Prod.mk.inj h).1.symm
    | exact .inr ⟨_, (Prod.mk.inj h).1.symm⟩

theorem noRet_memFinalize {c : FnCtx} {m : AMode} {n : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m n = .ok (pre, m')) : NoRet pre := by
  rcases memFinalize_pre h with rfl | ⟨v, rfl⟩
  · intro x t h; cases h
  · exact noRet_loadConst64 _ _

theorem throw_ne_ok {α : Type} (e : String) (v : α) : (throw e : Except String α) ≠ .ok v :=
  fun h => nomatch h

theorem rmwLoopCmp_ne_ret (op : AtomicRmwLoopOp) (b : Nat) : rmwLoopCmp op b ≠ .ret := by
  unfold rmwLoopCmp; split <;> simp

theorem rmwLoopSext_ne_ret {b : Nat} {a : Insn} (h : a ∈ rmwLoopSext b) : a ≠ .ret := by
  unfold rmwLoopSext at h; split at h <;> simp at h <;> (subst h; simp)

/-- **No allocated instruction's lines contain a `ret`** (only the epilogue does). -/
theorem noRet_lines {c : FnCtx} {m : MInst} {ps ps' : Backend.PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : NoRet ls := by
  intro x t hx hr
  subst hr
  cases m <;> simp only [MInst.lines, pure, Except.pure, bind, Except.bind] at h
  all_goals (repeat' split at h)
  all_goals (first | cases h | skip)
  all_goals (try (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h))
  all_goals (try simp [rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead, MInst.lines.addOff] at hx)
  all_goals (try (obtain hx | hx := (hx : _ ∨ _)))
  all_goals (first | exact noRet_memFinalize ‹memFinalize _ _ _ = _› _ _ hx rfl | skip)
  all_goals (try (cases ‹CondBrKind› <;> simp [CondBrKind.insn] at hx))
  all_goals (try (cases ‹AtomicRmwLoopOp› <;> simp [rmwLoopMid] at hx))
  all_goals (try (obtain ⟨h1, -⟩ := hx; unfold casLoopCmp at h1; split at h1 <;> cases h1))
  all_goals (try (split at hx <;> simp at hx))
  all_goals (try (split at hx <;> (try split at hx) <;> simp at hx))
  all_goals (try (obtain ⟨a, ha | ha | ha, rfl, -⟩ := hx))
  all_goals (try exact absurd ‹throw _ = Except.ok _› (throw_ne_ok _ _))
  all_goals first
    | exact rmwLoopSext_ne_ret ‹_› rfl
    | exact rmwLoopCmp_ne_ret _ _ ‹Insn.ret = _›.symm
    | exact rmwLoopCmp_ne_ret _ _ ‹_ = Insn.ret›
    | exact rmwLoopCmp_ne_ret _ _ hx.1
    | cases ‹Insn.ret = Insn.csel _ _ _ _›

/-- **Through straight-line lines without `ret`, every state before the last line's step is at a
line other than `ret`** (`step_execLines`'s premises). -/
theorem nonRet_execLines {R : RL} (hR : R.Wf) {ls1 : List Line} {j : Nat} {s s' : ArmState}
    (hat : ∀ k ln, ls1[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls1 → i.hooked = false)
    (hprog : s.program = R.fb.program R.base)
    (hpc : Arm.r .PC s = R.base + BitVec.ofNat 64 (lineOffset R.fa.lines.toList j))
    (herr : Arm.r .ERR s = .None)
    (hinter : InterOk ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ ls1 s)
    (hrun : execLines ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ ls1 s = some s')
    (hnr : NoRet ls1) : ∀ i < ls1.length, AtNonRet R (iterN R.step i s) := by
  intro i hi
  obtain ⟨x, t, -, hli, -, -, -, -⟩ := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit
    hat hhook hprog hpc herr hinter hrun i hi
  exact ⟨j + i, x, t, hat i _ hli, hnr x t (List.mem_of_getElem? hli),
    hhook x t (List.mem_of_getElem? hli),
    iterN_execLines_pc hR.layout hR.lm hR.fit ls1 j s s' hat hhook hprog hpc herr hinter hrun i
      (by omega)⟩

/-- **The lines of a code of `inst` items contain no `ret`** (`noRet_lines` at every item). -/
theorem noRet_codeLinesE {c : FnCtx} {af : AFunc} {code : List AInst} {ps ps' : Backend.PState}
    {ls : List Line} (hinst : ∀ a ∈ code, ∃ m, a = .inst m)
    (h : codeLinesE c af code ps = .ok (ls, ps')) : NoRet ls := by
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
        · exact noRet_lines hl1 x t hx
        · exact ih (fun b hb => hinst b (List.mem_cons_of_mem _ hb)) hl2 x t hx

/-- **The conclusion of `ItemSim` at one configuration, runs ending inside the item at a line
other than `ret`** (`OpOut`/`OpOutG`/`OpOutR` for the steps' predicate `ok` and the measure `μ`;
`t'` the run's last state). -/
abbrev OpOutN (R : RL) (ok : ArmState → Lab → Prop) (μ : MConf CV ArmState → Nat)
    (t : ArmState × Mon) (c : MConf CV ArmState) (ls : List Lab) (t' : ArmState × Mon) : Prop :=
  Done R c ∨ ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) μ t c ls ∨
    ((∃ evs c' φ, SrcStep R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) ∧ AtNonRet R t'.1) ∨
    (PrivW (PrivA R) (evTr ls) ∧ AtNonRet R t'.1)

theorem OpOutN.out {R : RL} {ok : ArmState → Lab → Prop} {μ : MConf CV ArmState → Nat}
    {t : ArmState × Mon} {c : MConf CV ArmState} {ls : List Lab} {t' : ArmState × Mon}
    (h : OpOutN R ok μ t c ls t') :
    Done R c ∨ ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) μ t c ls ∨
      (∃ evs c' φ, SrcStep R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) ∨ PrivW (PrivA R) (evTr ls) :=
  h.imp_right (Or.imp_right (Or.imp And.left And.left))

/-- The item configuration `op k allocs` at the head of block `b`. -/
abbrev OpC (b k : Nat) (allocs : Array Loc) (its : List RItem) (m : Loc → CV) (w : ArmState) :
    MConf CV ArmState := .run ⟨b, .op k allocs :: its, m, w⟩

/-- **`ItemSim` from the instruction items**: without moves, the per-item obligation holds when
it holds at every instruction item with a source step, from `Q ∧ AInv` (the `rets` of a return
tail returns without events, `RelQ.op'`). -/
theorem itemSim_of_op {R : RL} (hnm : NoMoves R)
    (hop : ∀ s mon b k allocs its m w evs0 c0, Q R s (OpC b k allocs its m w) →
      AInv R (OpC b k allocs its m w) → SrcStep R (OpC b k allocs its m w) evs0 c0 →
      ∀ ls t', PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t' →
        OpOut R (s, mon) (OpC b k allocs its m w) ls) :
    ItemSim Policy.arm R.step (fun _ _ => True) (SrcStep R) (RelQ R) (Done R)
      (fun c => c.measure) (PrivA R) := by
  rintro ⟨s, mon⟩ c hqa ls t' hr
  match c with
  | .ret vals m w => exact .inl (.inl ⟨vals, m, w, rfl⟩)
  | .halt w => exact .inl (.inr (.inl ⟨w, rfl⟩))
  | .run ⟨b, its, m, w⟩ =>
  by_cases hS : ∃ evs c', SrcStep R (.run ⟨b, its, m, w⟩) evs c'
  case neg => exact .inl (.inr (.inr fun evs c' h => hS ⟨evs, c', h⟩))
  obtain ⟨evs0, c0, hs0⟩ := hS
  cases hs0 with
  | @move _ src dst its' =>
    obtain ⟨mt, hq⟩ := RelQ.q hqa
    obtain ⟨items, hit, hmem⟩ := q_items hq
    exact absurd (hmem _ List.mem_cons_self) (hnm b items hit src dst)
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    rcases RelQ.op' hqa (.op hvb hi hops hevs hfoot hst) with ⟨hq, hA⟩ | ⟨rfl, vals, m', w', rfl⟩
    · exact hop s mon b k allocs its' m w _ _ hq hA (.op hvb hi hops hevs hfoot hst) ls t' hr
    · exact .inr (.inl (itemSimOut_ret (.op hvb hi hops hevs hfoot hst)))

theorem dmbish_inst {env : Env} {a : ArmInst} (h : Insn.dmbish.toArmInst env = .ok a) (s : ArmState) :
    instEvs a s = [dmbEv] ∧ clsOf a = .dmb := by
  have e : Insn.dmbish.toArmInst env =
      .ok (ArmInst.BR (BranchInst.Barrier { CRm := 11#4, op2 := 5#3 })) := rfl
  rw [e] at h
  cases h
  refine ⟨?_, ?_⟩
  · simp only [instEvs]; exact ite_eq_left (by decide)
  · simp only [clsOf]; exact ite_eq_left (by decide)

theorem patch_dmb (w : ArmState) : patch [dmbEv] w = w := by
  simp [patch, applyR, dmbEv, AKind.dir, setMem_self]

theorem assign_fence {regs : Array Reg} {i' : MInst} (h : MInst.fence.assign regs = .ok i') :
    i' = .fence := by
  simp [MInst.assign, MInst.visitOperands, StateT.run, pure, StateT.pure, bind,
    Except.bind] at h
  split at h
  · cases h
  · rename_i v hv
    cases hv
    split at h
    · cases h; rfl
    · cases h

theorem lines_fence (c : FnCtx) (ps : Backend.PState) :
    MInst.fence.lines c ps = .ok ([.ins .dmbish none], ps) := rfl

/-- The instructions without memory kind (`NoEvScope`). -/
def NoEvForm (ctx : FnCtx) (i : MInst) : Prop :=
  (i.isCtl = false ∧ FormOk ctx i = true ∧ akinds i = []) ∨ (∃ ds, i = .args ds) ∨
    (∃ us, i = .rets us) ∨ (∃ c, i = .udf c)

/-- **The per-item obligation at an event-free item** (`itemSim_noev`), a run ending inside the
item at a line other than `ret`. -/
theorem noev_opR {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat} {allocs : Array Loc}
    {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → NoEvForm R.ctx i)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    OpOutN R (fun _ _ => True) (fun c => c.measure) (s, mon) (OpC b k allocs its' m w) ls t' := by
  cases hs0 with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
  have hsc' := hform vb i hvb hi
  have hak : akinds i = [] := by
    rcases hsc' with ⟨-, -, h⟩ | ⟨ds, rfl⟩ | ⟨us, rfl⟩ | ⟨cd, rfl⟩ <;> first | exact h | rfl
  have he : evs0 = [] := hevs.trans (cEvs_nil hak _ _)
  subst he
  rw [patch_nil] at hst
  have hstep : SrcStep R (.run ⟨b, .op k allocs :: its', m, w⟩) [] c0 :=
    .op hvb hi hops hevs hfoot (by rw [patch_nil]; exact hst)
  have hlt : ∀ c' : MConf CV ArmState, c'.measure ≤ its'.length →
      c'.measure < (MConf.run ⟨b, .op k allocs :: its', m, w⟩ : MConf CV ArmState).measure :=
    fun c' h => by rw [measure_run, List.length_cons]; omega
  have zero : ∀ c' : MConf CV ArmState, c'.measure ≤ its'.length →
      SrcStep R (.run ⟨b, .op k allocs :: its', m, w⟩) [] c' → Q R s c' → AInv R c' →
      ItemSimOut Policy.arm R.step (fun _ _ => True) (SrcStep R) (RelQ R) (PrivA R)
        (fun c => c.measure) (s, mon) (.run ⟨b, .op k allocs :: its', m, w⟩) ls := by
    intro c' hm hs hq' hA'
    exact ⟨0, [], c', (s, mon), fun _ => (0, 0), Nat.zero_le _, .inr (hlt c' hm), hs,
      by rw [List.take_zero]; exact .nil, .inl ⟨hq', hA'⟩, img_nil (by simp) _⟩
  -- a step ending the function: no Arm step
  by_cases hterm : (∃ vals m' w', c0 = .ret vals m' w') ∨ ∃ w', c0 = .halt w'
  · rcases hterm with ⟨vals, m', w', rfl⟩ | ⟨w', rfl⟩ <;>
    exact .inr (.inl (zero _ (Nat.zero_le _) hstep trivial trivial))
  rcases hsc' with ⟨hctl, hfo, -⟩ | ⟨ds, rfl⟩ | ⟨us, rfl⟩ | ⟨cd, rfl⟩
  rotate_left
  · -- `args`
    have hq' := realizes_args hR hq hA hvb hi hst
    have hA' := aInv_step hR hq hA hst
    cases hst with
    | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
      rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
      cases hn with
      | next hk => exact .inr (.inl (zero _ (Nat.le_of_eq measure_run) hstep hq' hA'))
      | goto _ _ _ =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨-, -, h⟩ := hsem; cases h
      | ret h => cases h
      | halt => exact absurd ⟨_, rfl⟩ fun h => hterm (.inr h)
  · -- `rets`: the step returns
    exfalso
    cases hst with
    | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
      rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
      simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, rfl⟩ := hsem
      cases hn with
      | ret _ => exact hterm (.inl ⟨_, _, _, rfl⟩)
  · -- `udf`: the step traps
    exfalso
    cases hst with
    | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
      rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
      simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, rfl⟩ := hsem
      cases hn with
      | halt => exact hterm (.inr ⟨_, rfl⟩)
  -- a straight-line form without memory kind
  cases hst with
  | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
  obtain rfl := csem_ctl hctl (R.sem_csem hsem)
  cases hn with
  | next hk =>
  have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hctl
  have hst := q_stRel hq
  have herrw : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
  obtain ⟨j, regs, i', ls1, T, s', c'', hal, hasg, hl1, hins, hdrop, hpc, hrun, hint, ⟨m', w'', rfl⟩,
    hm'', hq''⟩ := realizes_op_lines hR hq hvb hi hops hsz hsem hlen hk hOS hL
      (csem_next_world' (R.sem_csem hsem) hnc herrw)
  have hk1 : kinds ls1 = [] := by rw [lines_kinds R.ctx i' {} (hl1 {}), akinds_assign hasg, hak]
  have hat := lines_at hdrop
  have hhook : ∀ x t, Line.ins x t ∈ ls1 → x.hooked = false := fun x t h => by
    obtain ⟨x', t', e, hh⟩ := hins _ h; cases e; exact hh
  have hnom := nomem_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hk1 hat hhook hst.prog
    hpc hst.err hint hrun
  by_cases hN : ls1.length ≤ ls.length
  · obtain ⟨⟨s1, mon1⟩, r1, -⟩ := PRun.split (ls.take ls1.length) (ls.drop ls1.length)
      (by rw [List.take_append_drop]; exact hr)
    have hlen1 : (ls.take ls1.length).length = ls1.length := by simp; omega
    obtain ⟨hs1, hev1, -⟩ := prun_nil r1 fun i hi => hnom i (by omega)
    rw [hlen1] at hs1
    have hit : iterN R.step ls1.length s = s' :=
      iterN_execLines hR.layout hR.lm hR.fit ls1 j s s' hat hhook hst.prog hpc hst.err hint hrun
    simp only at hs1
    rw [hit] at hs1
    subst hs1
    refine .inr (.inl ⟨ls1.length, [], _, (s1, mon1), fun _ => (0, 0), hN,
      .inr (hlt _ (Nat.le_of_eq measure_run)), .op hvb hi hops hevs hfoot (by rw [patch_nil]; exact hm''),
      r1, .inl ⟨hq'', aInv_step hR hq hA hm''⟩, img_nil hev1 _⟩)
  · obtain ⟨hs', hev, -⟩ := prun_nil hr fun i hi => hnom i (by omega)
    refine .inr (.inr (.inr ⟨privW_of_nil hev, ?_⟩))
    rw [hs']
    exact nonRet_execLines hR hat hhook hst.prog hpc hst.err hint hrun (noRet_lines (hl1 {})) _
      (by omega)

/-- **The per-item obligation at an event-free item** (`itemSim_noev`). -/
theorem noev_op {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat} {allocs : Array Loc}
    {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → NoEvForm R.ctx i)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    OpOut R (s, mon) (OpC b k allocs its' m w) ls :=
  (noev_opR hR hq hA hs0 hform hr).out

/-- **The per-item obligation at a `dmb ish`** (`fence`): the Arm's one step has the barrier event,
the source step's; a run ending before it is at its line. -/
theorem fence_opR {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat} {allocs : Array Loc}
    {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i = .fence)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    OpOutN R (fun _ _ => True) (fun c => c.measure) (s, mon) (OpC b k allocs its' m w) ls t' := by
  cases hs0 with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
  obtain rfl := hform vb i hvb hi
  have he : evs0 = [dmbEv] := hevs.trans (IselMemAux.cEvs_fence _ _ _ _)
  subst he
  have hst0 := hst
  rw [patch_dmb] at hst0
  cases hst0 with
  | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
  obtain rfl := csem_ctl (show MInst.fence.isCtl = false from rfl) (R.sem_csem hsem)
  cases hn with
  | next hk =>
  have hstr := q_stRel hq
  have herrw : Arm.r .ERR w = .None := by
    rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
  obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) (i := .fence) rfl
  obtain ⟨j, regs, i', ls1, T, s', c'', hal, hasg, hl1, hins, hdrop, hpc, hrun, hint, ⟨m', w'', rfl⟩,
    hm'', hq''⟩ := realizes_op_lines hR hq hvb hi hops hsz hsem hlen hk hOS hL
      (csem_next_world' (R.sem_csem hsem) (fun _ h => by cases h) herrw)
  obtain rfl := assign_fence hasg
  have hls1 : ls1 = [.ins .dmbish none] := by
    have := (hl1 {}).symm.trans (lines_fence R.ctx {})
    simp only [Except.ok.injEq, Prod.mk.injEq] at this
    exact this.1
  subst hls1
  have hat := lines_at hdrop
  have hhook : ∀ x t, Line.ins x t ∈ [Line.ins .dmbish none] → x.hooked = false := fun x t h => by
    obtain ⟨x', t', e, hh⟩ := hins _ h; cases e; exact hh
  obtain ⟨x, t, a, hli, ha, hdec, hev, -⟩ := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm
    hR.fit hat hhook hstr.prog hpc hstr.err hint hrun 0 (by simp)
  simp only [List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hli
  obtain ⟨rfl, rfl⟩ := hli
  obtain ⟨hia, hca⟩ := dmbish_inst ha s
  have hit : iterN R.step 1 s = s' :=
    iterN_execLines hR.layout hR.lm hR.fit _ j s s' hat hhook hstr.prog hpc hstr.err hint hrun
  cases ls with
  | nil =>
    cases hr
    refine .inr (.inr (.inr ⟨fun p y hy => (by rw [evAt_evTr_nil (by simp)] at hy; cases hy), ?_⟩))
    exact nonRet_execLines hR hat hhook hstr.prog hpc hstr.err hint hrun
      (fun x t h => by simp at h; obtain ⟨rfl, -⟩ := h; intro h; cases h) 0 (by simp)
  | cons l ls'' =>
  cases hr with
  | @cons _ t1 _ _ _ hs hp _ hr' =>
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc =>
      rw [cls_of_decode (show decodeAt s = some a from hdec), hca] at hc
      cases hc
  have hl : l.evs = [dmbEv] := by
    rcases hp with h | ⟨M, hM⟩
    · rw [hxf] at h; cases h
    · have hev' : stepEvs s = instEvs a s := hev
      rw [hM, ArmPrecise.stepEvs_setMem, hev', hia]
      simp [ArmPrecise.reread, ArmPrecise.reread1, dmbEv, AKind.dir]
  obtain ⟨h1, -, -⟩ := tstep_own hs hp (by rw [hl]; exact agrees_noR (by simp [dmbEv, AKind.dir]) _) hxf
  obtain ⟨s1, mon1⟩ := t1
  simp only at h1
  subst h1
  refine .inr (.inl ⟨1, [dmbEv], _, (R.step s, mon1), fun _ => (0, 0), by simp, .inl Nat.one_pos,
    .op hvb hi hops hevs hfoot (by rw [patch_dmb]; exact hm''),
    by simpa using PRun.cons hs hp trivial .nil,
    .inl ⟨by rw [show R.step s = s' from hit]; exact hq'', aInv_step hR hq hA hm''⟩, ?_⟩)
  have htr : evTr ((l :: ls'').take 1) = [[dmbEv]] := by simp [evTr, hl]
  rw [htr]
  refine ⟨fun k hk => ?_, fun k k' _ h2 => by simp at h2; omega, fun p y hy hW _ => ?_,
    fun e he hF => absurd (by simp at he; subst he; rfl) hF, .inl ⟨by simp, fun e he => ?_⟩,
    fun h => by simp at h⟩
  · obtain rfl : k = 0 := by simpa using hk
    rfl
  · obtain ⟨j', k'⟩ := p
    rcases j' with _ | j'
    · rw [evAt_single] at hy
      rcases k' with _ | k' <;> simp at hy
      subst hy; exact absurd hW (by decide)
    · simp [evAt] at hy
  · simp at he; subst he; simp [dmbEv]

/-- **The per-item obligation at a `dmb ish`** (`fence`): the Arm's one step has the barrier event,
the source step's. -/
theorem fence_op {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat} {allocs : Array Loc}
    {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → i = .fence)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    OpOut R (s, mon) (OpC b k allocs its' m w) ls :=
  (fence_opR hR hq hA hs0 hform hr).out

/-! ## Exclusive and acquire/release instructions -/

/-- The pc, error and program after `a` do not depend on the memory. -/
def CtlIndep (a : ArmInst) : Prop :=
  ∀ (M : Memory) (y : ArmState), Arm.r .PC (exec_inst a (setMem M y)) = Arm.r .PC (exec_inst a y) ∧
    Arm.r .ERR (exec_inst a (setMem M y)) = Arm.r .ERR (exec_inst a y) ∧
    (exec_inst a (setMem M y)).program = (exec_inst a y).program

theorem exclFields_ok {bits o2 lb : Nat} {rs : BitVec 5} {rt rn : Reg} {ai : ArmInst}
    (h : Insn.armFields.exclFields bits o2 lb rs rt rn = .ok ai) :
    ∃ (sz rn' rt' : _), ai = ArmInst.LDST (LDSTInst.Reg_exclusive
        { size := sz, ord := BitVec.ofNat 1 o2, L := BitVec.ofNat 1 lb, Rs := rs, o0 := 1#1,
          Rn := rn', Rt := rt' }) ∧ rn.encSP = .ok rn' ∧ rt.encZR = .ok rt' ∧
      ((bits = 8 ∧ sz = 0#2) ∨ (bits = 16 ∧ sz = 1#2) ∨ (bits = 32 ∧ sz = 2#2) ∨
        (bits = 64 ∧ sz = 3#2)) := by
  unfold Insn.armFields.exclFields at h
  cases hn : rn.encSP with
  | error e => simp [hn, bind, Except.bind] at h; split at h <;> simp_all
  | ok Rn =>
  cases ht : rt.encZR with
  | error e => simp [hn, ht, bind, Except.bind] at h; split at h <;> simp_all
  | ok Rt =>
  simp only [hn, ht, bind, Except.bind, pure, Except.pure] at h
  split at h
  all_goals first
    | (cases h; exact ⟨_, Rn, Rt, rfl, rfl, rfl, by decide⟩)
    | cases h

/-- The same pc, error and program. -/
def SameCtl (s t : ArmState) : Prop :=
  Arm.r .PC s = Arm.r .PC t ∧ Arm.r .ERR s = Arm.r .ERR t ∧ s.program = t.program

theorem SameCtl.trans {s t u : ArmState} (h1 : SameCtl s t) (h2 : SameCtl t u) : SameCtl s u :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem SameCtl.symm {s t : ArmState} (h : SameCtl s t) : SameCtl t s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem sameCtl_setMem (M : Memory) (y : ArmState) : SameCtl (setMem M y) y :=
  ⟨r_setMem _ _ _, r_setMem _ _ _, setMem_program _ _⟩

theorem sameCtl_wgz (n : Nat) (i : BitVec 5) (v : BitVec n) (y : ArmState) :
    SameCtl (write_gpr_zr n i v y) y := by
  unfold write_gpr_zr
  split
  · simp only [SameCtl, write_gpr, Arm.r_of_w_different (show StateField.PC ≠ .GPR i by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR i by simp), Arm.w_program]
    exact ⟨trivial, trivial, trivial⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem sameCtl_wmb (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (y : ArmState) :
    SameCtl (write_mem_bytes n a v y) y :=
  ⟨Arm.r_of_write_mem_bytes, Arm.r_of_write_mem_bytes, write_mem_bytes_program _ _⟩

theorem sameCtl_pc4 {s t : ArmState} (h : SameCtl s t) :
    SameCtl (write_pc (read_pc s + 4#64) s) (write_pc (read_pc t + 4#64) t) := by
  simp only [SameCtl, write_pc, read_pc, Arm.r_of_w_same,
    Arm.r_of_w_different (show StateField.ERR ≠ .PC by simp), Arm.w_program]
  exact ⟨by rw [h.1], h.2.1, h.2.2⟩

theorem ctlIndep_of {a : ArmInst} (h : ∀ M y, SameCtl (exec_inst a (setMem M y)) (exec_inst a y)) :
    CtlIndep a := h

/-- **The exclusive and acquire/release instructions' pc, error and program do not depend on the
memory.** -/
theorem ctlIndep_excl (inst : Reg_exclusive_cls) : CtlIndep (.LDST (.Reg_exclusive inst)) := by
  refine ctlIndep_of fun M y => ?_
  simp only [exec_inst]
  unfold LDST.exec_reg_exclusive
  simp only [check_sp_sm']
  split
  · simp only [write_err_sm]; exact sameCtl_setMem _ _
  · by_cases hL : inst.L = 1#1
    · simp only [hL, ite_true]
      exact sameCtl_pc4 (((sameCtl_wgz _ _ _ _).trans (sameCtl_setMem _ _)).trans
        (sameCtl_wgz _ _ _ _).symm)
    · simp only [hL, ite_false]
      exact sameCtl_pc4 ((((sameCtl_wgz _ _ _ _).trans (sameCtl_wmb _ _ _ _)).trans
        (sameCtl_setMem _ _)).trans ((sameCtl_wgz _ _ _ _).trans (sameCtl_wmb _ _ _ _)).symm)

/-! ## Straight-line forms with one event -/

theorem reread_applyR_reread : ∀ {X : List Ev}, X.length ≤ 1 → (∀ e ∈ X, e.n ≤ 2 ^ 64) →
    ∀ (M m : Memory), ArmPrecise.reread (applyR (ArmPrecise.reread M X) m) X = ArmPrecise.reread M X
  | [], _, _, _, _ => rfl
  | [e], _, hn, M, m => by
    by_cases hR : e.k.dir = .R
    · rw [reread_one hR M, reread_one hR]
      simp only [applyR, hR, ite_true, readM_writeM _ _ _ _ (hn e List.mem_cons_self)]
    · simp [ArmPrecise.reread, ArmPrecise.reread1, hR]
  | _ :: _ :: _, h, _, _, _ => by simp at h

open Classical in
/-- **`straightSem` of a one-line form on a world with any memory**: the condition of a step
does not depend on the memory when the canonical instruction's pc, error and program do not. -/
theorem straightSem_one {F : BitVec 64 → Prop} {ctx : FnCtx} {i ic : MInst} {uses : List CV}
    {w : ArmState} {ops : Array Operand} {x : Insn} {t : Option Clif.TrapCode} {a : ArmInst}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hl : ic.lines ctx {} = .ok ([.ins x t], {})) (ha : x.toArmInst env0 = .ok a) (hc : CtlIndep a)
    (M : Memory) :
    straightSem F ctx i uses (setMem M w) =
      if AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w) ∧
          Arm.r .PC (exec_inst a (placeUses ops (canonRegs ops) uses w)) =
            Arm.r .PC (placeUses ops (canonRegs ops) uses w) + 4#64 ∧
          Arm.r .ERR (exec_inst a (placeUses ops (canonRegs ops) uses w)) = .None ∧
          (exec_inst a (placeUses ops (canonRegs ops) uses w)).program = w.program then
        some (defVals ops (canonRegs ops) (exec_inst a (setMem M (placeUses ops (canonRegs ops) uses w))),
          exec_inst a (setMem M (placeUses ops (canonRegs ops) uses w)), Ctl.next)
      else none := by
  obtain ⟨h1, h2, h3⟩ := hc M (placeUses ops (canonRegs ops) uses w)
  unfold straightSem
  simp only [hops, hic, placeUses_setMem, accessOk_setMem, execMInst, hl, execLines, ha, h1, r_setMem,
    setMem_program]
  by_cases hA : AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w)
  · by_cases hP : Arm.r .PC (exec_inst a (placeUses ops (canonRegs ops) uses w)) =
        Arm.r .PC (placeUses ops (canonRegs ops) uses w) + 4#64
    · simp only [hA, hP, true_and, ite_true]
      have e : (Arm.r .ERR (exec_inst a (setMem M (placeUses ops (canonRegs ops) uses w))) = .None ∧
          (exec_inst a (setMem M (placeUses ops (canonRegs ops) uses w))).program = w.program) =
          (Arm.r .ERR (exec_inst a (placeUses ops (canonRegs ops) uses w)) = .None ∧
          (exec_inst a (placeUses ops (canonRegs ops) uses w)).program = w.program) := by
        rw [h2, h3]
      simp only [e]
    · simp [hA, hP]
  · simp [hA]

/-- **The registers of an instruction item** under `Q`: its allocation is to allocatable
registers and its uses are the Arm state's registers. -/
theorem q_regs {R : RL} {s : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : ArmState} (hq : Q R s (OpC b k allocs its m w)) {vb : VBlock} {i : MInst}
    {ops : Array Operand} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hops : i.operands = .ok ops) :
    ∃ regs : Array Reg, allocs = regs.map Loc.reg ∧ regs.size = ops.size ∧
      (∀ p ∈ (ops.zip regs).toList, p.2.allocatable = true) ∧
      itemUses ops allocs m = useVals ops regs s := by
  have hst := q_stRel hq
  rcases Q.cases hq with hqs | ⟨vb', allocs', regs', i', x, -, hvb', he, -, hal', hins, hasg', -⟩
  rotate_left
  · -- a forwarding block: its only instruction is a `jump`, without operands
    rw [hvb] at hvb'
    cases hvb'
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [hins] at hi
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    obtain ⟨rfl, rfl⟩ := assign_jump hasg'
    obtain rfl : ops = #[] := by
      have h0 : (MInst.jump x).operands = .ok #[] := rfl
      rw [h0] at hops
      exact (Except.ok.inj hops).symm
    exact ⟨#[], hal', rfl, by simp, by simp [itemUses, useVals]⟩
  obtain ⟨j, vb0, items, pre, code, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hcode, -⟩ := hqs
  rw [hvb] at hvb0
  cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, -⟩ := itemCode_op hc1
  obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2
  cases hi2
  rw [hops] at hops2
  cases hops2
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
  refine ⟨regs, rfl, by simpa using hsz.symm, fun p hp => ?_, useVals_of_store hstat hm⟩
  have := (hloc (p.1, .reg p.2) (by rw [pairs_regs]; exact List.mem_map_of_mem hp)).1
  simp only [CheckCtx.locOk, Loc.cls?, Bool.and_eq_true] at this
  exact this.2

theorem regs_inj {regs regs' : Array Reg} (h : regs.map Loc.reg = regs'.map Loc.reg) :
    regs = regs' := by
  apply Array.toList_inj.1
  have := congrArg Array.toList h
  simp only [Array.toList_map] at this
  exact (List.map_inj_right (fun a b e => by cases e; rfl)).1 this

theorem aInv_patch {R : RL} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (h : AInv R (OpC b k allocs its m w)) (E : List Ev) :
    AInv R (OpC b k allocs its m (patch E w)) := fun hb hop r hr => by
  rw [h hb hop r hr]; simp only [patch, regVal_setMem]

theorem defVals_length (ops : Array Operand) (regs : Array Reg) (s t : ArmState) :
    (defVals ops regs s).length = (defVals ops regs t).length := by
  simp [defVals]

/-- **A straight-line form with at most one event and one Arm instruction** (`ldar`, `stlr`): the
per-form facts `oneEv_op` needs. `ev` is the **event equality**: the allocated instruction's
events on any memory are the canonical run's (`cEvs`) on that memory. -/
structure OneEvForm (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) : Prop where
  ctl : i.isCtl = false
  form : FormOk ctx i = true
  canon : ∃ ops ic x t a, i.operands = .ok ops ∧ i.assign (canonRegs ops) = .ok ic ∧
    ic.lines ctx {} = .ok ([.ins x t], {}) ∧ x.toArmInst env0 = .ok a ∧ CtlIndep a
  line : ∀ ops regs i', i.operands = .ok ops → regs.size = ops.size → i.assign regs = .ok i' →
    ∃ x t, ∀ ps, i'.lines ctx ps = .ok ([.ins x t], ps)
  arm : ∀ ops regs i' x t env a, i.operands = .ok ops → regs.size = ops.size →
    i.assign regs = .ok i' → i'.lines ctx {} = .ok ([.ins x t], {}) →
    x.toArmInst env = .ok a → (∀ rel rs rn, clsOf a ≠ .stx rel rs rn) ∧
      ∀ y, ∀ e ∈ instEvs a y, e.k ≠ .relXW ∧ (e.k.dir ≠ .F → 0 < e.n)
  ev : ∀ (s w : ArmState) ops regs i' x t env a, SameWorld F s w → i.operands = .ok ops →
    regs.size = ops.size → (∀ p ∈ (ops.zip regs).toList, p.2.allocatable = true) →
    i.assign regs = .ok i' → i'.lines ctx {} = .ok ([.ins x t], {}) → x.toArmInst env = .ok a →
    ∀ M, instEvs a (setMem M s) = cEvs F ctx i (useVals ops regs s) (setMem M w)

theorem lines_one_eq {ctx : FnCtx} {i' : MInst} {ls : List Line} {x : Insn} {t : Option Clif.TrapCode}
    (h1 : ∀ ps, i'.lines ctx ps = .ok (ls, ps)) (h2 : ∀ ps, i'.lines ctx ps = .ok ([.ins x t], ps)) :
    ls = [.ins x t] := by
  have := (h1 {}).symm.trans (h2 {})
  simp only [Except.ok.injEq, Prod.mk.injEq] at this
  exact this.1

/-- **The per-item obligation at a straight-line form with one Arm instruction** (`OneEvForm`):
the Arm's one step reads (writes) what the canonical run reads (writes), on every memory, so the
source steps with the Arm's read bytes (**receptiveness**: the step's condition does not depend on
the memory, `straightSem_one`), and `Q` holds after both patched with them (`q_patch`); a run
ending inside the item (with no Arm step) is at a line other than `ret`. -/
theorem oneEv_opR {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat} {allocs : Array Loc}
    {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → OneEvForm R.F R.ctx i)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    OpOutN R (fun _ _ => True) (fun c => c.measure) (s, mon) (OpC b k allocs its' m w) ls t' := by
  cases hs0 with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
  have hf := hform vb i hvb hi
  obtain ⟨regs, hal, hsz, hall, huses⟩ := q_regs hq hvb hi hops
  have hstr := q_stRel hq
  have herrw : Arm.r .ERR w = .None := by
    rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
  have halw : CheckSPAlignment w :=
    align_of_sp (show Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s from
      (hstr.world.1 (.GPR 31#5) (by simp [Masked])).symm) hstr.align
  have hnc : ∀ info, i ≠ .call info := by rintro info rfl; exact absurd hf.ctl (by simp [MInst.isCtl])
  have hnt : ∀ info ti, i ≠ .tryCall info ti := by rintro info ti rfl; exact absurd hf.ctl (by simp [MInst.isCtl])
  have hwf : csemWF R.ctx i (itemUses ops allocs m) = true := by
    rw [huses]; simp [csemWF, hf.form, hops, useVals_length ops regs hsz]
  have hsemM : ∀ M, R.sem i (itemUses ops allocs m) (setMem M w) =
      straightSem R.F R.ctx i (itemUses ops allocs m) (setMem M w) := fun M => by
    rw [R.sem_eq hnc hnt, csem_of_wf hf.ctl hwf (by rw [r_setMem]; exact herrw)
      (by rw [spAlign_setMem]; exact halw)]
  obtain ⟨ops', ic, x', t', a', hops', hic, hlc, hac, hci⟩ := hf.canon
  rw [hops] at hops'
  cases hops'
  have hss := fun M => straightSem_one (F := R.F) (uses := itemUses ops allocs m) (w := w) hops hic
    hlc hac hci M
  obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hf.form
  cases hst with
  | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz1 hsem hlen hho hcl hn =>
  rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
  obtain rfl := csem_ctl hf.ctl (R.sem_csem hsem)
  cases hn with
  | next hk =>
  have hsem' := hsem
  rw [show patch evs0 w = setMem (applyR evs0 w.mem) w from rfl, hsemM, hss] at hsem'
  split at hsem'
  case isFalse => cases hsem'
  rename_i hC
  simp only [Option.some.injEq, Prod.mk.injEq] at hsem'
  obtain ⟨rfl, -, -⟩ := hsem'
  -- the Arm instruction at `s`
  have hav0 : ∀ e ∈ evs0, Avoids R.F e.n e.addr := by
    rw [hevs]
    exact cEvs_avoid (by rw [patch, r_setMem]; exact herrw)
      (fun _ => ⟨hwf, by rw [patch, spAlign_setMem]; exact halw⟩) (R.sem_csem hsem)
  obtain ⟨j, regs', i', ls1, T, s', c'', hal', hasg, hl1, hins, hdrop, hpc, -, -, -, -, -⟩ :=
    realizes_op_lines hR (q_patch hR hq hav0) hvb hi hops hsz1 hsem hlen hk hOS hL
      (csem_next_world' (R.sem_csem hsem) hnc (by rw [patch, r_setMem]; exact herrw))
  obtain rfl : regs' = regs := regs_inj (hal'.symm.trans hal)
  obtain ⟨x, t, hxl⟩ := hf.line ops regs' i' hops hsz hasg
  obtain rfl := lines_one_eq hl1 hxl
  have hj : R.fa.lines.toList[j]? = some (.ins x t) := by simpa using lines_at hdrop 0 _ rfl
  have hhk : x.hooked = false := by
    obtain ⟨x0, t0, e, hh⟩ := hins _ List.mem_cons_self; cases e; exact hh
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hhk
    hstr.prog (by have := hpc; rw [patch, r_setMem] at this; exact this) hstr.err
  obtain ⟨hnostx, hevk⟩ := hf.arm ops regs' i' x t _ a hops hsz hasg (hxl {}) ha
  -- the Arm run
  cases ls with
  | nil =>
    cases hr
    have hpcs : Arm.r .PC s = R.pcOf j := by rw [patch, r_setMem] at hpc; exact hpc
    refine .inr (.inr (.inr ⟨fun p y hy => ?_, ?_⟩))
    · rw [evAt_evTr_nil (by simp)] at hy
      cases hy
    · exact ⟨j, x, t, hj, noRet_lines (hl1 {}) x t (by simp), hhk, hpcs⟩
  | cons l ls'' =>
  cases hr with
  | @cons _ t1 _ _ _ hs hp _ hr' =>
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc => rw [cls_of_decode hdec] at hc; exact absurd hc (hnostx _ _ _)
  obtain ⟨M, hM⟩ : ∃ M, l.evs = stepEvs (setMem M s) := by
    rcases hp with h | h
    · rw [hxf] at h; cases h
    · exact h
  have hl : l.evs = instEvs a (setMem M s) := by
    rw [hM, ArmPrecise.stepEvs_setMem, hev, ArmPrecise.instEvs_setMem]
  have hevq : ∀ M', instEvs a (setMem M' s) = cEvs R.F R.ctx i (itemUses ops allocs m) (setMem M' w) :=
    fun M' => by rw [huses]; exact hf.ev s w ops regs' i' x t _ a hstr.world hops hsz hall hasg (hxl {}) ha M'
  have hfix : l.evs = cEvs R.F R.ctx i (itemUses ops allocs m) (patch l.evs w) := by
    show l.evs = cEvs R.F R.ctx i (itemUses ops allocs m) (setMem (applyR l.evs w.mem) w)
    rw [← hevq, ArmPrecise.instEvs_setMem, hl, ArmPrecise.instEvs_setMem,
      reread_applyR_reread (len_instEvs a s) (ArmPrecise.n_instEvs a s)]
  -- the source step reading the Arm's bytes
  have hsem1 : R.sem i (itemUses ops allocs m) (patch l.evs w) =
      some (defVals ops (canonRegs ops) (exec_inst a' (setMem (applyR l.evs w.mem)
        (placeUses ops (canonRegs ops) (itemUses ops allocs m) w))),
        exec_inst a' (setMem (applyR l.evs w.mem) (placeUses ops (canonRegs ops) (itemUses ops allocs m) w)),
        .next) := by
    show R.sem i _ (setMem _ w) = _
    rw [hsemM, hss, ite_eq_left hC]
  have hlen1 : (defVals ops (canonRegs ops) (exec_inst a' (setMem (applyR l.evs w.mem)
      (placeUses ops (canonRegs ops) (itemUses ops allocs m) w)))).length =
      ((ops.zip allocs).toList.filter (·.1.isDef)).length := by
    rw [defVals_length _ _ _ (exec_inst a' (setMem (applyR evs0 w.mem)
      (placeUses ops (canonRegs ops) (itemUses ops allocs m) w)))]
    exact hlen
  have hav1 : ∀ e ∈ l.evs, Avoids R.F e.n e.addr := by
    rw [hfix]
    exact cEvs_avoid (by rw [patch, r_setMem]; exact herrw)
      (fun _ => ⟨hwf, by rw [patch, spAlign_setMem]; exact halw⟩) (R.sem_csem hsem1)
  have hq1 := q_patch hR hq hav1
  obtain ⟨j2, regs2, i2, ls2, T2, s2, c2, hal2, hasg2, hl2, hins2, hdrop2, hpc2, hrun2, hint2,
    ⟨m2', w2, rfl⟩, hm2, hq2⟩ := realizes_op_lines hR hq1 hvb hi hops hsz1 hsem1 hlen1 hk hOS hL
      (csem_next_world' (R.sem_csem hsem1) hnc (by rw [patch, r_setMem]; exact herrw))
  obtain rfl : regs2 = regs' := regs_inj (hal2.symm.trans hal)
  obtain ⟨x2, t2, hxl2⟩ := hf.line ops regs2 i2 hops hsz hasg2
  obtain rfl := lines_one_eq hl2 hxl2
  have hstr1 := q_stRel hq1
  have hhook2 : ∀ x t, Line.ins x t ∈ [Line.ins x2 t2] → x.hooked = false := fun x t h => by
    obtain ⟨x', t', e, hh⟩ := hins2 _ h; cases e; exact hh
  have hit : iterN R.step 1 (patch l.evs s) = s2 :=
    iterN_execLines hR.layout hR.lm hR.fit _ j2 _ s2 (lines_at hdrop2) hhook2 hstr1.prog hpc2
      hstr1.err hint2 hrun2
  obtain ⟨s1, mon1⟩ := t1
  have ht1 : s1 = R.step (patch l.evs s) := by
    cases hs with
    | exec => rfl
    | xfail => cases hxf
  subst ht1
  -- the item's image
  have hfoot1 : IFoot R.sem i (itemUses ops allocs m) (patch l.evs w) l.evs := by
    have hfo := straightSem_foot (F := R.F) (ctx := R.ctx) (i := i) (uses := itemUses ops allocs m)
      (w := patch l.evs w)
    have hce : cEvs R.F R.ctx i (itemUses ops allocs m) (patch l.evs w) =
        straightEvs R.ctx i (itemUses ops allocs m) (patch l.evs w) := by
      unfold cEvs; simp only [hf.ctl, Bool.false_eq_true, ite_false]
    rw [← hce, ← hfix] at hfo
    refine ⟨hfo.1, fun m' hm' => ?_⟩
    rw [show setMem m' (patch l.evs w) = setMem m' w from rfl, hsemM, show patch l.evs w =
      setMem (applyR l.evs w.mem) w from rfl, hsemM]
    exact hfo.2 m' hm'
  have hlen : l.evs.length ≤ 1 := by rw [hl]; exact len_instEvs a _
  refine .inr (.inl ⟨1, l.evs, _, (R.step (patch l.evs s), mon1), fun k => (0, k), by simp,
    .inl Nat.one_pos, .op hvb hi hops hfix hfoot1 hm2, by simpa using PRun.cons hs hp trivial .nil,
    .inl ⟨by show Q R (R.step (patch l.evs s)) _; rw [show R.step (patch l.evs s) = s2 from hit]; exact hq2,
      aInv_step hR hq1 (aInv_patch hA _) hm2⟩, ?_⟩)
  have htr : evTr ((l :: ls'').take 1) = [l.evs] := by simp [evTr]
  rw [htr]
  refine ⟨fun k hk => by rw [evAt_single]; exact List.getElem?_eq_getElem hk,
    fun k k' h1 h2 => Or.inr ⟨rfl, h1⟩, fun p y hy hW hn => ?_, fun e he hF => ?_,
    .inl ⟨hlen, fun e he => ?_⟩, fun h => by omega⟩
  · obtain ⟨j', k'⟩ := p
    rcases j' with _ | j'
    · rw [evAt_single] at hy
      exact absurd rfl (hn k' (List.getElem?_eq_some_iff.mp hy).1)
    · simp [evAt] at hy
  · have he' : e ∈ instEvs a (setMem M s) := hl ▸ he
    have hn0 := (hevk _ e he').2 hF
    have := hav1 e he 0 hn0
    simpa [PrivA] using this
  · exact (hevk _ e (hl ▸ he)).1

/-- **The per-item obligation at a straight-line form with one Arm instruction** (`OneEvForm`):
the Arm's one step reads (writes) what the canonical run reads (writes), on every memory, so the
source steps with the Arm's read bytes (**receptiveness**: the step's condition does not depend on
the memory, `straightSem_one`), and `Q` holds after both patched with them (`q_patch`). -/
theorem oneEv_op {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat} {allocs : Array Loc}
    {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → OneEvForm R.F R.ctx i)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    OpOut R (s, mon) (OpC b k allocs its' m w) ls :=
  (oneEv_opR hR hq hA hs0 hform hr).out

/-! ## `ldar` and `stlr` -/

theorem toArmInst_excl {bits o2 lb : Nat} {rs : BitVec 5} {rt rn : Reg} {env : Env} {ai : ArmInst}
    {x : Insn} (hx : x.armFields env = Insn.armFields.exclFields bits o2 lb rs rt rn)
    (h : x.toArmInst env = .ok ai) :
    ∃ (sz rn' rt' : _), ai = ArmInst.LDST (LDSTInst.Reg_exclusive
        { size := sz, ord := BitVec.ofNat 1 o2, L := BitVec.ofNat 1 lb, Rs := rs, o0 := 1#1,
          Rn := rn', Rt := rt' }) ∧ rn.encSP = .ok rn' ∧ rt.encZR = .ok rt' ∧
      ((bits = 8 ∧ sz = 0#2) ∨ (bits = 16 ∧ sz = 1#2) ∨ (bits = 32 ∧ sz = 2#2) ∨
        (bits = 64 ∧ sz = 3#2)) := by
  unfold Insn.toArmInst at h
  rw [hx] at h
  cases he : Insn.armFields.exclFields bits o2 lb rs rt rn with
  | error e => rw [he] at h; cases h
  | ok a0 =>
    rw [he] at h
    cases h
    obtain ⟨sz, rn', rt', rfl, h1, h2, h3⟩ := exclFields_ok he
    exact ⟨sz, rn', rt', rfl, h1, h2, h3⟩

theorem sz_eq {bits : Nat} {sz sz' : BitVec 2}
    (h : (bits = 8 ∧ sz = 0#2) ∨ (bits = 16 ∧ sz = 1#2) ∨ (bits = 32 ∧ sz = 2#2) ∨ (bits = 64 ∧ sz = 3#2))
    (h' : (bits = 8 ∧ sz' = 0#2) ∨ (bits = 16 ∧ sz' = 1#2) ∨ (bits = 32 ∧ sz' = 2#2) ∨
      (bits = 64 ∧ sz' = 3#2)) : sz = sz' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> first | rfl | (simp at h)

/-- Two exclusive/acquire-release instructions with the same fields but the registers have the same
events when the address registers (not `sp`) and, for a store, the data agree. -/
theorem exclEvs_regs {size : BitVec 2} {o : BitVec 1}
    {l : BitVec 1} {rs : BitVec 5} {o1 : BitVec 1} {rn rt rn' rt' : BitVec 5} {s y : ArmState}
    (hn : rn ≠ 31#5) (hn' : rn' ≠ 31#5) (ha : read_gpr 64 rn s = read_gpr 64 rn' y) (hm : s.mem = y.mem)
    (hv : l ≠ 1#1 → ldst_read false (8 <<< size.toNat) rt s = ldst_read false (8 <<< size.toNat) rt' y) :
    exclEvs { size, ord := o, L := l, Rs := rs, o0 := o1, Rn := rn, Rt := rt } s =
      exclEvs { size, ord := o, L := l, Rs := rs, o0 := o1, Rn := rn', Rt := rt' } y := by
  unfold exclEvs
  simp only [hn, hn', false_and, ite_false, ha, hm, exclKind]
  by_cases hl : l = 1#1
  · simp only [hl, ite_true]
  · simp only [hl, ite_false, hv hl]

theorem exclEvs_mem {inst : Reg_exclusive_cls} {y : ArmState} {e : Ev} (he : e ∈ exclEvs inst y) :
    e.k = exclKind inst ∧ 0 < e.n := by
  unfold exclEvs at he
  have hpos : 0 < (8 <<< inst.size.toNat) / 8 := by
    rw [Nat.shiftLeft_eq, Nat.mul_div_cancel_left _ (by decide)]; exact Nat.two_pow_pos _
  split at he
  · cases he
  · split at he <;> (simp only [List.mem_singleton] at he; subst he; exact ⟨rfl, hpos⟩)

theorem x_of_alloc {r : Reg} (h : r.allocatable = true) {rn : BitVec 5} (he : r.encSP = .ok rn) :
    ∃ q, r = .x q ∧ q < 29 ∧ rn = BitVec.ofNat 5 q := by
  rcases allocatable_cases h with ⟨q, rfl, hq, -⟩ | ⟨q, rfl, -⟩
  · simp only [Reg.encSP, show q ≤ 30 by omega, ite_true, pure, Except.pure, Except.ok.injEq] at he
    exact ⟨q, rfl, hq, he.symm⟩
  · simp [Reg.encSP, throw, throwThe, MonadExceptOf.throw] at he

theorem x_of_allocZR {r : Reg} (h : r.allocatable = true) {rt : BitVec 5} (he : r.encZR = .ok rt) :
    ∃ q, r = .x q ∧ q < 29 ∧ rt = BitVec.ofNat 5 q := by
  rcases allocatable_cases h with ⟨q, rfl, hq, -⟩ | ⟨q, rfl, -⟩
  · simp only [Reg.encZR, show q ≤ 30 by omega, ite_true, pure, Except.pure, Except.ok.injEq] at he
    exact ⟨q, rfl, hq, he.symm⟩
  · simp [Reg.encZR, throw, throwThe, MonadExceptOf.throw] at he

theorem lo64_regVal (s : ArmState) (q : Nat) : lo64 (regVal s (.x q)) = Arm.r (.GPR (rnum q)) s := by
  simp [lo64, regVal, BitVec.setWidth_setWidth_of_le]

theorem atom_toArmInst_ok {ty : CTy} (hty : AtomTy ty) (o2 lb : Nat) (rs : BitVec 5) (p q : Nat)
    (hp : p ≤ 30) (hq : q ≤ 30) :
    ∃ a, Insn.armFields.exclFields ty.bits o2 lb rs (.x p) (.x q) = .ok a := by
  rcases hty with rfl | rfl | rfl | rfl <;>
    simp [Insn.armFields.exclFields, CTy.bits, Reg.encSP, Reg.encZR, hp, hq, bind, Except.bind,
      pure, Except.pure]

/-- **`ldar` is a one-event form** (`OneEvForm`): the allocated `ldar`'s read is the canonical
one's (the address register's value, the access size, the memory's bytes). -/
theorem ldar_form {F : BitVec 64 → Prop} {ctx : FnCtx} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.loadAcquire ty rt rn fl) = true) :
    OneEvForm F ctx (.loadAcquire ty rt rn fl) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  have hty : AtomTy ty := by simpa [FormOk] using hfo
  have hops : (MInst.loadAcquire ty (.vreg d .int) (.vreg u .int) fl).operands =
      .ok #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩] := rfl
  have hasg2 : ∀ r0 r1 : Reg, (MInst.loadAcquire ty (.vreg d .int) (.vreg u .int) fl).assign #[r0, r1] =
      .ok (.loadAcquire ty r1 r0 fl) := fun _ _ => rfl
  obtain ⟨a0, ha0⟩ := atom_toArmInst_ok hty 1 1 31 1 0 (by omega) (by omega)
  have hca : (Insn.ldar ty.bits (.x 1) (.x 0)).toArmInst env0 = .ok a0.norm := by
    show ArmInst.norm <$> Insn.armFields.exclFields _ _ _ _ _ _ = _
    rw [ha0]; rfl
  obtain ⟨szc, rnc, rtc, hac, hrnc, hrtc, hszc⟩ := toArmInst_excl rfl hca
  refine ⟨rfl, hfo, ⟨_, _, _, _, _, hops, rfl, rfl, hca, hac ▸ ctlIndep_excl _⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg2] at hasg; cases hasg
    exact ⟨_, _, fun ps => rfl⟩
  · intro ops regs i' x t env a hops' hsz hasg hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg2] at hasg; cases hasg
    rw [show (MInst.loadAcquire ty r1 r0 fl).lines ctx {} =
      .ok ([.ins (.ldar ty.bits r1 r0) fl.trapCode], {}) from rfl] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    obtain ⟨sz, rn', rt', rfl, -, -, -⟩ := toArmInst_excl rfl ha
    refine ⟨fun rel rs rn h => by simp [clsOf, exclCls] at h, fun y e he => ?_⟩
    obtain ⟨hk, hn⟩ := exclEvs_mem (show e ∈ exclEvs _ y from he)
    rw [hk]
    exact ⟨by simp [exclKind], fun _ => hn⟩
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg2] at hasg; cases hasg
    rw [show (MInst.loadAcquire ty r1 r0 fl).lines ctx {} =
      .ok ([.ins (.ldar ty.bits r1 r0) fl.trapCode], {}) from rfl] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    obtain ⟨sz, rn', rt', rfl, hrn, -, hsz'⟩ := toArmInst_excl rfl ha
    obtain ⟨q, rfl, hq, rfl⟩ := x_of_alloc (hall (⟨u, .int, .use, .early, .reg⟩, r0) (by simp)) hrn
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .loadAcquire ty (.x 1) (.x 0) fl) hops rfl rfl,
      linesEvs_single hca, hac]
    obtain rfl := sz_eq hsz' hszc
    simp only [Reg.encSP, show (0 : Nat) ≤ 30 by omega, ite_true, pure, Except.pure,
      Except.ok.injEq] at hrnc
    subst hrnc
    refine exclEvs_regs (ofNat5_ne31 (by omega)) (by decide) ?_ (by rw [placeUses_setMem]; rfl)
      (fun h => absurd rfl h)
    rw [read_gpr_sm, placeUses_setMem, read_gpr_sm,
      show useVals #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩] #[.x q, r1] s =
        [regVal s (.x q)] by simp [useVals, Operand.isUse],
      show placeUses #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩]
        (canonRegs #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩]) [regVal s (.x q)] w =
        setReg w (.x 0) (regVal s (.x q)) by
          simp [placeUses, Operand.isUse, canonRegs, canonReg, canonBase, List.range_succ]]
    simp [setReg, read_gpr, Arm.r_of_w_same, lo64_regVal, rnum]

/-- **`stlr` is a one-event form** (`OneEvForm`): the allocated `stlr`'s write is the
canonical one's (the address register's value, the access size, the data register's bytes). -/
theorem stlr_form {F : BitVec 64 → Prop} {ctx : FnCtx} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} (hfo : FormOk ctx (.storeRelease ty rt rn fl) = true) :
    OneEvForm F ctx (.storeRelease ty rt rn fl) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨u, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  have hty : AtomTy ty := by simpa [FormOk] using hfo
  have hops : (MInst.storeRelease ty (.vreg d .int) (.vreg u .int) fl).operands =
      .ok #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .use, .early, .reg⟩] := rfl
  have hasg2 : ∀ r0 r1 : Reg, (MInst.storeRelease ty (.vreg d .int) (.vreg u .int) fl).assign #[r0, r1] =
      .ok (.storeRelease ty r1 r0 fl) := fun _ _ => rfl
  obtain ⟨a0, ha0⟩ := atom_toArmInst_ok hty 1 0 31 1 0 (by omega) (by omega)
  have hca : (Insn.stlr ty.bits (.x 1) (.x 0)).toArmInst env0 = .ok a0.norm := by
    show ArmInst.norm <$> Insn.armFields.exclFields _ _ _ _ _ _ = _
    rw [ha0]; rfl
  obtain ⟨szc, rnc, rtc, hac, hrnc, hrtc, hszc⟩ := toArmInst_excl rfl hca
  refine ⟨rfl, hfo, ⟨_, _, _, _, _, hops, rfl, rfl, hca, hac ▸ ctlIndep_excl _⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg2] at hasg; cases hasg
    exact ⟨_, _, fun ps => rfl⟩
  · intro ops regs i' x t env a hops' hsz hasg hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg2] at hasg; cases hasg
    rw [show (MInst.storeRelease ty r1 r0 fl).lines ctx {} =
      .ok ([.ins (.stlr ty.bits r1 r0) fl.trapCode], {}) from rfl] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    obtain ⟨sz, rn', rt', rfl, -, -, -⟩ := toArmInst_excl rfl ha
    refine ⟨fun rel rs rn h => by simp [clsOf, exclCls] at h, fun y e he => ?_⟩
    obtain ⟨hk, hn⟩ := exclEvs_mem (show e ∈ exclEvs _ y from he)
    rw [hk]
    exact ⟨by simp [exclKind], fun _ => hn⟩
  · intro s w ops regs i' x t env a hsw hops' hsz hall hasg hl ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, r1, rfl⟩ := regs2 hsz
    rw [hasg2] at hasg; cases hasg
    rw [show (MInst.storeRelease ty r1 r0 fl).lines ctx {} =
      .ok ([.ins (.stlr ty.bits r1 r0) fl.trapCode], {}) from rfl] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Line.ins.injEq, and_true] at hl
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hl
    obtain ⟨sz, rn', rt', rfl, hrn, hrt, hsz'⟩ := toArmInst_excl rfl ha
    obtain ⟨q, rfl, hq, rfl⟩ := x_of_alloc (hall (⟨u, .int, .use, .early, .reg⟩, r0) (by simp)) hrn
    obtain ⟨p, rfl, hp, rfl⟩ := x_of_allocZR (hall (⟨d, .int, .use, .early, .reg⟩, r1) (by simp)) hrt
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [IselMemAux.straightEvs_one_line (ic := .storeRelease ty (.x 1) (.x 0) fl) hops rfl rfl,
      linesEvs_single hca, hac]
    obtain rfl := sz_eq hsz' hszc
    simp only [Reg.encSP, show (0 : Nat) ≤ 30 by omega, ite_true, pure, Except.pure,
      Except.ok.injEq] at hrnc
    simp only [Reg.encZR, show (1 : Nat) ≤ 30 by omega, ite_true, pure, Except.pure,
      Except.ok.injEq] at hrtc
    subst hrnc hrtc
    have hu : useVals #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .use, .early, .reg⟩] #[.x q, .x p] s =
        [regVal s (.x q), regVal s (.x p)] := by simp [useVals, Operand.isUse]
    have hpu : placeUses #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .use, .early, .reg⟩]
        (canonRegs #[⟨u, .int, .use, .early, .reg⟩, ⟨d, .int, .use, .early, .reg⟩])
        [regVal s (.x q), regVal s (.x p)] w = setReg (setReg w (.x 0) (regVal s (.x q))) (.x 1) (regVal s (.x p)) := by
      simp [placeUses, Operand.isUse, canonRegs, canonReg, canonBase, List.range_succ]
    refine exclEvs_regs (ofNat5_ne31 (by omega)) (by decide) ?_ (by rw [placeUses_setMem]; rfl) ?_
    · rw [read_gpr_sm, placeUses_setMem, read_gpr_sm, hu, hpu]
      simp [setReg, read_gpr, Arm.r_of_w_same, Arm.r_of_w_different, lo64_regVal, rnum]
    · intro _
      rw [ldst_read_sm, placeUses_setMem, ldst_read_sm, hu, hpu]
      simp [ldst_read, read_gpr_zr, setReg, read_gpr, Arm.r_of_w_same, lo64_regVal, rnum,
        ofNat5_ne31 (show p ≤ 30 by omega)]

/-! ## The scope and the run level -/

/-- The memory forms of the scope: event-free (`NoEvForm`), `fence`, a covered `ldar` or `stlr`. -/
def MemForm (ctx : FnCtx) (i : MInst) : Prop :=
  NoEvForm ctx i ∨ i = .fence ∨ (∃ ty rt rn fl, i = .loadAcquire ty rt rn fl ∧ FormOk ctx i = true) ∨
    ∃ ty rt rn fl, i = .storeRelease ty rt rn fl ∧ FormOk ctx i = true

/-- **The scope of `arm_alloc_refines_mem`**: every instruction of the function is a memory form
(a superset of `NoEvScope`). -/
def MemScope (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
    MemForm R.ctx i

theorem memScope_of_noEv {R : RL} (h : NoEvScope R) : MemScope R :=
  fun b vb k i hb hi => .inl (h b vb k i hb hi)

/-- **The per-item obligation of the memory scope.** -/
theorem itemSim_mem {R : RL} (hR : R.Wf) (hsc : MemScope R) (hnm : NoMoves R) :
    ItemSim Policy.arm R.step (fun _ _ => True) (SrcStep R) (RelQ R) (Done R)
      (fun c => c.measure) (PrivA R) := by
  refine itemSim_of_op hnm fun s mon b k allocs its m w evs0 c0 hq hA hs ls t' hr => ?_
  have hs' := hs
  cases hs' with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi _ _ _ _ =>
  have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
    fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
  rcases hsc b vb k i hvb hi with h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩
  · exact noev_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr
  · exact fence_op hR hq hA hs (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr
  · exact oneEv_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr
  · exact oneEv_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr

/-- **Layer 4b for the memory scope** (module doc): every precise Arm run from a `Q`-related
state realizes a run of the allocated code (`MTRun`) with `Refines` (equal kinds, the addresses
outside the world private, the monitor pairs atomic), up to the allocated code's return, trap or
undefined behaviour (`Done`), for functions whose instructions are event-free, `fence`, `ldar` or
`stlr` (`MemScope`) and whose allocation has no moves. -/
theorem arm_alloc_refines_mem {R : RL} (hR : R.Wf) (hsc : MemScope R) (hnm : NoMoves R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_mem hR hsc hnm) hr (RelQ.of hq hA)
  exact ⟨n, trS, cE, ψ, hn, mtrun_of_srun hs, href, hend⟩

/-! ## Precise one-step runs -/

/-- **At an unhooked instruction line, every memory gives a precise one-step run** of the machine
`R.step`, its label the instruction's events on that memory (a store exclusive: with the monitor
armed, `Policy.arm.succ mon`). -/
theorem exists_prun_lineS {R : RL} (hR : R.Wf) {s : ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.fa.lines.toList[j]? = some (.ins x t)) (hh : x.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (mon : Mon)
    (hsucc : ∀ a, x.toArmInst (R.envOf j) = .ok a → ∀ rel rs rn, clsOf a = .stx rel rs rn →
      Policy.arm.succ mon)
    (m : Memory) :
    ∃ a t', x.toArmInst (R.envOf j) = .ok a ∧ stepEvs (setMem m s) = instEvs a (setMem m s) ∧
      PRun Policy.arm R.step (fun _ _ => True) (s, mon) [⟨stepEvs (setMem m s), false⟩] t' := by
  have hline : ∀ m', ∃ a, x.toArmInst (R.envOf j) = .ok a ∧ R.step (setMem m' s) = exec_inst a (setMem m' s) ∧
      stepEvs (setMem m' s) = instEvs a (setMem m' s) ∧ decodeAt (setMem m' s) = some a := fun m' =>
    stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh (by rw [setMem_program]; exact hprog)
      (by rw [r_setMem]; exact hpc) (by rw [r_setMem]; exact herr)
  obtain ⟨a, ha, -, hev, hdec⟩ := hline m
  have hl := ArmPrecise.len_stepEvs (setMem m s)
  have hn := ArmPrecise.n_stepEvs (setMem m s)
  have hag : Agrees (stepEvs (setMem m s)) (applyR (stepEvs (setMem m s)) s.mem) :=
    ArmPrecise.agrees_applyR hl hn _
  have hk := kindsOk_stepEvs (setMem m s)
  rw [ArmPrecise.cls_setMem] at hk
  have hfoot : Footprint R.step (setMem m s) (stepEvs (setMem m s)) := by
    intro m' hm'
    have e := footprint_exec_inst a (setMem m s) m' (by rw [← hev]; exact hm')
    rw [← hev] at e
    simp only [setMem_setMem, setMem_mem] at e ⊢
    obtain ⟨a1, ha1, hs1, -⟩ := hline m'
    obtain ⟨a2, ha2, hs2, -⟩ := hline (applyR (stepEvs (setMem m s)) m)
    rw [ha] at ha1 ha2
    cases ha1; cases ha2
    rw [hs1, hs2]; exact e
  have hdec0 : decodeAt s = some a := by rw [← decodeAt_setMem m s]; exact hdec
  refine ⟨a, _, ha, hev, .cons (.exec hk hag (ArmPrecise.footprint_of_setMem hfoot hag)
    (fun rel rs rn h => hsucc a ha rel rs rn (by rw [cls_of_decode hdec0] at h; exact h)))
    (.inr ⟨m, rfl⟩) trivial .nil⟩

/-- **At an unhooked instruction line, every memory gives a precise one-step run** of the machine
`R.step`, its label the instruction's events on that memory (no store exclusive). -/
theorem exists_prun_line {R : RL} (hR : R.Wf) {s : ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.fa.lines.toList[j]? = some (.ins x t)) (hh : x.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None)
    (hnstx : ∀ a, x.toArmInst (R.envOf j) = .ok a → ∀ rel rs rn, clsOf a ≠ .stx rel rs rn)
    (mon : Mon) (m : Memory) :
    ∃ a t', x.toArmInst (R.envOf j) = .ok a ∧ stepEvs (setMem m s) = instEvs a (setMem m s) ∧
      PRun Policy.arm R.step (fun _ _ => True) (s, mon) [⟨stepEvs (setMem m s), false⟩] t' :=
  exists_prun_lineS hR hj hh hprog hpc herr mon
    (fun a ha rel rs rn h => absurd h (hnstx a ha rel rs rn)) m

end Concurrency.ArmAllocThread

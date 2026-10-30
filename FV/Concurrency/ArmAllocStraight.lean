import FV.Concurrency.AllocThread
import FV.Concurrency.ArmAllocLines
import FV.Concurrency.ArmAllocItem

/-!
# Layer 4b for the items without memory events (T2h, #311)

The per-item obligation `ArmAllocThread.ItemSim` of layer 4b for the register-level relation
(`RelQ`: `QA`, i.e. `Q ∧ AInv` or a return tail) and the allocated code's thread step
(`SrcStep`: `AllocThread.MTStep` under the activation's `csem`, events `cEvs`), for the items
whose instruction has no memory kind
(`Code.akinds`): the straight-line covered forms without memory access (`FormOk`), `args`, and
every item whose step ends the function (`rets`, `udf`: the Arm run after it is the caller's):

* `itemSim_noev`: for the functions whose instructions are of these kinds (`NoEvScope`) and whose
  allocation has no moves (`NoMoves`), `ItemSim` holds with no premise on the Arm's reads: the Arm
  runs the item's lines (`realizes_op_lines`), which have no events (`nomem_execLines`), so the
  precise run is the single-core run (`prun_nil`);
* **`arm_alloc_refines_noev`**: such a function's precise Arm runs from `Q`-related states
  realize runs of the allocated code (`AllocThread.MTRun`) with `ThreadRefine.Refines`, up to the
  allocated code's return, trap or undefined behaviour (`Done`).
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
open Code VCodeEvents

/-- The allocated code's thread step under the activation's semantics. -/
abbrev SrcStep (R : RL) : MConf CV ArmState → List Ev → MConf CV ArmState → Prop :=
  MTStep R.vc R.rf R.sem ckeep (cEvs R.F R.ctx)

/-- The register-level relation at item boundaries (the monitor is free): `QA`, i.e. `Q ∧ AInv`,
or a return tail (`RetTail`: the callee restores emit no code, the epilogue's pops restore the
saved registers, so after a restore the store is the machine's but at the restored registers). -/
def RelQ (R : RL) (t : ArmState × Mon) (c : MConf CV ArmState) : Prop := QA R t.1 c

theorem RelQ.of {R : RL} {t : ArmState × Mon} {c : MConf CV ArmState} (hq : Q R t.1 c)
    (hA : AInv R c) : RelQ R t c := .inl ⟨hq, hA⟩

/-- `RelQ` at a configuration that is not running. -/
theorem relQ_ret {R : RL} {t : ArmState × Mon} {vals : List CV} {m : Loc → CV} {w : ArmState} :
    RelQ R t (.ret vals m w) := .inl ⟨trivial, trivial⟩

theorem relQ_halt {R : RL} {t : ArmState × Mon} {w : ArmState} : RelQ R t (.halt w) :=
  .inl ⟨trivial, trivial⟩

/-- `RelQ` at an item gives `Q` with the machine's store. -/
theorem RelQ.q {R : RL} {t : ArmState × Mon} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (h : RelQ R t (.run ⟨b, its, m, w⟩)) : ∃ mt, Q R t.1 (.run ⟨b, its, mt, w⟩) :=
  qa_q h

/-- The allocated code is done: returned, trapped, or without a step (undefined behaviour). -/
def Done (R : RL) (c : MConf CV ArmState) : Prop :=
  (∃ vals m w, c = .ret vals m w) ∨ (∃ w, c = .halt w) ∨ ∀ evs c', ¬ SrcStep R c evs c'

/-- The private locations: the addresses outside the activation's world (`RL.F`: its frame, the
callees' dead stack, the kept addresses and the code). -/
def PrivA (R : RL) (l : Nat) : Prop := R.F (BitVec.ofNat 64 l)

/-- The allocation has no moves. -/
def NoMoves (R : RL) : Prop :=
  ∀ (b : Nat) (items : Array RItem), R.rf.blocks[b]? = some items →
    ∀ src dst, RItem.move src dst ∉ items.toList

/-- Every instruction of the function has no memory kind: a covered straight-line form, `args`,
`rets` or `udf`. -/
def NoEvScope (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
    (i.isCtl = false ∧ FormOk R.ctx i = true ∧ akinds i = []) ∨ (∃ ds, i = .args ds) ∨
      (∃ us, i = .rets us) ∨ (∃ c, i = .udf c)

/-! ## Arm runs without events -/

theorem evAt_evTr_nil {L : List Lab} (h : ∀ l ∈ L, l.evs = []) (p : Nat × Nat) :
    evAt (evTr L) p = none := by
  simp only [evAt, evTr, List.getElem?_map]
  cases hl : L[p.1]? with
  | none => rfl
  | some l => simp [h l (List.mem_of_getElem? hl)]

theorem privW_of_nil {Priv : Nat → Prop} {L : List Lab} (h : ∀ l ∈ L, l.evs = []) :
    PrivW Priv (evTr L) := fun p y hy => by rw [evAt_evTr_nil h] at hy; cases hy

theorem img_nil {Priv : Nat → Prop} {L : List Lab} (h : ∀ l ∈ L, l.evs = [])
    (φ : Nat → Nat × Nat) : Img Priv [] (evTr L) φ where
  ev k hk := absurd hk (Nat.not_lt_zero _)
  mono k k' _ h2 := absurd h2 (Nat.not_lt_zero _)
  priv p y hy := by rw [evAt_evTr_nil h] at hy; cases hy
  shared e he := absurd he List.not_mem_nil
  shape := .inl ⟨Nat.zero_le _, fun e he => absurd he List.not_mem_nil⟩
  pair h2 := by simp at h2

theorem patch_nil (w : ArmState) : patch [] w = w := rfl

/-- The completing case of `ItemSim`: the item's segment of `n` Arm steps. -/
abbrev ItemSimOut (P : Policy) (f : ArmState → ArmState) (ok : ArmState → Lab → Prop) {C : Type}
    (S : C → List Ev → C → Prop) (Rel : ArmState × Mon → C → Prop) (Priv : Nat → Prop)
    (μ : C → Nat) (t : ArmState × Mon) (c : C) (ls : List Lab) : Prop :=
  ∃ n evs c' t1 φ, n ≤ ls.length ∧ (0 < n ∨ μ c' < μ c) ∧ S c evs c' ∧
    PRun P f ok t (ls.take n) t1 ∧ Rel t1 c' ∧ Img Priv evs (evTr (ls.take n)) φ

/-! ## The items -/

theorem q_items {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hq : Q R s (.run ⟨b, its, m, w⟩)) :
    ∃ items, R.rf.blocks[b]? = some items ∧ ∀ it ∈ its, it ∈ items.toList := by
  obtain ⟨items, pre, hit, hsplit⟩ := Q.split hq
  exact ⟨items, hit, fun it h => by rw [hsplit]; exact List.mem_append_right _ h⟩

theorem measure_run {b : Nat} {its : List RItem} {m : Loc → CV} {w : ArmState} :
    (MConf.run ⟨b, its, m, w⟩ : MConf CV ArmState).measure = its.length := rfl

/-- The lines of an allocated instruction at line `j` are the function's lines from `j`. -/
theorem lines_at {R : RL} {j : Nat} {ls1 T : List Line} (h : R.L.drop j = ls1 ++ T) :
    ∀ k ln, ls1[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
  intro k ln hk
  have := congrArg (·[k]?) h
  simp only [List.getElem?_drop, RL.L] at this
  rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
  exact hk

/-- A `rets` item's step returns. -/
theorem srcStep_rets {R : RL} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {evs : List Ev} {c' : MConf CV ArmState} {vb : VBlock} {us : List (Reg × Reg)}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us))
    (hs : SrcStep R (.run ⟨b, .op k allocs :: its, m, w⟩) evs c') :
    ∃ vals m' w', c' = .ret vals m' w' := by
  cases hs with
  | @op _ _ _ _ _ _ vb0 i0 ops0 _ _ hvb0 hi0 hops0 _ _ hst =>
  rw [hvb] at hvb0; cases hvb0; rw [hi] at hi0; cases hi0
  cases hst with
  | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
    rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops0] at hops1; cases hops1
    simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨-, -, rfl⟩ := hsem
    cases hn with
    | ret _ => exact ⟨_, _, _, rfl⟩

/-- `RelQ` at an instruction item: `Q ∧ AInv`, or the item is the `rets` of a return tail, whose
step returns without events. -/
theorem RelQ.op' {R : RL} {t : ArmState × Mon} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : ArmState} {evs : List Ev} {c' : MConf CV ArmState}
    (h : RelQ R t (.run ⟨b, .op k allocs :: its, m, w⟩))
    (hs : SrcStep R (.run ⟨b, .op k allocs :: its, m, w⟩) evs c') :
    (Q R t.1 (.run ⟨b, .op k allocs :: its, m, w⟩) ∧ AInv R (.run ⟨b, .op k allocs :: its, m, w⟩)) ∨
      (evs = [] ∧ ∃ vals m' w', c' = .ret vals m' w') := by
  rcases h with h | h
  · exact .inl h
  · right
    simp only [RetTail] at h
    obtain ⟨_mt, _D, _hq, _hm, vb, pend, k', a', rest, us, hvb, he, hk, htl⟩ := h
    rcases pend with _ | ⟨it, pend⟩
    · simp only [List.nil_append, List.cons.injEq, RItem.op.injEq] at he
      obtain ⟨⟨rfl, -⟩, -⟩ := he
      refine ⟨?_, srcStep_rets hvb hk hs⟩
      cases hs with
      | @op _ _ _ _ _ _ vb0 i0 ops0 _ _ hvb0 hi0 hops0 hevs _ _ =>
        rw [hvb] at hvb0; cases hvb0; rw [hk] at hi0; cases hi0
        exact hevs.trans (cEvs_nil rfl _ _)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp [retTailOk, RItem.restoreReg, RItem.avoids] at htl

/-- `RelQ` at an instruction item whose step does not return is `Q ∧ AInv` (a return tail ends
at its `rets`, whose step returns). -/
theorem RelQ.op {R : RL} {t : ArmState × Mon} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : ArmState} {evs : List Ev} {c' : MConf CV ArmState}
    (h : RelQ R t (.run ⟨b, .op k allocs :: its, m, w⟩))
    (hs : SrcStep R (.run ⟨b, .op k allocs :: its, m, w⟩) evs c')
    (hnr : ∀ vals m' w', c' ≠ .ret vals m' w') :
    Q R t.1 (.run ⟨b, .op k allocs :: its, m, w⟩) ∧ AInv R (.run ⟨b, .op k allocs :: its, m, w⟩) := by
  rcases RelQ.op' h hs with h | ⟨-, vals, m', w', rfl⟩
  · exact h
  · exact absurd rfl (hnr vals m' w')

/-- A step returning without events: no Arm step (for a measure `μ` lower at the return). -/
theorem itemSimOut_retμ {R : RL} {ok : ArmState → Lab → Prop} {μ : MConf CV ArmState → Nat}
    {t : ArmState × Mon} {c : MConf CV ArmState} {vals : List CV} {m' : Loc → CV} {w' : ArmState}
    {ls : List Lab} (hs : SrcStep R c [] (.ret vals m' w')) (hμ : μ (.ret vals m' w') < μ c) :
    ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) μ t c ls :=
  ⟨0, [], _, t, fun _ => (0, 0), Nat.zero_le _, .inr hμ, hs,
    by rw [List.take_zero]; exact .nil, relQ_ret, img_nil (by simp) _⟩

/-- A step returning without events: no Arm step. -/
theorem itemSimOut_ret {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon} {b : Nat}
    {it : RItem} {its : List RItem} {m : Loc → CV} {w : ArmState} {vals : List CV}
    {m' : Loc → CV} {w' : ArmState} {ls : List Lab}
    (hs : SrcStep R (.run ⟨b, it :: its, m, w⟩) [] (.ret vals m' w')) :
    ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) (fun c => c.measure) t
      (.run ⟨b, it :: its, m, w⟩) ls :=
  itemSimOut_retμ hs (by simp [MConf.measure])

/-- **The per-item obligation of the event-free items** (module doc). -/
theorem itemSim_noev {R : RL} (hR : R.Wf) (hsc : NoEvScope R) (hnm : NoMoves R) :
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
  have hsc' := hsc b vb k i hvb hi
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
      by rw [List.take_zero]; exact .nil, RelQ.of hq' hA', img_nil (by simp) _⟩
  -- a step ending the function: no Arm step
  by_cases hterm : (∃ vals m' w', c0 = .ret vals m' w') ∨ ∃ w', c0 = .halt w'
  · rcases hterm with ⟨vals, m', w', rfl⟩ | ⟨w', rfl⟩ <;>
    exact .inr (.inl (zero _ (Nat.zero_le _) hstep trivial trivial))
  obtain ⟨hq, hA⟩ : Q R s _ ∧ AInv R _ :=
    RelQ.op hqa hstep fun vals m' w' e => hterm (.inl ⟨vals, m', w', e⟩)
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
      r1, RelQ.of hq'' (aInv_step hR hq hA hm''), img_nil hev1 _⟩)
  · obtain ⟨-, hev, -⟩ := prun_nil hr fun i hi => hnom i (by omega)
    exact .inr (.inr (.inr (privW_of_nil hev)))

/-! ## The run level -/

theorem mtrun_of_srun {R : RL} : ∀ {c c' : MConf CV ArmState} {tr : List (List Ev)},
    SRun (SrcStep R) c tr c' → MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c tr c'
  | _, _, _, .nil => .nil
  | _, _, _, .cons h r => .cons h (mtrun_of_srun r)

/-- **Layer 4b for the event-free functions** (module doc): every precise Arm run from a
`Q`-related state realizes a run of the allocated code (`MTRun`) with `Refines` (equal kinds, the
addresses outside the world private, the monitor pairs atomic), up to the allocated code's
return, trap or undefined behaviour (`Done`). -/
theorem arm_alloc_refines_noev {R : RL} (hR : R.Wf) (hsc : NoEvScope R) (hnm : NoMoves R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_noev hR hsc hnm) hr (RelQ.of hq hA)
  exact ⟨n, trS, cE, ψ, hn, mtrun_of_srun hs, href, hend⟩

end Concurrency.ArmAllocThread

import FV.Concurrency.ArmAllocMem
import FV.Concurrency.MoveEvs

/-!
# Layer 4b with the allocation's moves (T2k, #311)

`spillAlloc` saves the callee-saved registers by moves at every entry (`spillSaves`) and keeps
every vreg in a frame slot (loads and stores around each instruction), so no allocation of a
compiled function satisfies `NoMoves`. A move's code (`RAFrame.moveInsts`: `mov`, slot stores
and loads at `sp + off`, through x16 beyond 32 KiB) writes only the activation's frame, which is
private (`PrivA`), and its reads are of the frame too. In an arbitrary run of the Arm thread such
a read returns any bytes, so the run level carries **the run condition `OkPriv`**: the step's
reads of private locations return the thread's own bytes (its state's memory). For the compiled
code of a thread this is what `PrivCoh.privCoh_of_consistent` gives (reads of locations only the
thread writes read its latest write there).

* `OkPriv`, `PRun.mono`: the run condition, and runs under a stronger condition;
* `prun_priv`: a precise run whose single-core steps access only private locations and are no
  store exclusives is, under `OkPriv`, the single-core run (its labels the single-core events);
* `move_op`: **the per-item obligation at a move**: the Arm runs the move's lines (the
  single-core run, `Q` after it, `Backend.Proof.realizes_move`'s proof), all of whose events are
  private (`MoveCodeOk`, which every activation's move code is: `moveCodeOk`, from
  `Backend.Proof.moveLines_evs`, `moveLines_noStx`); the source step has
  no event;
* `itemSim_of_op_ok`: `ArmAllocMem.itemSim_of_op` without `NoMoves`: under `OkPriv`, `ItemSim`
  holds when it holds (under any run condition) at every instruction item with a source step;
* **`arm_alloc_refines_mv`**: `arm_alloc_refines_mem` for allocations with moves (every
  allocation `spillAlloc` produces), for precise Arm runs under `OkPriv`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
open Code VCodeEvents

/-! ## The run condition -/

/-- **The step's reads of private locations return the thread's own bytes**: every read event
whose (start) address is private (`PrivA`) holds the bytes of the thread's memory. -/
def OkPriv (R : RL) (s : ArmState) (l : Lab) : Prop :=
  ∀ e ∈ l.evs, e.k.dir = .R → PrivA R e.addr.toNat → readM e.n e.addr s.mem = e.val

theorem PRun.mono {P : Policy} {f : ArmState → ArmState} {ok ok' : ArmState → Lab → Prop}
    (h : ∀ s l, ok s l → ok' s l) :
    ∀ {t t' : ArmState × Mon} {ls : List Lab}, PRun P f ok t ls t' → PRun P f ok' t ls t'
  | _, _, _, .nil => .nil
  | _, _, _, .cons hs hp ho hr => .cons hs hp (h _ _ ho) (PRun.mono h hr)

theorem privA_addr {R : RL} {a : BitVec 64} : PrivA R a.toNat ↔ R.F a := by
  simp [PrivA, BitVec.ofNat_toNat]

/-- The re-read events keep the addresses. -/
theorem mem_reread {M : Memory} {E : List Ev} {e : Ev} (h : e ∈ ArmPrecise.reread M E) :
    ∃ e0 ∈ E, e.k = e0.k ∧ e.addr = e0.addr ∧ e.n = e0.n := by
  simp only [ArmPrecise.reread, List.mem_map] at h
  obtain ⟨e0, he0, rfl⟩ := h
  refine ⟨e0, he0, ?_⟩
  simp only [ArmPrecise.reread1]
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- **A precise step under `OkPriv` whose single-core step accesses only private locations** and
is no store exclusive is the single-core step. -/
theorem tstep_priv {R : RL} {s : ArmState} {mon : Mon} {l : Lab} {t1 : ArmState × Mon}
    (hs : TStep Policy.arm R.step (s, mon) l t1) (hp : ArmPrecise.Precise s l) (ho : OkPriv R s l)
    (hpv : ∀ e ∈ stepEvs s, R.F e.addr) (hx : NoStx s) :
    t1.1 = R.step s ∧ l.evs = stepEvs s := by
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc => exact absurd hc (hx _ _ _)
  have hag : Agrees l.evs s.mem := by
    intro e he hR
    rcases hp with h | ⟨M, hM⟩
    · rw [hxf] at h; cases h
    · have he' := he
      rw [hM, ArmPrecise.stepEvs_setMem] at he'
      obtain ⟨e0, he0, -, ha, -⟩ := mem_reread he'
      exact ho e he hR (privA_addr.2 (ha ▸ hpv e0 he0))
  obtain ⟨h1, h2, -⟩ := tstep_own hs hp hag hxf
  exact ⟨h1, h2⟩

/-- **A precise run under `OkPriv` through single-core steps accessing only private locations**
(no store exclusive) is the single-core run; its labels are that run's events. -/
theorem prun_priv {R : RL} : ∀ {L : List Lab} {s : ArmState} {mon : Mon} {t' : ArmState × Mon},
    PRun Policy.arm R.step (OkPriv R) (s, mon) L t' →
    (∀ i < L.length, (∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) →
    t'.1 = iterN R.step L.length s ∧ evTr L = segEvs R.step L.length s
  | [], _, _, _, .nil, _ => ⟨rfl, rfl⟩
  | l :: L, s, mon, t', .cons (t1 := t1) hs hp ho hr, h => by
    obtain ⟨h1, h2⟩ := tstep_priv hs hp ho (h 0 (by simp)).1 (h 0 (by simp)).2
    obtain ⟨s1, mon1⟩ := t1
    simp only at h1
    subst h1
    have ih := prun_priv hr fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [iterN] using this
    refine ⟨by simpa [iterN] using ih.1, ?_⟩
    simp only [evTr, List.map_cons, List.length_cons, segEvs] at ih ⊢
    rw [h2, ← ih.2]

theorem stepEvs_mem_segEvs {f : ArmState → ArmState} :
    ∀ {n i : Nat} {s : ArmState}, i < n → stepEvs (iterN f i s) ∈ segEvs f n s
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, s, _ => List.mem_cons_self
  | n + 1, i + 1, s, h => List.mem_cons_of_mem _ (stepEvs_mem_segEvs (n := n) (s := f s) (by omega))

/-- A segment of private writes images the step without events. -/
theorem img_privW {Priv : Nat → Prop} {tr : List (List Ev)} (h : PrivW Priv tr)
    (φ : Nat → Nat × Nat) : Img Priv [] tr φ where
  ev k hk := absurd hk (Nat.not_lt_zero _)
  mono k k' _ h2 := absurd h2 (Nat.not_lt_zero _)
  priv p y hy hW _ := h p y hy hW
  shared e he := absurd he List.not_mem_nil
  shape := .inl ⟨Nat.zero_le _, fun e he => absurd he List.not_mem_nil⟩
  pair h2 := by simp at h2

/-- The events of a segment of single-core steps accessing only private locations are private
writes. -/
theorem privW_segEvs {R : RL} {n : Nat} {s : ArmState}
    (h : ∀ i < n, ∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) :
    PrivW (PrivA R) (segEvs R.step n s) := by
  intro p y hy _
  obtain ⟨j, k⟩ := p
  simp only [evAt] at hy
  cases hj : (segEvs R.step n s)[j]? with
  | none => rw [hj] at hy; cases hy
  | some x =>
    rw [hj] at hy
    simp only [Option.bind_some] at hy
    obtain ⟨i, hi, rfl⟩ := mem_segEvs (List.mem_of_getElem? hj)
    exact privA_addr.2 (h i hi y (List.mem_of_getElem? hy))

/-! ## The per-item obligation at a move -/

/-- **What layer 4b needs of move code** (`Backend.Proof.moveLines_evs`, `moveLines_noStx`): the
events of a checked move's lines, run from a state with the body's `sp`, are private, and no line
is a store exclusive. -/
def MoveCodeOk (R : RL) : Prop :=
  ∀ (c : CheckCtx) (wh : String) (src dst : Loc), c.checkMove wh src dst = .ok () →
    Live R.rf src → Live R.rf dst →
    (∀ a b, src = .reg (.v a) → dst = .reg (.v b) → R.rf.floatMove = true) →
    ∀ code, R.fr.moveInsts src dst = .ok code → ∀ (s : ArmState), spOf s = R.spB →
      CheckSPAlignment s → ∀ ls ps ps', codeLinesE R.ctx R.af code ps = .ok (ls, ps') →
      (∀ env, ∀ e ∈ linesEvs env ls s, R.F e.addr) ∧
      (∀ x t, Line.ins x t ∈ ls → ∀ env ai, x.toArmInst env = .ok ai →
        ∀ rel rs rn, clsOf ai ≠ .stx rel rs rn)

/-- **Every activation's move code is `MoveCodeOk`** (`moveLines_evs`, with the frame layout of
`RL.frameOk`; `moveLines_noStx`). -/
theorem moveCodeOk {R : RL} (hR : R.Wf) : MoveCodeOk R :=
  fun _ _ _ _ hchk hLs hLd hT _ hmi _ hsp hal _ _ _ hls =>
    ⟨fun env => moveLines_evs (R.frameOk hR) R.ctx R.af hchk hLs hLd hT hmi hsp hal hls env,
      moveLines_noStx R.ctx R.af hchk hmi hls⟩

/-- The configuration at a move item. -/
abbrev MvC (b : Nat) (src dst : Loc) (its : List RItem) (m : Loc → CV) (w : ArmState) :
    MConf CV ArmState := .run ⟨b, .move src dst :: its, m, w⟩

/-- **Straight-line lines `ls1` at line `j`, run by the machine from `s` to `s'`** (the premises
of `step_execLines`). -/
structure LinesAt (R : RL) (j : Nat) (ls1 : List Line) (s s' : ArmState) : Prop where
  at_ : ∀ k ln, ls1[k]? = some ln → R.fa.lines.toList[j + k]? = some ln
  hook : ∀ x t, Line.ins x t ∈ ls1 → x.hooked = false
  prog : s.program = R.fb.program R.base
  pc : Arm.r .PC s = R.base + BitVec.ofNat 64 (lineOffset R.fa.lines.toList j)
  err : Arm.r .ERR s = .None
  inter : InterOk ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ ls1 s
  run : execLines ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ ls1 s = some s'

theorem LinesAt.iter {R : RL} (hR : R.Wf) {j : Nat} {ls1 : List Line} {s s' : ArmState}
    (h : LinesAt R j ls1 s s') : iterN R.step ls1.length s = s' :=
  iterN_execLines hR.layout hR.lm hR.fit ls1 j s s' h.at_ h.hook h.prog h.pc h.err h.inter h.run

theorem LinesAt.seg {R : RL} (hR : R.Wf) {j : Nat} {ls1 : List Line} {s s' : ArmState}
    (h : LinesAt R j ls1 s s') :
    (segEvs R.step ls1.length s).flatten = linesEvs (R.envOf j) ls1 s :=
  segEvs_execLines (X := R.X) (H := R.H) (base := R.base) hR.layout hR.lm hR.fit ls1 j s s' h.at_
    h.hook h.prog h.pc h.err h.inter h.run

/-- **A move's lines from `Q`** (`Backend.Proof.realizes_move`'s proof): the lines of its code
run from `s` (`LinesAt`), `Q` at the next item after them, every event of their single-core
steps private, no store exclusive. -/
theorem move_lines {R : RL} (hR : R.Wf) {s : ArmState} {b : Nat} {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState} (hq : Q R s (MvC b src dst its m w)) :
    ∃ j ls1 s' code, R.fr.moveInsts src dst = .ok code ∧
      (∀ ps, codeLinesE R.ctx R.af code ps = .ok (ls1, ps)) ∧ LinesAt R j ls1 s s' ∧
      Q R s' (.run ⟨b, its, upd m dst (m src), w⟩) ∧
      ∀ i < ls1.length, (∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s) := by
  obtain ⟨j, vb, items, pre, code, ls0, ps1, ps2, T, hvb, hit, hsplit, hchk, hcode, hls, htr, hdrop,
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
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1' ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
  have hat := lines_at hdrop'
  have hhook : ∀ x t, Line.ins x t ∈ ls1' → x.hooked = false := fun x t h => by
    obtain ⟨x', t', e, hh⟩ := hins _ h; cases e; exact hh
  have hlat : LinesAt R j ls1' s s' :=
    ⟨hat, hhook, by rw [hst.prog], by rw [hpc]; rfl, hst.err, hint _, hrun _⟩
  -- the move's lines: private events, no store exclusive
  obtain ⟨hev, hns⟩ := moveCodeOk hR c wh src dst hcm hLs hLd hT _ hc1 s hst.sp hst.align ls1' ps1 ps1
    (hcl ps1)
  have hseg := hlat.seg hR
  have hstep := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hat hhook
    (by rw [hst.prog]) (by rw [hpc]; rfl) hst.err (hint _) (hrun _)
  have hpriv : ∀ i < ls1'.length, (∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧
      NoStx (iterN R.step i s) := by
    intro i hi
    refine ⟨fun e he => hev (R.envOf j) e ?_, fun rel rs rn hc => ?_⟩
    · have hm : e ∈ (segEvs R.step ls1'.length s).flatten :=
        List.mem_flatten.2 ⟨_, stepEvs_mem_segEvs hi, he⟩
      rw [hseg] at hm
      exact hm
    · obtain ⟨x, t, a, hli, ha, hdec, -, -⟩ := hstep i hi
      rw [show R.step = ArmStepX R.X R.H R.fa from rfl, cls_of_decode hdec] at hc
      exact hns x t (List.mem_of_getElem? hli) _ a ha rel rs rn hc
  -- the configuration and `Q` after the move
  refine ⟨j, ls1', s', _, hc1, hcl, hlat, ?_, hpriv⟩
  · refine ⟨j + ls1'.length, vb, items, pre ++ [.move src dst], c2, ls2, ps1, ps2, T, hvb,
      hit, by rw [hsplit]; simp, hchk', hc2, h2, htr, ?_, ?_, ?_⟩
    · rw [← List.drop_drop, hdrop', List.drop_left]
    · rw [execLines_pc (hrun ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩), hpc]
      simp only [RL.pcOf, RL.L]
      rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop') (fun ln h => by
        obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩), BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]
    · have hsp' : spOf s' = R.spB := hmo.sp
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

/-- **The per-item obligation at a move** (module doc). -/
theorem move_op {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b : Nat}
    {src dst : Loc} {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (MvC b src dst its m w)) (hA : AInv R (MvC b src dst its m w))
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ItemSimOut Policy.arm R.step (OkPriv R) (SrcStep R) (RelQ R) (PrivA R) (fun c => c.measure)
        (s, mon) (MvC b src dst its m w) ls ∨ PrivW (PrivA R) (evTr ls) := by
  obtain ⟨j, ls1', s', code, -, -, hlat, hq', hpriv⟩ := move_lines hR hq
  have hiter := hlat.iter hR
  have hA' : AInv R (.run ⟨b, its, upd m dst (m src), w⟩) := aInv_step hR hq hA .move
  by_cases hN : ls1'.length ≤ ls.length
  · obtain ⟨⟨s1, mon1⟩, r1, -⟩ := PRun.split (ls.take ls1'.length) (ls.drop ls1'.length)
      (by rw [List.take_append_drop]; exact hr)
    have hlen1 : (ls.take ls1'.length).length = ls1'.length := by simp; omega
    obtain ⟨hs1, hev1⟩ := prun_priv r1 fun i hi => hpriv i (by omega)
    rw [hlen1] at hs1 hev1
    simp only at hs1
    rw [hiter] at hs1
    subst hs1
    refine .inl ⟨ls1'.length, [], _, (s1, mon1), fun _ => (0, 0), hN,
      .inr (by simp [measure_run]), .move, r1, ⟨hq', hA'⟩, ?_⟩
    rw [hev1]
    exact img_privW (privW_segEvs fun i hi => (hpriv i hi).1) _
  · obtain ⟨-, hev1⟩ := prun_priv hr fun i hi => hpriv i (by omega)
    rw [hev1]
    exact .inr (privW_segEvs fun i hi => (hpriv i (by omega)).1)

/-! ## The run level -/

/-- **`ItemSim` from the instruction items, with moves**: under `OkPriv`, the per-item obligation
holds when it holds at every instruction item with a source step (for runs under any condition,
in particular `fun _ _ => True` as `ArmAllocMem`'s items give it). -/
theorem itemSim_of_op_ok {R : RL} (hR : R.Wf)
    (hop : ∀ s mon b k allocs its m w evs0 c0, Q R s (OpC b k allocs its m w) →
      AInv R (OpC b k allocs its m w) → SrcStep R (OpC b k allocs its m w) evs0 c0 →
      ∀ ls t', PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t' →
        OpOut R (s, mon) (OpC b k allocs its m w) ls) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStep R) (RelQ R) (Done R)
      (fun c => c.measure) (PrivA R) := by
  rintro ⟨s, mon⟩ c ⟨hq, hA⟩ ls t' hr
  match c with
  | .ret vals m w => exact .inl (.inl ⟨vals, m, w, rfl⟩)
  | .halt w => exact .inl (.inr (.inl ⟨w, rfl⟩))
  | .run ⟨b, its, m, w⟩ =>
  by_cases hS : ∃ evs c', SrcStep R (.run ⟨b, its, m, w⟩) evs c'
  case neg => exact .inl (.inr (.inr fun evs c' h => hS ⟨evs, c', h⟩))
  obtain ⟨evs0, c0, hs0⟩ := hS
  cases hs0 with
  | @move _ src dst its' =>
    rcases move_op hR hq hA hr with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    have hr' := PRun.mono (fun _ _ _ => trivial) hr
    rcases hop s mon b k allocs its' m w _ _ hq hA (.op hvb hi hops hevs hfoot hst) ls t' hr' with
      h | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi'⟩ | h | h
    · exact .inl h
    · obtain ⟨t1', r1, -⟩ := PRun.split (ls.take n) (ls.drop n)
        (by rw [List.take_append_drop]; exact hr)
      obtain rfl := PRun.det (PRun.mono (fun _ _ _ => trivial) r1) hr1
      exact .inr (.inl ⟨n, evs, c', t1', φ, hn, hpos, hs, r1, hR1, hi'⟩)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))

/-- **The per-item obligation of the memory scope, with moves.** -/
theorem itemSim_mv {R : RL} (hR : R.Wf) (hsc : MemScope R) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStep R) (RelQ R) (Done R)
      (fun c => c.measure) (PrivA R) := by
  refine itemSim_of_op_ok hR fun s mon b k allocs its m w evs0 c0 hq hA hs ls t' hr => ?_
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

/-- **Layer 4b for the memory scope, with moves** (module doc): every precise Arm run under
`OkPriv` from a `Q`-related state realizes a run of the allocated code (`MTRun`) with `Refines`
(equal kinds, the addresses outside the world private, the monitor pairs atomic), up to the
allocated code's return, trap or undefined behaviour (`Done`), for functions whose instructions
are event-free, `fence`, `ldar` or `stlr` (`MemScope`), whatever their moves. -/
theorem arm_alloc_refines_mv {R : RL} (hR : R.Wf) (hsc : MemScope R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_mv hR hsc) hr ⟨hq, hA⟩
  exact ⟨n, trS, cE, ψ, hn, mtrun_of_srun hs, href, hend⟩

end Concurrency.ArmAllocThread

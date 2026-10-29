import FV.E2E.RegLevelReadsIn

/-!
# Aligning the segments of two realisations (SEM1 #537, item (3), route (a))

The determinism clause of `ThmPDERX` compares, index by index, the machine runs of one activation
from two entries (`StEqOutX`, `docs/plans/uninit.md` §5.9). The guarded reads of a run
(`RL.WReadsIn`) are stated per realised VCode step; using them on both runs at the same machine
index needs the two realisations to cut their runs into the same segments.

**Finding (decided here).** `Q`'s line index and emitter state are existential and not unique
(an emitter state `ps1` with another trap numbering gives a second witness for the same
configuration), and since #553 a block is entered at any line representing it (`RepL`): a
trusted forwarding block at its own label or at its target's, so one branch may enter one block
at two pcs, depending on its outcome (a conditional branch whose two successors are one block,
or a jump table naming a block twice). "The segment ends at the first arrival at the next
item's line" is therefore not the same index in two runs whose pcs agree. The fix keeps `Q` and
exposes its witness:

* `QW R s j ps1 T c`: `Q` at the witness `(j, ps1, T)`: `Qs` at `(j, ps1)` when `T = []`, or
  (`T ≠ []`) a forwarding block entered at a line representing its target, without a machine
  step (`QE` through `fwd`); `QW.q`;
* a realisation step from `QW` at a witness ends at the witness computed from it and the arrival
  pc (`RL.nextW`: the next item's lines after the item's own, or the chosen entry witness of the
  target block at the arrival pc, `RL.entryW`), at the first arrival at the step's targets
  (`RL.TgtS`: the next item's line, or every pc at which the target block is entered), so two
  runs started at the same witness with agreeing pcs end at the same index and witness;
* `FirstArrS f s n S`: the pc after `n` steps is in `S`, and at no index strictly between;
  **`firstArrS_eq`**: two runs whose pcs agree, both arriving first in `S`, with the same
  zero-length case, take the same number of steps.
-/

namespace Backend.Proof

open Backend E2E

/-- **The code part of `Qs` at the witness `(j, ps1)`**: the items `its` of block `b` and their
lines from line `j`, with the emitter state `ps1` before them (no machine state). -/
def QWst (R : RL) (j : Nat) (ps1 : PState) (b : Nat) (its : List RItem) : Prop :=
  ∃ vb items pre code X psm ps2, ∃ x : Seg × List Line × Nat,
    R.vc.blocks[b]? = some vb ∧ R.rf.blocks[b]? = some items ∧ items.toList = pre ++ its ∧
    ItemsChecked R vb its ∧
    itemsCode R.fr vb its = .ok code ∧
    codeLinesE R.ctx R.af code.dropLast ps1 = .ok (X, psm) ∧
    codeLinesE R.ctx R.af code.getLast?.toList psm = .ok (x.1.term, ps2) ∧
    ps2.traps.toList <+: R.psF.traps.toList ∧
    R.L.drop j = relaxLines R.far (X ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) ∧
    segX R.fa.k R.af b = some x ∧ SegChecked R.fa.k R.af b

/-- **`Qs` at the witness `(j, ps1)`**: its line index and the emitter state before the items. -/
def QWs (R : RL) (s : Arm.ArmState) (j : Nat) (ps1 : PState) (b : Nat) (its : List RItem)
    (m : Loc → CV) (w : Arm.ArmState) : Prop :=
  ∃ vb items pre code X psm ps2, ∃ x : Seg × List Line × Nat,
    R.vc.blocks[b]? = some vb ∧ R.rf.blocks[b]? = some items ∧ items.toList = pre ++ its ∧
    ItemsChecked R vb its ∧
    itemsCode R.fr vb its = .ok code ∧
    codeLinesE R.ctx R.af code.dropLast ps1 = .ok (X, psm) ∧
    codeLinesE R.ctx R.af code.getLast?.toList psm = .ok (x.1.term, ps2) ∧
    ps2.traps.toList <+: R.psF.traps.toList ∧
    R.L.drop j = relaxLines R.far (X ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) ∧
    Arm.r .PC s = R.pcOf j ∧ StRel R s m w ∧
    segX R.fa.k R.af b = some x ∧ SegChecked R.fa.k R.af b

theorem QWs.qs {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {b : Nat} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : QWs R s j ps1 b its m w) : Qs R s b its m w := by
  obtain ⟨vb, items, pre, code, X, psm, ps2, x, h⟩ := h
  exact ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, h⟩

theorem QWs.pc {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {b : Nat} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : QWs R s j ps1 b its m w) : Arm.r .PC s = R.pcOf j := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpc, -⟩ := h
  exact hpc

theorem QWs.st {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {b : Nat} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : QWs R s j ps1 b its m w) :
    QWst R j ps1 b its ∧ Arm.r .PC s = R.pcOf j ∧ StRel R s m w := by
  obtain ⟨vb, items, pre, code, X, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13⟩ := h
  exact ⟨⟨vb, items, pre, code, X, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13⟩, h10,
    h11⟩

theorem QWst.qWs {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {b : Nat}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} (h : QWst R j ps1 b its)
    (hpc : Arm.r .PC s = R.pcOf j) (hst : StRel R s m w) : QWs R s j ps1 b its m w := by
  obtain ⟨vb, items, pre, code, X, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13⟩ := h
  exact ⟨vb, items, pre, code, X, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, hpc, hst, h12,
    h13⟩

/-- **A block entered at the witness `(j, ps1)`** (the code part of `QE`): at its items' lines
(`QWst`), or it forwards to a block entered so, whose label a line at the witness's pc
represents. -/
inductive QEWst (R : RL) (j : Nat) (ps1 : PState) : Nat → Prop
  | std {b : Nat} {items : Array RItem} : R.rf.blocks[b]? = some items →
      QWst R j ps1 b items.toList → QEWst R j ps1 b
  | fwd {b bx : Nat} {vb vbx : VBlock} {x : Label} {items : Array RItem} {allocs : Array Loc}
      {regs : Array Reg} {i : MInst} {jl : Nat} : R.vc.blocks[b]? = some vb →
      R.af.fwd? vb.label = some x → R.rf.blocks[b]? = some items →
      items.toList = [.op 0 allocs] → allocs = regs.map Loc.reg → vb.insts = #[i] →
      i.assign regs = .ok (.jump x) → succOf R.vc b 0 = some bx →
      R.vc.blocks[bx]? = some vbx → vbx.label = x →
      RepL R.af (planOwn R.fa.k R.af) R.L x jl → R.pcOf jl = R.pcOf j →
      QEWst R j ps1 bx → QEWst R j ps1 b

/-- **A forwarding block entered at the witness `(j, ps1)`** without a machine step: block `b`
(items `its`, one `op` of its only instruction, a `jump x`) forwards to `bx`, whose label a line
at the witness's pc represents, entered at the witness (`QEWst`). -/
def QEFst (R : RL) (j : Nat) (ps1 : PState) (b : Nat) (its : List RItem) : Prop :=
  ∃ (vb vbx : VBlock) (x : Label) (items : Array RItem) (allocs : Array Loc) (regs : Array Reg)
    (i : MInst) (bx jl : Nat), R.vc.blocks[b]? = some vb ∧
    R.af.fwd? vb.label = some x ∧ R.rf.blocks[b]? = some items ∧ its = items.toList ∧
    items.toList = [.op 0 allocs] ∧ allocs = regs.map Loc.reg ∧ vb.insts = #[i] ∧
    i.assign regs = .ok (.jump x) ∧ succOf R.vc b 0 = some bx ∧
    R.vc.blocks[bx]? = some vbx ∧ vbx.label = x ∧
    RepL R.af (planOwn R.fa.k R.af) R.L x jl ∧ R.pcOf jl = R.pcOf j ∧ QEWst R j ps1 bx

/-- **`Q` at the witness `(j, ps1, T)`**: `Qs` at `(j, ps1)` (`T = []`), or a forwarding block
entered without a machine step at the witness of the block it is entered as (`T ≠ []`). -/
def QW (R : RL) (s : Arm.ArmState) (j : Nat) (ps1 : PState) (T : List Line) :
    MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ =>
    (T = [] ∧ QWs R s j ps1 b its m w) ∨
      (T ≠ [] ∧ QEFst R j ps1 b its ∧ Arm.r .PC s = R.pcOf j ∧ StRel R s m w)
  | _ => True

theorem QEWst.qe {R : RL} {j : Nat} {ps1 : PState} {s : Arm.ArmState} {m : Loc → CV}
    {w : Arm.ArmState} (hpc : Arm.r .PC s = R.pcOf j) (hst : StRel R s m w) :
    ∀ {b : Nat}, QEWst R j ps1 b → QE R s m w b
  | _, .std hit h => .std hit (QWst.qWs h hpc hst).qs
  | _, .fwd hvb hx hit hil hal hins hasg hsucc hvbx hlx _ _ h =>
    .fwd hvb hx hit hil hal hins hasg hsucc hvbx hlx (QEWst.qe hpc hst h)

/-- `QW` is `Q` at a witness. -/
theorem QW.q {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c : MConf CV Arm.ArmState} (h : QW R s j ps1 T c) : Q R s c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    rcases h with ⟨-, h⟩ | ⟨-, ⟨vb, vbx, x, items, allocs, regs, i, bx, jl, hvb, hx, hit, hits, hil,
      hal, hins, hasg, hsucc, hvbx, hlx, -, -, h⟩, hpc, hst⟩
    · exact .inl h.qs
    · exact .inr ⟨items, hit, hits, .fwd hvb hx hit hil hal hins hasg hsucc hvbx hlx
        (QEWst.qe hpc hst h)⟩
  | ret => trivial
  | halt => trivial

/-- The witness determines the pc of a `QW` state. -/
theorem QW.pc {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, its, m, w⟩)) : Arm.r .PC s = R.pcOf j := by
  rcases h with ⟨-, h⟩ | ⟨-, -, hpc, -⟩
  · exact h.pc
  · exact hpc

/-- A `QW` state is related to the configuration's store and world. -/
theorem QW.stRel {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, its, m, w⟩)) : StRel R s m w := by
  rcases h with ⟨-, h⟩ | ⟨-, -, -, hst⟩
  · exact h.st.2.2
  · exact hst

/-! ## First arrival -/

/-- **`p` is reached after `n` steps and at no index strictly between.** -/
def FirstArr (f : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) (n : Nat) (p : BitVec 64) :
    Prop :=
  Arm.r .PC (iterN f n s) = p ∧ ∀ i, 0 < i → i < n → Arm.r .PC (iterN f i s) ≠ p

/-- **A pc in `S` is reached after `n` steps and at no index strictly between.** -/
def FirstArrS (f : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) (n : Nat)
    (S : BitVec 64 → Prop) : Prop :=
  S (Arm.r .PC (iterN f n s)) ∧ ∀ i, 0 < i → i < n → ¬ S (Arm.r .PC (iterN f i s))

theorem firstArrS_singleton {f : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {n : Nat}
    {p : BitVec 64} : FirstArrS f s n (· = p) ↔ FirstArr f s n p := Iff.rfl

/-- **Two first arrivals in one set along pc-agreeing runs take the same number of steps** (when
they agree on the zero-length case). -/
theorem firstArrS_eq {f f' : Arm.ArmState → Arm.ArmState} {s s' : Arm.ArmState} {n n' : Nat}
    {S : BitVec 64 → Prop} (h : FirstArrS f s n S) (h' : FirstArrS f' s' n' S)
    (hpc : ∀ i ≤ max n n', Arm.r .PC (iterN f i s) = Arm.r .PC (iterN f' i s'))
    (hz : n = 0 ↔ n' = 0) : n = n' := by
  rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (hz.mp h0) (by omega)
    · exact absurd (by rw [← hpc n (by omega)]; exact h.1) (h'.2 n h0 hlt)
  · exact heq
  · rcases Nat.eq_zero_or_pos n' with h0 | h0
    · exact absurd (hz.mpr h0) (by omega)
    · exact absurd (by rw [hpc n' (by omega)]; exact h'.1) (h.2 n' h0 hgt)

/-- **Two first arrivals at one pc along pc-agreeing runs take the same number of steps** (when
they agree on the zero-length case). -/
theorem firstArr_eq {f f' : Arm.ArmState → Arm.ArmState} {s s' : Arm.ArmState} {n n' : Nat}
    {p : BitVec 64} (h : FirstArr f s n p) (h' : FirstArr f' s' n' p)
    (hpc : ∀ i ≤ max n n', Arm.r .PC (iterN f i s) = Arm.r .PC (iterN f' i s'))
    (hz : n = 0 ↔ n' = 0) : n = n' :=
  firstArrS_eq (S := (· = p)) h h' hpc hz

/-! ## The witness after a step -/

/-- **An entry witness of block `t` at the pc `p`**: a line representing `t` is at `p`, which
is the witness's pc, and `t`'s entry configuration is at the witness (`QWst` or `QEFst`). Only
the code data of `R` occur (no entry state, hooks, budget or kept set), so two activations of
one compiled function choose the same witness (`RL.entryW_congr`). -/
def RL.EntryWit (R : RL) (t : Nat) (p : BitVec 64) (W : Nat × PState × List Line) : Prop :=
  R.pcOf W.1 = p ∧
    (∃ vb jl, R.vc.blocks[t]? = some vb ∧ RepL R.af (planOwn R.fa.k R.af) R.L vb.label jl ∧
      R.pcOf jl = p) ∧
    ∀ (items : Array RItem), R.rf.blocks[t]? = some items →
      (W.2.2 = [] ∧ QWst R W.1 W.2.1 t items.toList) ∨
        (W.2.2 ≠ [] ∧ QEFst R W.1 W.2.1 t items.toList)

/-- **At an entry witness**: a state at its pc, related to a store and world, is at `QW` of the
block's entry configuration. -/
theorem RL.EntryWit.qW {R : RL} {t : Nat} {p : BitVec 64} {W : Nat × PState × List Line}
    (hW : R.EntryWit t p W) {items : Array RItem} (hit : R.rf.blocks[t]? = some items)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} (hpc : Arm.r .PC s = p)
    (hst : StRel R s m w) : QW R s W.1 W.2.1 W.2.2 (.run ⟨t, items.toList, m, w⟩) := by
  rcases hW.2.2 items hit with ⟨hT, h⟩ | ⟨hT, h⟩
  · exact .inl ⟨hT, h.qWs (hpc.trans hW.1.symm) hst⟩
  · exact .inr ⟨hT, h, hpc.trans hW.1.symm, hst⟩

open Classical in
/-- **The chosen entry witness of block `t` at the pc `p`.** -/
noncomputable def RL.entryW (R : RL) (t : Nat) (p : BitVec 64) : Nat × PState × List Line :=
  if h : ∃ W, R.EntryWit t p W then Classical.choose h else (0, {}, [])

theorem RL.entryW_spec {R : RL} {t : Nat} {p : BitVec 64} (h : ∃ W, R.EntryWit t p W) :
    R.EntryWit t p (R.entryW t p) := by
  unfold RL.entryW
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Two activations of one compiled function**: the same code data (VCode, allocation,
allocated and laid-out function, load address, emitter state); entry state, hooks, budget, kept
set and GOT pins may differ. -/
structure RL.SameCode (R R' : RL) : Prop where
  vc : R'.vc = R.vc
  rf : R'.rf = R.rf
  af : R'.af = R.af
  fa : R'.fa = R.fa
  base : R'.base = R.base
  psF : R'.psF = R.psF

theorem RL.entryWit_congr {R R' : RL} (h : R.SameCode R') (t : Nat) (p : BitVec 64) :
    R'.EntryWit t p = R.EntryWit t p := by
  obtain ⟨vc, rf, af, fa, fb, lm, base, s0, X, H, psF, K, G, gv⟩ := R
  obtain ⟨vc', rf', af', fa', fb', lm', base', s0', X', H', psF', K', G', gv'⟩ := R'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- **Two activations of one compiled function choose the same entry witnesses.** -/
theorem RL.entryW_congr {R R' : RL} (h : R.SameCode R') (t : Nat) (p : BitVec 64) :
    R'.entryW t p = R.entryW t p := by
  unfold RL.entryW
  rw [RL.entryWit_congr h]

/-- **An initial witness**: the line after the prologue, where block 0's lines start, with the
emitter state of the witness (code data only, as `RL.EntryWit`). -/
def RL.InitWit (R : RL) (W : Nat × PState × List Line) : Prop :=
  W.1 = 1 + (prologueLines R.af.saves R.af.frameSize).length ∧ W.2.2 = [] ∧
    ∀ (items : Array RItem), R.rf.blocks[0]? = some items → QWst R W.1 W.2.1 0 items.toList

open Classical in
/-- **The chosen initial witness.** -/
noncomputable def RL.initW (R : RL) : Nat × PState × List Line :=
  if h : ∃ W, R.InitWit W then Classical.choose h else (0, {}, [])

theorem RL.initW_spec {R : RL} (h : ∃ W, R.InitWit W) : R.InitWit R.initW := by
  unfold RL.initW
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Two activations of one compiled function choose the same initial witness.** -/
theorem RL.initW_congr {R R' : RL} (h : R.SameCode R') : R'.initW = R.initW := by
  obtain ⟨vc, rf, af, fa, fb, lm, base, s0, X, H, psF, K, G, gv⟩ := R
  obtain ⟨vc', rf', af', fa', fb', lm', base', s0', X', H', psF', K', G', gv'⟩ := R'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- **The witness after a straight step** over item `it` of block `b`: the lines after the
item's own. -/
def RL.straightW (R : RL) (b : Nat) (it : RItem) (j : Nat) (ps1 : PState) (T : List Line) :
    Nat × PState × List Line :=
  match R.vc.blocks[b]? with
  | some vb =>
    match itemCode R.fr vb it with
    | .ok c1 =>
      match codeLinesE R.ctx R.af c1 ps1 with
      | .ok (ls1, psm) => (j + (relaxLines R.far ls1).length, psm, T)
      | .error _ => (j, ps1, T)
    | .error _ => (j, ps1, T)
  | none => (j, ps1, T)

theorem RL.straightW_eq {R : RL} {b : Nat} {it : RItem} {j : Nat} {ps1 psm : PState}
    {T : List Line} {vb : VBlock} {c1 : List AInst} {ls1 : List Line}
    (hvb : R.vc.blocks[b]? = some vb) (hc1 : itemCode R.fr vb it = .ok c1)
    (h1 : codeLinesE R.ctx R.af c1 ps1 = .ok (ls1, psm)) :
    R.straightW b it j ps1 T = (j + (relaxLines R.far ls1).length, psm, T) := by
  simp only [RL.straightW, hvb, hc1, h1]

/-- A step from `c` to `c''` **goes on in the same block** (`c''` holds the items after `c`'s
first); otherwise it enters a block (or leaves the activation). -/
def RL.Straight (c c'' : MConf CV Arm.ArmState) : Prop :=
  match c, c'' with
  | .run ⟨b, _ :: its, _, _⟩, .run ⟨b'', its'', _, _⟩ => b'' = b ∧ its'' = its
  | _, _ => False

open Classical in
/-- **The witness after a step from `c` (at witness `(j, ps1, T)`) to `c''`, arriving at the
pc `p`**: the straight step's, or the chosen entry witness at `p` of the block entered. -/
noncomputable def RL.nextW (R : RL) (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) (p : BitVec 64) : Nat × PState × List Line :=
  match c, c'' with
  | .run ⟨b, it :: its, _, _⟩, .run ⟨b'', its'', _, _⟩ =>
    if b'' = b ∧ its'' = its then R.straightW b it j ps1 T else R.entryW b'' p
  | _, _ => (j, ps1, T)

theorem RL.nextW_straight {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState} {p : BitVec 64} :
    R.nextW j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b, its, m', w'⟩) p =
      R.straightW b it j ps1 T := by
  simp [RL.nextW]

theorem RL.nextW_entry {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b b'' : Nat}
    {it : RItem} {its its'' : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState} {p : BitVec 64}
    (h : ¬ (b'' = b ∧ its'' = its)) :
    R.nextW j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) p = R.entryW b'' p := by
  simp only [RL.nextW]
  rw [if_neg h]

/-- **`QW` at the witness after a step from `c` (at witness `(j, ps1, T)`) to `c''`**, in the
arrival state `u` (`RL.nextW` at `u`'s pc). -/
def RL.QWn (R : RL) (j : Nat) (ps1 : PState) (T : List Line) (c c'' : MConf CV Arm.ArmState)
    (u : Arm.ArmState) : Prop :=
  QW R u (R.nextW j ps1 T c c'' (Arm.r .PC u)).1 (R.nextW j ps1 T c c'' (Arm.r .PC u)).2.1
    (R.nextW j ps1 T c c'' (Arm.r .PC u)).2.2 c''

open Classical in
/-- **The targets of a step** from `c` (at witness `(j, ps1, T)`) to `c''`: the line of the next
item for a straight step, else every pc at which the block entered has an entry witness
(`RL.EntryWit`: a line representing it). -/
noncomputable def RL.TgtS (R : RL) (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) : BitVec 64 → Prop :=
  match c, c'' with
  | .run ⟨b, it :: its, _, _⟩, .run ⟨b'', its'', _, _⟩ =>
    if b'' = b ∧ its'' = its then (· = R.pcOf (R.straightW b it j ps1 T).1)
    else fun p => ∃ W, R.EntryWit b'' p W
  | _, _ => (· = R.pcOf j)

theorem RL.tgtS_straight {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState} :
    R.TgtS j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b, its, m', w'⟩) =
      (· = R.pcOf (R.straightW b it j ps1 T).1) := by
  simp [RL.TgtS]

theorem RL.tgtS_entry {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b b'' : Nat}
    {it : RItem} {its its'' : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState}
    (h : ¬ (b'' = b ∧ its'' = its)) :
    R.TgtS j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) =
      fun p => ∃ W, R.EntryWit b'' p W := by
  simp only [RL.TgtS]
  rw [if_neg h]

open Classical in
/-- **The zero-length case** of a step: a straight step whose item has no lines, or a block
entry from a forwarding block entered without a step (`T ≠ []`) or from a line that is no
instruction (a `goto` whose branch the emission removed). -/
noncomputable def RL.EmptyW (R : RL) (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) : Prop :=
  if RL.Straight c c'' then (R.nextW j ps1 T c c'' 0).1 = j
  else T ≠ [] ∨ ∀ x t, R.L[j]? ≠ some (.ins x t)

/-- **The length of a segment**: the first arrival at the step's targets, the zero-length case
decided by `EmptyW`. -/
def RL.SegLen (R : RL) (j : Nat) (ps1 : PState) (T : List Line) (c c'' : MConf CV Arm.ArmState)
    (s : Arm.ArmState) (n : Nat) : Prop :=
  FirstArrS R.step s n (R.TgtS j ps1 T c c'') ∧ (n = 0 ↔ R.EmptyW j ps1 T c c'')

/-- **Two runs started at one witness, with agreeing pcs, cut their segments at the same index**
when the targets and the zero-length cases agree. -/
theorem RL.segLen_eq {R R' : RL} {j : Nat}
    {ps1 : PState} {T : List Line} {c c'' c₂ c₂'' : MConf CV Arm.ArmState} {s s' : Arm.ArmState}
    {n n' : Nat} (h : R.SegLen j ps1 T c c'' s n) (h' : R'.SegLen j ps1 T c₂ c₂'' s' n')
    (hS : R'.TgtS j ps1 T c₂ c₂'' = R.TgtS j ps1 T c c'')
    (hE : R'.EmptyW j ps1 T c₂ c₂'' ↔ R.EmptyW j ps1 T c c'')
    (hpc : ∀ i ≤ max n n', Arm.r .PC (iterN R.step i s) = Arm.r .PC (iterN R'.step i s')) :
    n = n' := by
  have h1 := h'.1
  rw [hS] at h1
  exact firstArrS_eq h.1 h1 hpc (h.2.trans (hE.symm.trans h'.2.symm))

/-- **An instruction line after an instruction line has a pc distinct from every later
line's.** -/
theorem RL.pcOf_ne {R : RL} (hR : R.Wf) {j0 j1 j2 : Nat} {x0 x1 : Insn}
    {t0 t1 : Option Clif.TrapCode} (hj0 : R.L[j0]? = some (.ins x0 t0)) (h01 : j0 < j1)
    (hj1 : R.L[j1]? = some (.ins x1 t1)) (h12 : j1 < j2) : R.pcOf j1 ≠ R.pcOf j2 := by
  intro he
  simp only [RL.pcOf, RL.L] at he hj0 hj1
  have hsz : (R.fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hR.layout]; exact hR.fit
  have hs0 := lineOffset_succ R.fa.lines.toList j0 _ hj0
  have hs1 := lineOffset_succ R.fa.lines.toList j1 _ hj1
  simp only [Line.size] at hs0 hs1
  have hm1 := lineOffset_mono R.fa.lines.toList (show j0 + 1 ≤ j1 by omega)
  have hm2 := lineOffset_mono R.fa.lines.toList (show j1 + 1 ≤ j2 by omega)
  have hl2 := lineOffset_le_size R.fa.lines.toList j2
  have he2 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he)
  simp only [BitVec.toNat_ofNat] at he2
  rw [Nat.mod_eq_of_lt (by omega)] at he2
  by_cases hlt : lineOffset R.fa.lines.toList j2 < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hlt] at he2
    omega
  · rw [show lineOffset R.fa.lines.toList j2 = 2 ^ 64 by omega, Nat.mod_self] at he2
    omega

/-- **An instruction line before an instruction line has a pc distinct from every earlier
line's.** -/
theorem RL.pcOf_ne_le {R : RL} (hR : R.Wf) {j0 j1 j2 : Nat} {x0 x1 : Insn}
    {t0 t1 : Option Clif.TrapCode} (hj0 : R.L[j0]? = some (.ins x0 t0)) (h01 : j0 < j1)
    (hj1 : R.L[j1]? = some (.ins x1 t1)) (h20 : j2 ≤ j0) : R.pcOf j1 ≠ R.pcOf j2 := by
  intro he
  simp only [RL.pcOf, RL.L] at he hj0 hj1
  have hsz : (R.fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hR.layout]; exact hR.fit
  have hs0 := lineOffset_succ R.fa.lines.toList j0 _ hj0
  have hs1 := lineOffset_succ R.fa.lines.toList j1 _ hj1
  simp only [Line.size] at hs0 hs1
  have hm1 := lineOffset_mono R.fa.lines.toList (show j0 + 1 ≤ j1 by omega)
  have hm2 := lineOffset_mono R.fa.lines.toList h20
  have hl1 := lineOffset_le_size R.fa.lines.toList (j1 + 1)
  have he2 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he)
  simp only [BitVec.toNat_ofNat] at he2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he2
  omega

/-- **The states strictly inside a segment are at instruction lines after its first line `j0`
and before `lim`.** -/
def RL.Inside (R : RL) (s : Arm.ArmState) (n j0 lim : Nat) : Prop :=
  ∀ i, 0 < i → i < n → ∃ jj x t, j0 < jj ∧ jj < lim ∧ R.L[jj]? = some (.ins x t) ∧
    Arm.r .PC (iterN R.step i s) = R.pcOf jj

theorem RL.Inside.zero {R : RL} {s : Arm.ArmState} {j0 lim : Nat} : R.Inside s 0 j0 lim :=
  fun _ h0 h => absurd h (by omega)

theorem RL.Inside.one {R : RL} {s : Arm.ArmState} {j0 lim : Nat} : R.Inside s 1 j0 lim :=
  fun _ h0 h => absurd h (by omega)

theorem RL.Inside.mono {R : RL} {s : Arm.ArmState} {n j0 lim lim' : Nat} (h : R.Inside s n j0 lim)
    (hl : lim ≤ lim') : R.Inside s n j0 lim' := fun i h0 hi => by
  obtain ⟨jj, x, t, h1, h2, h3, h4⟩ := h i h0 hi
  exact ⟨jj, x, t, h1, by omega, h3, h4⟩

/-- **Two inside runs in a row**: the second starts at an instruction line `j1` of the first's
range. -/
theorem RL.Inside.append {R : RL} {s : Arm.ArmState} {n n' j0 j1 lim : Nat}
    (h : R.Inside s n j0 lim) (h' : R.Inside (iterN R.step n s) n' j1 lim) (h01 : j0 < j1)
    (h1l : j1 < lim) {x1 : Insn} {t1 : Option Clif.TrapCode} (hj1 : R.L[j1]? = some (.ins x1 t1))
    (hpc : 0 < n → Arm.r .PC (iterN R.step n s) = R.pcOf j1) :
    R.Inside s (n + n') j0 lim := by
  intro i h0 hi
  rcases Nat.lt_or_ge i n with hlt | hge
  · exact h i h0 hlt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨j1, x1, t1, h01, h1l, hj1, by simpa using hpc h0⟩
    · obtain ⟨jj, x, t, e1, e2, e3, e4⟩ := h' k hk (by omega)
      exact ⟨jj, x, t, by omega, e2, e3, by rw [iterN_add]; exact e4⟩

/-- **A segment inside its lines arrives first at a line at or after `lim`.** -/
theorem RL.firstArr_of_inside {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n j0 lim j1 : Nat}
    {x0 : Insn} {t0 : Option Clif.TrapCode} (hj0 : R.L[j0]? = some (.ins x0 t0))
    (h : R.Inside s n j0 lim) (hl : lim ≤ j1)
    (hpc : Arm.r .PC (iterN R.step n s) = R.pcOf j1) : FirstArr R.step s n (R.pcOf j1) :=
  ⟨hpc, fun i h0 hi => by
    obtain ⟨jj, x, t, e1, e2, e3, e4⟩ := h i h0 hi
    rw [e4]
    exact RL.pcOf_ne hR hj0 e1 e3 (by omega)⟩

/-- **A segment inside its lines arrives first at a line `jl` outside `(j0, lim)`.** -/
theorem RL.firstArr_of_inside_out {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n j0 lim jl : Nat}
    {x0 : Insn} {t0 : Option Clif.TrapCode} (hj0 : R.L[j0]? = some (.ins x0 t0))
    (h : R.Inside s n j0 lim) (hout : jl ≤ j0 ∨ lim ≤ jl) {p : BitVec 64}
    (hp : p = R.pcOf jl) (hpc : Arm.r .PC (iterN R.step n s) = p) : FirstArr R.step s n p :=
  ⟨hpc, fun i h0 hi => by
    obtain ⟨jj, x, t, e1, e2, e3, e4⟩ := h i h0 hi
    rw [e4, hp]
    rcases hout with ho | ho
    · exact RL.pcOf_ne_le hR hj0 e1 e3 ho
    · exact RL.pcOf_ne hR hj0 e1 e3 (by omega)⟩

/-- **A segment inside its lines arrives first in `S`** when no pc of `S` is an inside
instruction line's. -/
theorem RL.firstArrS_of_inside {R : RL} {s : Arm.ArmState} {n j0 lim : Nat}
    {S : BitVec 64 → Prop} (h : R.Inside s n j0 lim)
    (hS : ∀ p, S p → ∀ jj x t, j0 < jj → jj < lim → R.L[jj]? = some (.ins x t) → p ≠ R.pcOf jj)
    (hpc : S (Arm.r .PC (iterN R.step n s))) : FirstArrS R.step s n S :=
  ⟨hpc, fun i h0 hi hSi => by
    obtain ⟨jj, x, t, e1, e2, e3, e4⟩ := h i h0 hi
    exact hS _ hSi jj x t e1 e2 e3 e4⟩

/-- **A line representing a block starts a run of label lines up to a block label.** -/
theorem repL_run {af : AFunc} {own : Label → Bool} {LL : List Line} {s : Label} {j : Nat}
    (h : RepL af own LL s j) : ∃ k l, j ≤ k ∧ LL[k]? = some (.label (.block l)) ∧
      ∀ i, j ≤ i → i < k → ∃ l', LL[i]? = some (.label l') := by
  induction h with
  | here _ hL => exact ⟨_, _, Nat.le_refl _, hL, fun i h1 h2 => absurd h2 (by omega)⟩
  | @skip s j l _ hL _ ih =>
    obtain ⟨k, l2, hk, hkl, hrun⟩ := ih
    refine ⟨k, l2, by omega, hkl, fun i h1 h2 => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact ⟨l, hL⟩
    · exact hrun i h1 h2
  | fwd _ _ ih => exact ih

/-- **An instruction line inside a run of lines with no block label has a pc distinct from
every line representing a block.** -/
theorem RL.pcOf_ne_rep {R : RL} (hR : R.Wf) {j0 jj lim jl : Nat} {x0 x1 : Insn}
    {t0 t1 : Option Clif.TrapCode} (hj0 : R.L[j0]? = some (.ins x0 t0)) (h01 : j0 < jj)
    (hjj : R.L[jj]? = some (.ins x1 t1)) (hlim : jj < lim)
    (hnb : ∀ k l, j0 < k → k < lim → R.L[k]? ≠ some (.label (.block l))) {own : Label → Bool}
    {s : Label} (hrep : RepL R.af own R.L s jl) : R.pcOf jj ≠ R.pcOf jl := by
  obtain ⟨k, l, hjk, hk, hrun⟩ := repL_run hrep
  rcases Nat.lt_or_ge jj jl with h | h
  · exact RL.pcOf_ne hR hj0 h01 hjj h
  rcases Nat.lt_or_ge j0 jl with h' | h'
  · exfalso
    rcases Nat.lt_or_ge k lim with hk' | hk'
    · exact hnb k l (by omega) hk' hk
    · obtain ⟨l', hl'⟩ := hrun jj h (by omega)
      rw [hjj] at hl'
      cases hl'
  · exact RL.pcOf_ne_le hR hj0 h01 hjj h'

/-- **No entry pc of a block is an inside instruction line's** (inside a run of lines with no
block label). -/
theorem RL.entryWit_ne {R : RL} (hR : R.Wf) {j0 lim : Nat} {x0 : Insn}
    {t0 : Option Clif.TrapCode} (hj0 : R.L[j0]? = some (.ins x0 t0))
    (hnb : ∀ k l, j0 < k → k < lim → R.L[k]? ≠ some (.label (.block l))) {t : Nat} :
    ∀ p, (∃ W, R.EntryWit t p W) → ∀ jj x' t', j0 < jj → jj < lim →
      R.L[jj]? = some (.ins x' t') → p ≠ R.pcOf jj := by
  rintro p ⟨W, -, ⟨vb, jl, -, hrep, rfl⟩, -⟩ jj x' t' h1 h2 h3
  exact (RL.pcOf_ne_rep hR hj0 h1 h3 h2 hnb hrep).symm

/-- **A realised segment at a witness** (the conclusion of the `realizes_*NA` cases): `QW` at the
next witness after `n` steps, the located reads of the states before, and the segment length. -/
abbrev RL.SegNA (R : RL) (Y : BitVec 64 → Prop) (s : Arm.ArmState) (j : Nat) (ps1 : PState)
    (T : List Line) (c c' : MConf CV Arm.ArmState) (n : Nat) : Prop :=
  R.QWn j ps1 T c c' (iterN R.step n s) ∧
    (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧ R.SegLen j ps1 T c c' s n

theorem RL.segLen_straight_iff {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState} :
    R.EmptyW j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b, its, m', w'⟩) ↔
      (R.straightW b it j ps1 T).1 = j := by
  unfold RL.EmptyW
  rw [if_pos (by simp [RL.Straight]), RL.nextW_straight]

/-- **A straight run of instruction lines is a first arrival at the line after it.** -/
theorem RL.firstArr_lines {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j n : Nat}
    (hins : ∀ k < n, ∃ x t, R.L[j + k]? = some (.ins x t))
    (hpcs : ∀ i ≤ n, Arm.r .PC (iterN R.step i s) = R.pcOf (j + i)) :
    FirstArr R.step s n (R.pcOf (j + n)) := by
  refine ⟨hpcs n (Nat.le_refl _), fun i hi0 hin => ?_⟩
  rw [hpcs i (by omega)]
  obtain ⟨x0, t0, h0⟩ := hins 0 (by omega)
  obtain ⟨x1, t1, h1⟩ := hins i hin
  exact RL.pcOf_ne hR (by simpa using h0) (by omega) h1 (by omega)

theorem RL.emptyW_entry_iff {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b b'' : Nat}
    {it : RItem} {its its'' : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState}
    (h : ¬ (b'' = b ∧ its'' = its)) :
    R.EmptyW j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) ↔
      T ≠ [] ∨ ∀ x t, R.L[j]? ≠ some (.ins x t) := by
  unfold RL.EmptyW
  rw [if_neg (by simpa [RL.Straight] using h)]

/-- **Two activations of one compiled function compute the same next witness.** -/
theorem RL.nextW_congr {R R' : RL} (h : R.SameCode R') (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) (p : BitVec 64) :
    R'.nextW j ps1 T c c'' p = R.nextW j ps1 T c c'' p := by
  obtain ⟨vc, rf, af, fa, fb, lm, base, s0, X, H, psF, K, G, gv⟩ := R
  obtain ⟨vc', rf', af', fa', fb', lm', base', s0', X', H', psF', K', G', gv'⟩ := R'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- **Two activations of one compiled function have the same targets.** -/
theorem RL.tgtS_congr {R R' : RL} (h : R.SameCode R') (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) : R'.TgtS j ps1 T c c'' = R.TgtS j ps1 T c c'' := by
  obtain ⟨vc, rf, af, fa, fb, lm, base, s0, X, H, psF, K, G, gv⟩ := R
  obtain ⟨vc', rf', af', fa', fb', lm', base', s0', X', H', psF', K', G', gv'⟩ := R'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- **Two activations of one compiled function have the same zero-length cases.** -/
theorem RL.emptyW_congr {R R' : RL} (h : R.SameCode R') (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) : R'.EmptyW j ps1 T c c'' ↔ R.EmptyW j ps1 T c c'' := by
  obtain ⟨vc, rf, af, fa, fb, lm, base, s0, X, H, psF, K, G, gv⟩ := R
  obtain ⟨vc', rf', af', fa', fb', lm', base', s0', X', H', psF', K', G', gv'⟩ := R'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  exact Iff.rfl

/-- The next witness sees only the blocks and items of the two configurations. -/
theorem RL.nextW_run {R : RL} (j : Nat) (ps1 : PState) (T : List Line) (b b'' : Nat)
    (its its'' : List RItem) (m m' m₂ m₂' : Loc → CV) (w w' w₂ w₂' : Arm.ArmState)
    (p : BitVec 64) :
    R.nextW j ps1 T (.run ⟨b, its, m₂, w₂⟩) (.run ⟨b'', its'', m₂', w₂'⟩) p =
      R.nextW j ps1 T (.run ⟨b, its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) p := by
  cases its <;> rfl

/-- The targets see only the blocks and items of the two configurations. -/
theorem RL.tgtS_run {R : RL} (j : Nat) (ps1 : PState) (T : List Line) (b b'' : Nat)
    (its its'' : List RItem) (m m' m₂ m₂' : Loc → CV) (w w' w₂ w₂' : Arm.ArmState) :
    R.TgtS j ps1 T (.run ⟨b, its, m₂, w₂⟩) (.run ⟨b'', its'', m₂', w₂'⟩) =
      R.TgtS j ps1 T (.run ⟨b, its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) := by
  cases its <;> rfl

/-- The zero-length case sees only the blocks and items of the two configurations. -/
theorem RL.emptyW_run {R : RL} (j : Nat) (ps1 : PState) (T : List Line) (b b'' : Nat)
    (its its'' : List RItem) (m m' m₂ m₂' : Loc → CV) (w w' w₂ w₂' : Arm.ArmState) :
    R.EmptyW j ps1 T (.run ⟨b, its, m₂, w₂⟩) (.run ⟨b'', its'', m₂', w₂'⟩) ↔
      R.EmptyW j ps1 T (.run ⟨b, its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) := by
  cases its <;> exact Iff.rfl

/-- **Two activations of one compiled function, at configurations of the same blocks and items,
arriving at one pc, reach the same next witness.** -/
theorem RL.nextW_same {R R' : RL} (h : R.SameCode R') (j : Nat) (ps1 : PState) (T : List Line)
    {b b'' : Nat} {its its'' : List RItem} {m m' m₂ m₂' : Loc → CV} {w w' w₂ w₂' : Arm.ArmState}
    (p : BitVec 64) :
    R'.nextW j ps1 T (.run ⟨b, its, m₂, w₂⟩) (.run ⟨b'', its'', m₂', w₂'⟩) p =
      R.nextW j ps1 T (.run ⟨b, its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) p :=
  (RL.nextW_run (R := R') j ps1 T b b'' its its'' m m' m₂ m₂' w w' w₂ w₂' p).trans
    (RL.nextW_congr h j ps1 T _ _ p)

/-- **Two activations of one compiled function, started at one witness at configurations of the
same blocks and items, with agreeing pcs, cut their segments at the same index.** -/
theorem RL.segLen_eq_same {R R' : RL} (h : R.SameCode R') {j : Nat} {ps1 : PState}
    {T : List Line} {b b'' : Nat} {its its'' : List RItem} {m m' m₂ m₂' : Loc → CV}
    {w w' w₂ w₂' : Arm.ArmState} {s s' : Arm.ArmState} {n n' : Nat}
    (hs : R.SegLen j ps1 T (.run ⟨b, its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) s n)
    (hs' : R'.SegLen j ps1 T (.run ⟨b, its, m₂, w₂⟩) (.run ⟨b'', its'', m₂', w₂'⟩) s' n')
    (hpc : ∀ i ≤ max n n', Arm.r .PC (iterN R.step i s) = Arm.r .PC (iterN R'.step i s')) :
    n = n' :=
  RL.segLen_eq hs hs'
    ((RL.tgtS_run (R := R') j ps1 T b b'' its its'' m m' m₂ m₂' w w' w₂ w₂').trans
      (RL.tgtS_congr h j ps1 T _ _))
    ((RL.emptyW_run (R := R') j ps1 T b b'' its its'' m m' m₂ m₂' w w' w₂ w₂').trans
      (RL.emptyW_congr h j ps1 T _ _)) hpc

end Backend.Proof

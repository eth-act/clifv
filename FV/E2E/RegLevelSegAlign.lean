import FV.E2E.RegLevelReadsIn

/-!
# Aligning the segments of two realisations (SEM1 #537, item (3), route (a))

The determinism clause of `ThmPDERX` compares, index by index, the machine runs of one activation
from two entries (`StEqOutX`, `docs/plans/uninit.md` §5.9). The guarded reads of a run
(`RL.WReadsIn`) are stated per realised VCode step; using them on both runs at the same machine
index needs the two realisations to cut their runs into the same segments.

**Finding (decided here).** `Q`'s line index is existential and not unique: its lines are matched
as a prefix of `R.L.drop j` followed by an arbitrary tail `T`, so a suffix of the last block that
repeats earlier in the function, or an emitter state `ps1` with another trap numbering, gives a
second index for the same configuration. "The segment ends at the first arrival at the next
item's line" is therefore not the same index in two runs whose pcs agree: each run may arrive at
another index of the same configuration. The fix keeps `Q` and exposes its witness:

* `QW R s j ps1 T c`: `Q`'s body at the witness `(j, ps1, T)`; `q_iff_qW`;
* a realisation step from `QW` at a witness ends at a witness computed from it (the next
  item's lines after the item's own, or the chosen entry witness of the target block), so two
  runs started at the same witness end at the same line;
* `FirstArr f s n p`: `p` is the pc after `n` steps and at no index strictly between;
  **`firstArr_eq`**: two runs whose pcs agree, both arriving first at `p`, with the same
  zero-length case, take the same number of steps.
-/

namespace Backend.Proof

open Backend E2E

/-- **`Q` at the witness `(j, ps1, T)`**: the line index, the emitter state before the items and
the lines after them. -/
def QW (R : RL) (s : Arm.ArmState) (j : Nat) (ps1 : PState) (T : List Line) :
    MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ =>
    ∃ vb items pre code ls ps2,
      R.vc.blocks[b]? = some vb ∧ R.rf.blocks[b]? = some items ∧ items.toList = pre ++ its ∧
      ItemsChecked R vb its ∧
      itemsCode R.fr vb its = .ok code ∧
      codeLinesE R.ctx R.af code ps1 = .ok (ls, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j = relaxLines R.far (ftList (ls ++ nxtOf R.af b)) ++ T ∧
      Arm.r .PC s = R.pcOf j ∧ StRel R s m w
  | _ => True

/-- `Q` is `QW` at some witness. -/
theorem q_iff_qW {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} :
    Q R s (.run ⟨b, its, m, w⟩) ↔ ∃ j ps1 T, QW R s j ps1 T (.run ⟨b, its, m, w⟩) := by
  constructor
  · rintro ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨j, ps1, T, vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨j, ps1, T, vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem QW.q {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c : MConf CV Arm.ArmState} (h : QW R s j ps1 T c) : Q R s c := by
  cases c with
  | run vs =>
    obtain ⟨b, its, m, w⟩ := vs
    exact q_iff_qW.mpr ⟨j, ps1, T, h⟩
  | ret => trivial
  | halt => trivial

/-- The witness determines the pc of a `QW` state. -/
theorem QW.pc {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, its, m, w⟩)) : Arm.r .PC s = R.pcOf j := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpc, _⟩ := h
  exact hpc

/-! ## First arrival -/

/-- **`p` is reached after `n` steps and at no index strictly between.** -/
def FirstArr (f : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) (n : Nat) (p : BitVec 64) :
    Prop :=
  Arm.r .PC (iterN f n s) = p ∧ ∀ i, 0 < i → i < n → Arm.r .PC (iterN f i s) ≠ p

/-- **Two first arrivals at one pc along pc-agreeing runs take the same number of steps** (when
they agree on the zero-length case). -/
theorem firstArr_eq {f f' : Arm.ArmState → Arm.ArmState} {s s' : Arm.ArmState} {n n' : Nat}
    {p : BitVec 64} (h : FirstArr f s n p) (h' : FirstArr f' s' n' p)
    (hpc : ∀ i ≤ max n n', Arm.r .PC (iterN f i s) = Arm.r .PC (iterN f' i s'))
    (hz : n = 0 ↔ n' = 0) : n = n' := by
  rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (hz.mp h0) (by omega)
    · exact absurd ((hpc n (by omega)).symm.trans h.1) (h'.2 n h0 hlt)
  · exact heq
  · rcases Nat.eq_zero_or_pos n' with h0 | h0
    · exact absurd (hz.mpr h0) (by omega)
    · exact absurd ((hpc n' (by omega)).trans h'.1) (h.2 n' h0 hgt)

/-! ## The witness after a step -/

/-- **An entry witness of block `t`**: its `pc` is that of the block's label line, and there
any state related to a store and world is `QW` at block `t`'s start. -/
def RL.EntryWit (R : RL) (t : Nat) (W : Nat × PState × List Line) : Prop :=
  (∀ vb jl, R.vc.blocks[t]? = some vb → R.L[jl]? = some (.label (.block vb.label)) →
      R.pcOf jl = R.pcOf W.1) ∧
    ∀ (s : Arm.ArmState) (m : Loc → CV) (w : Arm.ArmState) (items : Array RItem),
      R.rf.blocks[t]? = some items → Arm.r .PC s = R.pcOf W.1 → StRel R s m w →
      QW R s W.1 W.2.1 W.2.2 (.run ⟨t, items.toList, m, w⟩)

open Classical in
/-- **The chosen entry witness of block `t`.** -/
noncomputable def RL.entryW (R : RL) (t : Nat) : Nat × PState × List Line :=
  if h : ∃ W, R.EntryWit t W then Classical.choose h else (0, {}, [])

theorem RL.entryW_spec {R : RL} {t : Nat} (h : ∃ W, R.EntryWit t W) :
    R.EntryWit t (R.entryW t) := by
  unfold RL.entryW
  rw [dif_pos h]
  exact Classical.choose_spec h

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
/-- **The witness after a step from `c` (at witness `(j, ps1, T)`) to `c''`**: the straight
step's, or the chosen entry witness of the block entered. -/
noncomputable def RL.nextW (R : RL) (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) : Nat × PState × List Line :=
  match c, c'' with
  | .run ⟨b, it :: its, _, _⟩, .run ⟨b'', its'', _, _⟩ =>
    if b'' = b ∧ its'' = its then R.straightW b it j ps1 T else R.entryW b''
  | _, _ => (j, ps1, T)

theorem RL.nextW_straight {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState} :
    R.nextW j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b, its, m', w'⟩) =
      R.straightW b it j ps1 T := by
  simp [RL.nextW]

theorem RL.nextW_entry {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b b'' : Nat}
    {it : RItem} {its its'' : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState}
    (h : ¬ (b'' = b ∧ its'' = its)) :
    R.nextW j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b'', its'', m', w'⟩) = R.entryW b'' := by
  simp only [RL.nextW]
  rw [if_neg h]

open Classical in
/-- **The zero-length case** of a step: a straight step whose item has no lines, or a block
entry from a line that is no instruction (a `goto` whose branch `fallthrough` removed). -/
noncomputable def RL.EmptyW (R : RL) (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) : Prop :=
  if RL.Straight c c'' then (R.nextW j ps1 T c c'').1 = j
  else ∀ x t, R.L[j]? ≠ some (.ins x t)

/-- **The length of a segment**: the first arrival at the next witness's line, the zero-length
case decided by `EmptyW`. -/
def RL.SegLen (R : RL) (j : Nat) (ps1 : PState) (T : List Line) (c c'' : MConf CV Arm.ArmState)
    (s : Arm.ArmState) (n : Nat) : Prop :=
  FirstArr R.step s n (R.pcOf (R.nextW j ps1 T c c'').1) ∧ (n = 0 ↔ R.EmptyW j ps1 T c c'')

/-- **Two runs started at one witness, with agreeing pcs, cut their segments at the same index**
when the next witnesses and the zero-length cases agree. -/
theorem RL.segLen_eq {R R' : RL} (hL : R'.L = R.L) (hb : R'.base = R.base) {j : Nat}
    {ps1 : PState} {T : List Line} {c c'' c₂ c₂'' : MConf CV Arm.ArmState} {s s' : Arm.ArmState}
    {n n' : Nat} (h : R.SegLen j ps1 T c c'' s n) (h' : R'.SegLen j ps1 T c₂ c₂'' s' n')
    (hW : R'.nextW j ps1 T c₂ c₂'' = R.nextW j ps1 T c c'')
    (hE : R'.EmptyW j ps1 T c₂ c₂'' ↔ R.EmptyW j ps1 T c c'')
    (hpc : ∀ i ≤ max n n', Arm.r .PC (iterN R.step i s) = Arm.r .PC (iterN R'.step i s')) :
    n = n' := by
  have hp : R'.pcOf (R'.nextW j ps1 T c₂ c₂'').1 = R.pcOf (R.nextW j ps1 T c c'').1 := by
    rw [hW]; simp only [RL.pcOf, RL.L] at hL ⊢; rw [hL, hb]
  have h1 := h'.1
  rw [hp] at h1
  exact firstArr_eq h.1 h1 hpc (h.2.trans (hE.symm.trans h'.2.symm))

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

end Backend.Proof

import FV.E2E.RegLevelNoCall

/-!
# Where the reads of an activation's run land (SEM1 #537, step 3p, docs/plans/uninit.md §5.9)

`RL.GoodX.reads` (D2) bounds the reads of the run only away from the kept addresses `G`. The
lock-step of two runs (`lockstep_runX`) needs more: every read is a byte the two runs agree on.
`RL.ReadsIn R u`: every memory read of the unhooked instruction at the pc of `u` is

* a byte of one of the function's data (`.word`) lines (the jump tables), or
* a byte of the activation's own frame `[spB, spB + frameDrop)` other than the frame record's
  saved-LR word (`RL.FrameRd`); the LR word only for the epilogue's `ldp x29, x30, [sp], #16`
  (`Insn.ldpFR`), or
* a byte outside the frame addresses `F` (a covered form's access to the world).

`RL.ReadIn lr a` implies `RL.ReadOk a` (`RL.readIn_ok`), so `ReadsIn` refines D2. Builders as for
D2 (`RL.readsIn_of_line`, `RL.readsIn_noLoad`, `RL.readsIn_hooked`, `RL.readsIn_execLinesG`).
`RL.GoodXNR` is `GoodXN` with `ReadsIn`; the `realizes_*NR` variants (files `*NR.lean`) state it.

**Guarded world reads** (SEM1 item (2)): `RL.ReadInY Y` narrows the third case to bytes outside
`F` *and* outside a guard set `Y` (`¬ R.F a ∧ ¬ Y a`); `RL.ReadIn` is `ReadInY R.F`. The builders
and the `realizes_*NR` theorems of the cases that read no world byte (all but the straight-line
forms and the atomic loops) hold for every `Y`; the straight-line forms and the atomic loops
need the instruction's `csem` at `Y` (`realizes_op_nextNY`, `realizes_rmwLoopNY`,
`realizes_casLoopNY`).
-/

namespace Backend.Proof

open Backend E2E

/-- The epilogue's frame-record reload `ldp x29, x30, [sp], #16`. -/
def _root_.Backend.Insn.ldpFR (i : Insn) : Bool :=
  decide (i = .ldp .fp .lr (.spPostIndexed 16))

/-- **A byte of the activation's frame** read by its body: `spB + o` with `o < frameDrop`, not
the frame record's saved-LR word (`frameDrop - 8 ≤ o`) unless `lr`. -/
def RL.FrameRd (R : RL) (lr : Bool) (a : BitVec 64) : Prop :=
  ∃ o, o < frameDrop R.af ∧ (o + 8 < frameDrop R.af ∨ lr = true) ∧ a = R.spB + BitVec.ofNat 64 o

/-- **A byte the activation's run may read, located, the world reads guarded by `Y`**: a byte of
a jump table, of the frame (`FrameRd lr`), or a byte outside the frame addresses `F` and outside
the guard set `Y` (module doc), or a byte of a literal-pool word (`.data`, #565). -/
def RL.ReadInY (R : RL) (Y : BitVec 64 → Prop) (lr : Bool) (a : BitVec 64) : Prop :=
  (∃ j tg bs, R.L[j]? = some (.word tg bs) ∧ ∃ i < 4, a = R.pcOf j + BitVec.ofNat 64 i) ∨
    R.FrameRd lr a ∨ (¬ R.F a ∧ ¬ Y a) ∨
    ∃ j d, R.L[j]? = some (.data d) ∧ ∃ i < 4, a = R.pcOf j + BitVec.ofNat 64 i

/-- **A byte the activation's run may read, located** (module doc): `ReadInY` at `Y := F`. -/
def RL.ReadIn (R : RL) (lr : Bool) (a : BitVec 64) : Prop := R.ReadInY R.F lr a

/-- **The reads at `u`, located, guarded by `Y`**: the reads of the unhooked instruction `x` at
the pc, as the line's encoding (`R.envL j`) decodes, are `ReadInY Y x.ldpFR`. -/
def RL.ReadsInY (R : RL) (Y : BitVec 64 → Prop) (u : Arm.ArmState) : Prop :=
  ∀ j x t, R.L[j]? = some (.ins x t) → Arm.r .PC u = R.pcOf j → x.hooked = false →
    ∀ a, x.toArmInst (R.envL j) = .ok a → ∀ p ∈ E2E.ExecBytes.MemReads a u, ∀ k < p.2,
      R.ReadInY Y x.ldpFR (p.1 + BitVec.ofNat 64 k)

/-- **The reads at `u`, located**: the reads of the unhooked instruction `x` at the pc are
`ReadIn x.ldpFR` (`ReadsInY` at `Y := F`). -/
def RL.ReadsIn (R : RL) (u : Arm.ArmState) : Prop := R.ReadsInY R.F u

/-- **`GoodXN` with the located reads guarded by `Y`.** -/
def RL.GoodXNY (R : RL) (Y : BitVec 64 → Prop) (u : Arm.ArmState) : Prop :=
  R.GoodXN u ∧ R.ReadsInY Y u

/-- **`GoodXN` with the located reads.** -/
def RL.GoodXNR (R : RL) (u : Arm.ArmState) : Prop := R.GoodXNY R.F u

theorem RL.FrameRd.mono {R : RL} {a : BitVec 64} (h : R.FrameRd false a) (lr : Bool) :
    R.FrameRd lr a := by
  obtain ⟨o, ho, hl, e⟩ := h
  exact ⟨o, ho, hl.elim Or.inl fun h => absurd h (by decide), e⟩

theorem RL.ReadInY.mono {R : RL} {Y : BitVec 64 → Prop} {a : BitVec 64} (h : R.ReadInY Y false a)
    (lr : Bool) : R.ReadInY Y lr a :=
  h.imp_right (Or.imp_left fun h => h.mono lr)

theorem RL.ReadIn.mono {R : RL} {a : BitVec 64} (h : R.ReadIn false a) (lr : Bool) :
    R.ReadIn lr a :=
  RL.ReadInY.mono h lr

/-- A guarded read is a located read. -/
theorem RL.ReadInY.readIn {R : RL} {Y : BitVec 64 → Prop} {lr : Bool} {a : BitVec 64}
    (h : R.ReadInY Y lr a) : R.ReadIn lr a :=
  h.imp_right (Or.imp_right (Or.imp_left fun h => ⟨h.1, h.1⟩))

/-- Guarded reads at a larger guard set are guarded reads at a smaller one. -/
theorem RL.ReadInY.anti {R : RL} {Y Y' : BitVec 64 → Prop} {lr : Bool} {a : BitVec 64}
    (h : R.ReadInY Y lr a) (hY : ∀ b, Y' b → Y b) : R.ReadInY Y' lr a :=
  h.imp_right (Or.imp_right (Or.imp_left fun h => ⟨h.1, fun h' => h.2 (hY _ h')⟩))

theorem RL.ReadsInY.readsIn {R : RL} {Y : BitVec 64 → Prop} {u : Arm.ArmState}
    (h : R.ReadsInY Y u) : R.ReadsIn u :=
  fun j x t hj hpc hx a ha p hp k hk => (h j x t hj hpc hx a ha p hp k hk).readIn

theorem RL.ReadsInY.anti {R : RL} {Y Y' : BitVec 64 → Prop} {u : Arm.ArmState}
    (h : R.ReadsInY Y u) (hY : ∀ b, Y' b → Y b) : R.ReadsInY Y' u :=
  fun j x t hj hpc hx a ha p hp k hk => (h j x t hj hpc hx a ha p hp k hk).anti hY

/-- The kept addresses are not in the activation's frame. -/
theorem RL.G_not_frame {R : RL} (hR : R.Wf) {a : BitVec 64} (h : R.G a) :
    ∀ o, o < frameDrop R.af → a ≠ R.spB + BitVec.ofNat 64 o := by
  intro o ho e
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

/-- **The located reads are D2's** (for every guard set `Y`). -/
theorem RL.readIn_ok {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {lr : Bool} {a : BitVec 64}
    (h : R.ReadInY Y lr a) : R.ReadOk a := by
  rcases h with h | ⟨o, ho, -, rfl⟩ | h | h
  · exact .inr (.inl h)
  · exact .inl fun hG => RL.G_not_frame hR hG o ho rfl
  · exact .inl fun hG => h.1 (.inr hG)
  · exact .inr (.inr h)

/-- **The guarded located reads give D2.** -/
theorem RL.ReadsInY.readsAt {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState}
    (h : R.ReadsInY Y u) : R.ReadsAt u :=
  fun j x t hj hpc hx a ha p hp k hk => RL.readIn_ok hR (h j x t hj hpc hx a ha p hp k hk)

/-- **The located reads give D2.** -/
theorem RL.ReadsIn.readsAt {R : RL} (hR : R.Wf) {u : Arm.ArmState} (h : R.ReadsIn u) :
    R.ReadsAt u :=
  RL.ReadsInY.readsAt hR h

theorem RL.GoodXNY.goodXN {R : RL} {Y : BitVec 64 → Prop} {u : Arm.ArmState} (h : R.GoodXNY Y u) :
    R.GoodXN u := h.1

theorem RL.GoodXNY.goodX {R : RL} {Y : BitVec 64 → Prop} {u : Arm.ArmState} (h : R.GoodXNY Y u) :
    R.GoodX u := h.1.1

theorem RL.GoodXNY.goodXNR {R : RL} {Y : BitVec 64 → Prop} {u : Arm.ArmState}
    (h : R.GoodXNY Y u) : R.GoodXNR u := ⟨h.1, h.2.readsIn⟩

theorem RL.GoodXNR.goodXN {R : RL} {u : Arm.ArmState} (h : R.GoodXNR u) : R.GoodXN u := h.1

theorem RL.GoodXNR.goodX {R : RL} {u : Arm.ArmState} (h : R.GoodXNR u) : R.GoodX u := h.1.1

/-- A slot of the allocator's frame is a frame read. -/
theorem RL.frameRd_slot {R : RL} (hR : R.Wf) {o : Nat} (ho : o < R.fr.size) :
    R.FrameRd false (R.spB + BitVec.ofNat 64 o) := by
  refine ⟨o, Nat.lt_of_lt_of_le ho (RL.size_le_drop hR), .inl ?_, rfl⟩
  obtain ⟨⟨hfs, -⟩, hfr, -⟩ := lowerRFunc_ok hR.alloc
  have hle : R.fr.size ≤ R.fr.total := compute_size_le_total R.vc R.rf
  by_cases h0 : R.fr.total = 0
  · simp only [RL.fr] at h0 hle ho; omega
  · have hframe := hfr h0
    simp only [frameDrop, hframe, ite_true, hfs]
    simp only [RL.fr] at hle ho ⊢; omega

/-! ## Builders -/

/-- `ReadsIn` at an instruction line from the reads of its instruction as the line's encoding
(`R.envOf j`) decodes (every guard set `Y`). -/
theorem RL.readsIn_of_lineE {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState}
    {j : Nat} {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t))
    (hpc : Arm.r .PC u = R.pcOf j)
    (h : x.hooked = false → ∀ a, x.toArmInst (R.envOf j) = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemReads a u, ∀ k < p.2, R.ReadInY Y x.ldpFR (p.1 + BitVec.ofNat 64 k)) :
    R.ReadsInY Y u := by
  intro j' x' t' hj' hpc' hh
  obtain rfl := RL.pcOf_inj hR hj hj' (hpc.symm.trans hpc')
  rw [hj] at hj'
  cases hj'
  rw [RL.envL_eq hR]
  exact h hh

/-- `ReadsIn` at an instruction line from the reads of its instruction (every guard set `Y`). -/
theorem RL.readsIn_of_line {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState} {j : Nat}
    {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (h : x.hooked = false → ∀ env a, x.toArmInst env = .ok a →
      ∀ p ∈ E2E.ExecBytes.MemReads a u, ∀ k < p.2, R.ReadInY Y x.ldpFR (p.1 + BitVec.ofNat 64 k)) :
    R.ReadsInY Y u :=
  RL.readsIn_of_lineE hR hj hpc fun hh => h hh _

/-- `ReadsIn` at a line whose instruction is no load. -/
theorem RL.readsIn_noLoad {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState} {j : Nat}
    {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.loads = false) : R.ReadsInY Y u :=
  RL.readsIn_of_line hR hj hpc fun _ _ a ha p hp => by
    rw [Insn.memReads_nil hx ha] at hp; cases hp

/-- `ReadsIn` at a hooked line. -/
theorem RL.readsIn_hooked {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState} {j : Nat}
    {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = true) : R.ReadsInY Y u :=
  RL.readsIn_of_line hR hj hpc fun h => by rw [hx] at h; cases h

/-- `ReadsIn` where the pc is at no instruction line of the activation. -/
theorem RL.readsIn_noLine {R : RL} {Y : BitVec 64 → Prop} {u : Arm.ArmState}
    (h : ∀ j x t, R.L[j]? = some (.ins x t) → Arm.r .PC u ≠ R.pcOf j) : R.ReadsInY Y u :=
  fun j x t hj hpc => absurd hpc (h j x t hj)

/-- `ReadsIn` at a `GoodX` state whose line holds no load. -/
theorem RL.readsIn_of_goodX {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState}
    (hg : R.GoodX u) (h : ∀ x, R.AtLine u x → x.loads = false) : R.ReadsInY Y u := by
  obtain ⟨x, ⟨j, t, hj, hpc⟩, -⟩ := hg.line
  exact RL.readsIn_noLoad hR hj hpc (h x ⟨j, t, hj, hpc⟩)

/-- **The located reads of a straight-line run** from the reads of its lines: the lines' reads
satisfy `Pa`, which at every loading line `x` gives `ReadIn x.ldpFR`. -/
theorem RL.readsIn_execLinesP {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ls : List Line} {j : Nat}
    {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s') {Pa : BitVec 64 → Prop}
    (hrd : LinesReads (R.envOf j) ls s Pa)
    (hP : ∀ x t, Line.ins x t ∈ ls → x.loads = true → ∀ a, Pa a → R.ReadInY Y x.ldpFR a) :
    ∀ i < ls.length, R.ReadsInY Y (iterN R.step i s) := by
  intro i hi
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls j s s' hat hhook
    hprog hpc herr hinter hrun
  obtain ⟨ln, hln⟩ : ∃ ln, ls[i]? = some ln := ⟨ls[i], List.getElem?_eq_getElem hi⟩
  have hmem := List.mem_of_getElem? hln
  obtain ⟨x, t, rfl⟩ := execLines_ins hrun _ hmem
  have hj : R.L[j + i]? = some (.ins x t) := hat i _ hln
  have hpci : Arm.r .PC (iterN R.step i s) = R.pcOf (j + i) := hpcs i (by omega)
  have hst : ∃ s1, execLines (R.envOf j) (ls.take i) s = some s1 ∧ iterN R.step i s = s1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨s, by simp [execLines], rfl⟩
    · obtain ⟨s1, hs1⟩ := execLines_take i hrun
      have hlen : (ls.take i).length = i := by simp; omega
      have hit := iterN_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit (ls.take i) j s s1
        (fun k ln hk => by
          rw [List.getElem?_take] at hk
          split at hk
          · exact hat k ln hk
          · cases hk)
        (fun i' t' hm => hhook i' t' (List.mem_of_mem_take hm)) hprog hpc herr
        (fun k hk0 hk s2 hs2 => hinter k hk0 (by omega) s2 (by
          rwa [List.take_take, Nat.min_eq_left (by omega)] at hs2)) hs1
      rw [hlen] at hit
      exact ⟨s1, hs1, hit⟩
  obtain ⟨s1, hs1, hit1⟩ := hst
  refine RL.readsIn_of_line hR hj hpci fun _ env a ha p hp k hk => ?_
  cases hl : x.loads
  · rw [Insn.memReads_nil hl ha] at hp; cases hp
  · rw [hit1] at hp
    exact hP x t hmem hl _ (hrd i x t hln s1 hs1 env a ha p hp k hk)

/-- `RL.readsIn_execLinesP` for reads `ReadIn false` (no line reads the saved LR word). -/
theorem RL.readsIn_execLines {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ls : List Line} {j : Nat}
    {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s (R.ReadInY Y false)) :
    ∀ i < ls.length, R.ReadsInY Y (iterN R.step i s) :=
  RL.readsIn_execLinesP hR hat hhook hprog hpc herr hinter hrun hrd fun x _ _ _ _ h => h.mono _

/-- **The states of a straight-line run with their located reads** (`RL.goodXN_execLinesG`). -/
theorem RL.goodXNR_execLinesG {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ls : List Line} {j : Nat}
    {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h0 : R.Good s) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s (R.ReadInY Y false)) :
    ∀ i < ls.length, R.GoodXNY Y (iterN R.step i s) := fun i hi =>
  ⟨RL.goodXN_execLinesG hR hat hhook htail hprog hpc herr h0 hinter hrun
      (hrd.mono fun _ h => RL.readIn_ok hR h) i hi,
    RL.readsIn_execLines hR hat hhook hprog hpc herr hinter hrun hrd i hi⟩

theorem RL.goodXNR_execLines {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ls : List Line} {j : Nat}
    {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s (R.ReadInY Y false)) :
    ∀ i < ls.length, R.GoodXNY Y (iterN R.step i s) :=
  RL.goodXNR_execLinesG hR hat hhook htail hprog hpc herr (.inr hsp) hinter hrun hrd

/-- `RL.goodXNR_execLinesG` for reads `Pa` that are D2's and, at each loading line `x`,
`ReadIn x.ldpFR` (the epilogue's `ldp` reads the saved LR word). -/
theorem RL.goodXNR_execLinesGP {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {ls : List Line} {j : Nat}
    {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h0 : R.Good s) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s') {Pa : BitVec 64 → Prop}
    (hok : ∀ a, Pa a → R.ReadOk a)
    (hP : ∀ x t, Line.ins x t ∈ ls → x.loads = true → ∀ a, Pa a → R.ReadInY Y x.ldpFR a)
    (hrd : LinesReads (R.envOf j) ls s Pa) :
    ∀ i < ls.length, R.GoodXNY Y (iterN R.step i s) := fun i hi =>
  ⟨RL.goodXN_execLinesG hR hat hhook htail hprog hpc herr h0 hinter hrun (hrd.mono hok) i hi,
    RL.readsIn_execLinesP hR hat hhook hprog hpc herr hinter hrun hrd hP i hi⟩

end Backend.Proof

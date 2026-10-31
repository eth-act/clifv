import FV.E2E.RegLevelMove

/-!
# The frames of nested activations are disjoint (#473, (iv))

An activation `R` entered in `R.s0` owns the stack bytes `[sp₀ - (drop + K), sp₀)` (`Region`):
its frame `[sp₀ - drop, sp₀)` (`Frame`; `drop = frameDrop R.af`) and, below the body's `sp`, the
`K` bytes of its callees' dead stack. A callee `B` called by `A` is **nested** in `A`
(`Nested A B`): `B` is entered with its whole region inside `A`'s dead stack (the `bl` leaves
`sp` at or below `A`'s body `sp`), and `B` keeps exactly `A`'s frame and kept addresses
(`B.G = A.FK`).

* `frameF_frame`: an activation's frame addresses (`frameF`: spill/float-move slots, the
  clobber area and fp/lr) are its `Frame`, or its code words;
* `slotArea`: the explicit CLIF slots `[spB + size, spB + frameSize - clobberBytes)` lie in the
  `Frame` and outside `frameF`'s stack part (`slotArea_frame`, `slotArea_not_frameF`);
* `Nested.region_dead`, `Nested.frame_not_FK`: a nested callee's region is in the caller's dead
  stack, so its frame avoids the caller's frame and kept addresses;
* **`Nested.gfree`**: the callee's kept addresses avoid its own region (`RL.Wf.gfree` of the
  callee from the caller's);
* `Chain`: the live activations of a thread (innermost first), each nested in the next;
  **`Chain.region_dead`**/**`Chain.frame_disj`**: every activation's region lies in the dead
  stack of each of its callers, so the frames of distinct live activations are disjoint;
  **`Chain.slot_not_F`**: the CLIF slots of every live activation are in the innermost
  activation's world (outside its `RL.F`) — the thread-wide private set is the union of the
  live frames, and the CLIF events, which avoid the innermost `RL.F`, avoid all of them.
-/

namespace Concurrency.FrameDisj

open Backend Backend.Proof E2E

/-- The stack region of the activation: its frame and its callees' budget. -/
def Region (R : RL) : BitVec 64 → Prop := StackBelow (frameDrop R.af + R.K) (spv R.s0)

/-- The activation's frame `[sp₀ - drop, sp₀)`. -/
def Frame (R : RL) : BitVec 64 → Prop := StackBelow (frameDrop R.af) (spv R.s0)

/-- The explicit CLIF slots: `[spB + size, spB + frameSize - clobberBytes)`, below the clobber
area the prologue pushes the saved registers into (part of `frameF`). -/
def slotArea (R : RL) (a : BitVec 64) : Prop :=
  R.fr.size ≤ (a - R.spB).toNat ∧ (a - R.spB).toNat < R.af.frameSize - clobberBytes R.af.saves

/-- **The callee `B` is nested in the caller `A`** (module doc). -/
structure Nested (A B : RL) : Prop where
  /-- `B`'s entry `sp` is at or below `A`'s body `sp` -/
  sp_le : (spv B.s0).toNat ≤ A.spB.toNat
  /-- `B`'s region fits in `A`'s callee budget -/
  fits : A.spB.toNat + (frameDrop B.af + B.K) ≤ (spv B.s0).toNat + A.K
  /-- `B` keeps `A`'s frame and kept addresses -/
  keep : B.G = A.FK

section
variable {R : RL}

theorem spB_toNat (hR : R.Wf) :
    R.spB.toNat = (spv R.s0).toNat - frameDrop R.af ∧ frameDrop R.af + R.K ≤ (spv R.s0).toNat :=
  spBody_toNat hR.stack

/-- The int/spill area and the CLIF slots end below the frame drop. -/
theorem size_le_drop (hR : R.Wf) : R.fr.size ≤ R.af.frameSize ∧ R.af.frameSize ≤ frameDrop R.af ∨
    R.fr.size = 0 ∧ R.af.frameSize = 0 ∧ frameDrop R.af = 0 := by
  obtain ⟨⟨hfs, -⟩, hfr, -⟩ := lowerRFunc_ok hR.alloc
  have hle : R.fr.size ≤ R.fr.total := compute_size_le_total R.vc R.rf
  simp only [RL.fr] at hle hfr ⊢
  unfold frameDrop
  by_cases hf : R.af.frame = true
  · left; simp only [hf, ite_true]; omega
  · right
    have h0 : (RAFrame.compute R.vc R.rf).total = 0 := Classical.byContradiction fun h => hf (hfr h)
    have hf' : R.af.frame = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, ite_false]
    exact ⟨by omega, by omega, trivial⟩

/-- `(a - spB).toNat < drop` places `a` in the frame. -/
theorem frame_of_off (hR : R.Wf) {a : BitVec 64} (h : (a - R.spB).toNat < frameDrop R.af) :
    Frame R a := by
  obtain ⟨h1, h2⟩ := spB_toNat hR
  have hlt := (spv R.s0).isLt
  have hal := a.isLt
  rw [BitVec.toNat_sub] at h
  unfold Frame StackBelow
  by_cases hge : R.spB.toNat ≤ a.toNat
  · rw [show 2 ^ 64 - R.spB.toNat + a.toNat = (a.toNat - R.spB.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- **The frame addresses are the frame or code** (module doc). -/
theorem frameF_frame (hR : R.Wf) {a : BitVec 64}
    (h : frameF R.fr.intBase R.fr.size R.af R.s0 a) : Frame R a ∨ CodeAddr R.s0 a := by
  have hd := size_le_drop hR
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | h
  · left; exact frame_of_off hR (by simp only [RL.spB]; omega)
  · left; exact frame_of_off hR (by simp only [RL.spB]; omega)
  · exact .inr h

theorem frame_region {a : BitVec 64} (h : Frame R a) : Region R a := by
  unfold Frame Region StackBelow at *; omega

theorem slotArea_frame (hR : R.Wf) {a : BitVec 64} (h : slotArea R a) : Frame R a := by
  have hd := size_le_drop hR
  exact frame_of_off hR (by unfold slotArea at h; omega)

/-- The CLIF slots are not among the frame's stack addresses. -/
theorem slotArea_not_frameF {a : BitVec 64} (h : slotArea R a)
    (hf : frameF R.fr.intBase R.fr.size R.af R.s0 a) : CodeAddr R.s0 a := by
  unfold slotArea at h
  rcases hf with ⟨-, hf⟩ | ⟨hf, -⟩ | hf
  · simp only [RL.spB] at h; omega
  · simp only [RL.spB] at h; omega
  · exact hf

/-- The dead stack below the body's `sp` is in the region and outside the frame. -/
theorem dead_region (hR : R.Wf) {a : BitVec 64} (h : StackBelow R.K R.spB a) :
    Region R a ∧ ¬ Frame R a := by
  obtain ⟨h1, h2⟩ := spB_toNat hR
  unfold StackBelow at h
  unfold Region Frame StackBelow
  omega

/-- The activation's code avoids its region (`StackRoom`). -/
theorem code_not_region (hR : R.Wf) {a : BitVec 64} (hc : CodeAddr R.s0 a) : ¬ Region R a := by
  have hroom := hR.stack.1
  have hd : frameDrop R.af ≤ R.af.frameSize + 16 := frameDrop_le R.af
  have h2 := hroom.2 a hc
  have h1 := hroom.1
  have hlt := (spv R.s0).isLt
  have hal := a.isLt
  intro ⟨ha1, ha2⟩
  -- `a` lies within the `frameSize + 16 + K` bytes below `sp₀`
  have e : (a - (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16 + R.K))).toNat =
      a.toNat - ((spv R.s0).toNat - (R.af.frameSize + 16 + R.K)) := by
    have hn : (R.af.frameSize + 16 + R.K) % 2 ^ 64 = R.af.frameSize + 16 + R.K :=
      Nat.mod_eq_of_lt (by omega)
    have hs : (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16 + R.K)).toNat =
        (spv R.s0).toNat - (R.af.frameSize + 16 + R.K) := by
      rw [BitVec.toNat_sub_of_le] <;> simp only [BitVec.le_def, BitVec.toNat_ofNat, hn] <;> omega
    rw [BitVec.toNat_sub_of_le] <;> simp only [BitVec.le_def, hs] <;> omega
  rw [e] at h2
  omega

end

/-! ## A callee nested in its caller -/

section nested
variable {A B : RL}

/-- The body's `sp` does not wrap and the callees' budget fits below it, from the stack room
alone (`spBody_toNat` without `StackAvail`'s probe budget, #581). -/
theorem spBody_toNat_room {K : Nat} {af : AFunc} {s : Arm.ArmState}
    (h : StackRoom (af.frameSize + 16 + K) s) :
    (spv s - BitVec.ofNat 64 (frameDrop af)).toNat = (spv s).toNat - frameDrop af ∧
      frameDrop af + K ≤ (spv s).toNat := by
  have h1 := h.1
  have h2 := frameDrop_le af
  have hlt := (spv s).isLt
  refine ⟨?_, by omega⟩
  rw [BitVec.toNat_sub_of_le] <;>
    simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : frameDrop af < 2 ^ 64)]
  omega

/-- `Nested.region_dead` from the callee's stack room alone (#581: the region does not need
`StackAvail`'s probe budget). -/
theorem Nested.region_dead_room (hn : Nested A B)
    (hB : StackRoom (B.af.frameSize + 16 + B.K) B.s0) {a : BitVec 64} (h : Region B a) :
    StackBelow A.K A.spB a := by
  have := spBody_toNat_room hB
  have := hn.sp_le
  have := hn.fits
  unfold Region StackBelow at h
  unfold StackBelow
  omega

/-- A nested callee's region is in the caller's dead stack. -/
theorem Nested.region_dead (hn : Nested A B) (hB : StackAvail B.K B.af B.s0) {a : BitVec 64}
    (h : Region B a) :
    StackBelow A.K A.spB a :=
  hn.region_dead_room hB.1 h

/-- `Nested.region_not_FK` from the callee's stack room alone (#581). -/
theorem Nested.region_not_FK_room (hn : Nested A B) (hA : A.Wf)
    (hB : StackRoom (B.af.frameSize + 16 + B.K) B.s0) {a : BitVec 64}
    (h : Region B a) : ¬ A.FK a := by
  have hd := hn.region_dead_room hB h
  obtain ⟨hreg, hnf⟩ := dead_region hA hd
  rintro (hf | hg)
  · rcases frameF_frame hA hf with hf | hc
    · exact hnf hf
    · exact code_not_region hA hc hreg
  · refine hA.gfree a hg ?_
    unfold Region at hreg; exact hreg

/-- A nested callee's region avoids the caller's frame and kept addresses. -/
theorem Nested.region_not_FK (hn : Nested A B) (hA : A.Wf) (hB : StackAvail B.K B.af B.s0)
    {a : BitVec 64}
    (h : Region B a) : ¬ A.FK a :=
  hn.region_not_FK_room hA hB.1 h

/-- **The callee's kept addresses avoid its region** (`RL.Wf.gfree` of the callee, which needs
only its stack room). -/
theorem Nested.gfree (hn : Nested A B) (hA : A.Wf) (hB : StackAvail B.K B.af B.s0) :
    ∀ a, B.G a → ¬ StackBelow (frameDrop B.af + B.K) (spv B.s0) a := fun a hg h => by
  rw [hn.keep] at hg
  exact hn.region_not_FK hA hB h hg

end nested

/-! ## The live activations of a thread -/

/-- The live activations, innermost first, each nested in the next. -/
def Chain : List RL → Prop
  | [] => True
  | [_] => True
  | B :: A :: rest => Nested A B ∧ Chain (A :: rest)

theorem Chain.tail {R : RL} {rest : List RL} (h : Chain (R :: rest)) : Chain rest := by
  match rest, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

/-- **The innermost activation's region lies in the dead stack of every other live
activation.** -/
theorem Chain.region_dead {T : RL} : ∀ {rest : List RL}, Chain (T :: rest) →
    (∀ R ∈ T :: rest, R.Wf) → ∀ C ∈ rest, ∀ a, Region T a → StackBelow C.K C.spB a
  | [], _, _, _, h, _, _ => by simp at h
  | A :: rest, hc, hw, C, hC, a, ha => by
    have hn : Nested A T := hc.1
    have hT : T.Wf := hw T (by simp)
    have hA : A.Wf := hw A (by simp)
    have hd := hn.region_dead hT.stack ha
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hd
    · have hreg := (dead_region hA hd).1
      exact Chain.region_dead hc.2 (fun R hR => hw R (List.mem_cons_of_mem _ hR)) C hC a hreg

/-- **The frames of distinct live activations are disjoint**: the `i`-th and the `j`-th
(`i < j`, innermost first). -/
theorem Chain.frame_disj : ∀ {L : List RL}, Chain L → (∀ R ∈ L, R.Wf) →
    ∀ i j (hi : i < L.length) (hj : j < L.length), i < j → ∀ a, Frame L[i] a → ¬ Frame L[j] a
  | [], _, _, _, _, hi, _, _, _, _ => by simp at hi
  | T :: rest, hc, hw, i, j, hi, hj, hij, a, ha => by
    cases i with
    | zero =>
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hC : rest[j]'(by simp at hj; omega) ∈ rest := List.getElem_mem _
      have hd := Chain.region_dead hc hw _ hC a (frame_region ha)
      exact (dead_region (hw _ (List.mem_cons_of_mem _ hC)) hd).2
    | succ i =>
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact Chain.frame_disj hc.tail (fun R hR => hw R (List.mem_cons_of_mem _ hR)) i j
        (by simp at hi; omega) (by simp at hj; omega) (by omega) a ha

/-- The kept addresses of the innermost activation: the frame addresses of every other live
activation, or the outermost's kept addresses. -/
theorem Chain.G_cases {T : RL} : ∀ {rest : List RL}, Chain (T :: rest) → ∀ a, T.G a →
    (∃ C ∈ rest, frameF C.fr.intBase C.fr.size C.af C.s0 a) ∨ ((T :: rest).getLast (by simp)).G a
  | [], _, a, h => .inr h
  | A :: rest, hc, a, h => by
    have hn : Nested A T := hc.1
    rw [hn.keep] at h
    rcases h with h | h
    · exact .inl ⟨A, by simp, h⟩
    · rcases Chain.G_cases hc.2 a h with ⟨C, hC, hf⟩ | hl
      · exact .inl ⟨C, List.mem_cons_of_mem _ hC, hf⟩
      · right; simpa using hl

/-- **The CLIF slots of every live activation are in the innermost one's world** (outside its
`RL.F`; module doc), when no activation's code lies in the outermost region. -/
theorem Chain.slot_not_F {T : RL} {rest : List RL} (hc : Chain (T :: rest))
    (hw : ∀ R ∈ T :: rest, R.Wf)
    (hcode : ∀ R ∈ T :: rest, ∀ a, CodeAddr R.s0 a → ¬ Region ((T :: rest).getLast (by simp)) a)
    {C : RL} (hC : C ∈ T :: rest) {a : BitVec 64} (hs : slotArea C a) : ¬ T.F a := by
  have hCw := hw C hC
  have hfC := slotArea_frame hCw hs
  -- the slot is in the outermost region
  have hlast : ∀ {L : List RL} (hL : L ≠ []), Chain L → (∀ R ∈ L, R.Wf) → ∀ R ∈ L, ∀ a,
      Region R a → Region (L.getLast hL) a := by
    intro L
    induction L with
    | nil => intro hL; exact absurd rfl hL
    | cons R0 L ih =>
      intro _ hcL hwL R hR a ha
      cases L with
      | nil =>
        simp at hR; subst hR; simpa using ha
      | cons A L =>
        rw [List.getLast_cons (by simp)]
        rcases List.mem_cons.mp hR with e | hR'
        · subst e
          exact ih (by simp) hcL.tail (fun R hR => hwL R (List.mem_cons_of_mem _ hR)) A (by simp) a
            (dead_region (hwL A (by simp)) (hcL.1.region_dead (hwL _ (by simp)).stack ha)).1
        · exact ih (by simp) hcL.tail (fun R hR => hwL R (List.mem_cons_of_mem _ hR)) R hR' a ha
  have hTw := hw T (by simp)
  intro hF
  rcases hF with (hf | hd) | hg
  · -- `T`'s frame addresses
    rcases List.mem_cons.mp hC with e | hC'
    · subst e
      exact code_not_region hTw (slotArea_not_frameF hs hf) (frame_region hfC)
    · rcases frameF_frame hTw hf with hfr | hcd
      · exact (dead_region (hw C hC) (Chain.region_dead hc hw C hC' a (frame_region hfr))).2 hfC
      · exact hcode T (by simp) a hcd (hlast (by simp) hc hw C hC a (frame_region hfC))
  · -- `T`'s dead stack
    obtain ⟨-, hnf⟩ := dead_region hTw hd
    rcases List.mem_cons.mp hC with rfl | hC'
    · exact hnf hfC
    · have hreg := (dead_region hTw hd).1
      exact (dead_region (hw C hC) (Chain.region_dead hc hw C hC' a hreg)).2 hfC
  · rcases Chain.G_cases hc a hg with ⟨D, hD, hf⟩ | hl
    · have hDw := hw D (List.mem_cons_of_mem _ hD)
      by_cases e : C = D
      · subst e
        exact code_not_region hDw (slotArea_not_frameF hs hf) (frame_region hfC)
      · rcases frameF_frame hDw hf with hfr | hcd
        · -- distinct live frames are disjoint
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_cons_of_mem T hD)
          have hij : i ≠ j := fun h => e (by subst h; rfl)
          rcases Nat.lt_or_gt_of_ne hij with h | h
          · exact Chain.frame_disj hc hw i j hi hj h a hfC hfr
          · exact Chain.frame_disj hc hw j i hj hi h a hfr hfC
        · exact hcode D (List.mem_cons_of_mem _ hD) a hcd
            (hlast (by simp) hc hw C hC a (frame_region hfC))
    · have hLw := hw _ (List.getLast_mem (by simp))
      exact hLw.gfree a hl (hlast (by simp) hc hw C hC a (frame_region hfC))

end Concurrency.FrameDisj

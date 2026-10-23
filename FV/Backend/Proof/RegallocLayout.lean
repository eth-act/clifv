import FV.Backend.Proof.RegallocFrame

/-!
# The frame layout of `RAFrame.compute` (M6 proof)

`frameOk_compute`: the frame `RAFrame.compute vc rf` satisfies `FrameOk` for the live
locations (`Live rf`), with `fmoveTmp` available when the code has float register moves, for
any `sp0` whose frame does not wrap around and any `F` containing `[sp0 + intBase, sp0 + size)`.
The layout (all offsets from `sp0`):

```
[intBase, intBase + 8 n)           int spill slots          (n = spillSlots)
[floatBase, floatBase + 16 n)      float spill slots        (if used)
[fmoveTmp, fmoveTmp + 16)          float move temporary     (if used)
                                   size = alignTo _ 16
[size, size + slotBytes)           explicit CLIF slots (not the allocator's)
[saveBase, total)                  clobber area: the registers the prologue pushes
                                   (`clobberOff`; saveBase = alignTo _ 16 = total - clobberBytes)
```
-/

namespace Backend.Proof

open Backend

theorem le_alignTo16 (n : Nat) : n ≤ alignTo n 16 := by
  unfold alignTo; omega

theorem lookup_mem {L : List (Reg × Nat)} {r : Reg} {o : Nat} (h : L.lookup r = some o) :
    (r, o) ∈ L := by
  induction L with
  | nil => simp at h
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup] at h
    by_cases e : r = a
    · subst e; simp at h; subst h; simp
    · have : (r == a) = false := by simpa using e
      rw [this] at h; exact List.mem_cons_of_mem _ (ih h)

theorem align_facts (x : Nat) (fm : Bool) :
    alignTo x 16 ≤ alignTo (if fm = true then alignTo x 16 + 16 else x) 16 ∧
      (fm = true → alignTo x 16 + 16 ≤ alignTo (if fm = true then alignTo x 16 + 16 else x) 16) := by
  cases fm
  · simp
  · simp only [if_true, forall_const]
    have := le_alignTo16 (alignTo x 16 + 16)
    omega

/-- The numeric layout of the computed frame: the int spill slots below the float spill slots
(`sB` is the end of the float spill area), then `fmoveTmp`, all below `size`; the clobber area
`[saveBase, total)` above the CLIF slots. -/
theorem compute_facts (vc : VCode) (rf : RFunc) :
    let fr := RAFrame.compute vc rf
    let sB := fr.floatBase + (if rf.floatStack then 16 * rf.spillSlots else 0)
    fr.intBase + 8 * rf.spillSlots ≤ fr.floatBase ∧
      sB ≤ fr.fmoveTmp ∧ fr.fmoveTmp ≤ fr.size ∧
      (rf.floatMove = true → fr.fmoveTmp + 16 ≤ fr.size) := by
  intro fr sB
  simp only [fr, sB, RAFrame.compute]
  refine ⟨le_alignTo16 _, le_alignTo16 _, (align_facts _ _).1, (align_facts _ _).2⟩

/-- The clobber area: it starts 16-aligned above the CLIF slots and ends at `total`. -/
theorem compute_saveBase (vc : VCode) (rf : RFunc) :
    (RAFrame.compute vc rf).size + vc.slotBytes ≤ (RAFrame.compute vc rf).total - clobberBytes rf.saved ∧
      (RAFrame.compute vc rf).total - clobberBytes rf.saved + clobberBytes rf.saved =
        (RAFrame.compute vc rf).total ∧
      ((RAFrame.compute vc rf).total - clobberBytes rf.saved) % 16 = 0 := by
  have e : (RAFrame.compute vc rf).total =
      alignTo ((RAFrame.compute vc rf).size + vc.slotBytes) 16 + clobberBytes rf.saved := rfl
  rw [e, Nat.add_sub_cancel]
  exact ⟨le_alignTo16 _, rfl, by unfold alignTo; omega⟩

theorem compute_size_le_total (vc : VCode) (rf : RFunc) :
    (RAFrame.compute vc rf).size ≤ (RAFrame.compute vc rf).total := by
  have := (compute_saveBase vc rf).1
  have := (compute_saveBase vc rf).2.1
  omega

theorem toNat_add_ofNat {a : BitVec 64} {o : Nat} (h : a.toNat + o < 2 ^ 64) :
    (a + BitVec.ofNat 64 o).toNat = a.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

/-- A live location's slot: its offset and where it lies. -/
theorem live_slot {vc : VCode} {rf : RFunc} {l : Loc} {o : Nat} (hD : Live rf l)
    (ho : (RAFrame.compute vc rf).offset l = .ok o) :
    let fr := RAFrame.compute vc rf
    (∃ k, l = .stack k .int ∧ k < rf.spillSlots ∧ o = fr.intBase + 8 * k ∧ slotBytes l = 8) ∨
    (∃ k, l = .stack k .float ∧ k < rf.spillSlots ∧ rf.floatStack = true ∧
      o = fr.floatBase + 16 * k ∧ slotBytes l = 16) := by
  intro fr
  cases l with
  | reg r => simp [RAFrame.offset] at ho
  | stack k c =>
    cases c with
    | int =>
      simp only [RAFrame.offset, pure, Except.pure, Except.ok.injEq] at ho
      exact .inl ⟨k, rfl, hD, ho.symm, rfl⟩
    | float =>
      simp only [RAFrame.offset, pure, Except.pure, Except.ok.injEq] at ho
      exact .inr ⟨k, rfl, hD.1, hD.2, ho.symm, rfl⟩
  | save r => exact absurd hD id

theorem alignTo16_mod (x : Nat) : alignTo x 16 % 16 = 0 := by
  unfold alignTo; omega

theorem compute_align (vc : VCode) (rf : RFunc) :
    (RAFrame.compute vc rf).intBase % 16 = 0 ∧ (RAFrame.compute vc rf).floatBase % 16 = 0 ∧
      (RAFrame.compute vc rf).fmoveTmp % 16 = 0 :=
  ⟨alignTo16_mod _, alignTo16_mod _, alignTo16_mod _⟩

/-- A live slot is aligned to its size and lies below the frame size. -/
theorem live_align {vc : VCode} {rf : RFunc} {l : Loc} {o : Nat} (hD : Live rf l)
    (ho : (RAFrame.compute vc rf).offset l = .ok o) :
    o % slotBytes l = 0 ∧ o + slotBytes l ≤ (RAFrame.compute vc rf).size := by
  obtain ⟨a1, a2, a3⟩ := compute_align vc rf
  obtain ⟨h1, h2, h3, h4⟩ := compute_facts vc rf
  rcases live_slot hD ho with ⟨k, rfl, hk, rfl, hs⟩ | ⟨k, rfl, hk, hfs, rfl, hs⟩ <;> rw [hs]
  · omega
  · simp only [hfs, ite_true] at h2; omega

/-- **The computed frame is laid out correctly** (for a frame that does not wrap around and
frame addresses covering `[sp0 + intBase, sp0 + size)`). -/
theorem frameOk_compute (vc : VCode) (rf : RFunc) (sp0 : BitVec 64) (F : BitVec 64 → Prop)
    (hwrap : sp0.toNat + (RAFrame.compute vc rf).size < 2 ^ 64)
    (hF : ∀ o, (RAFrame.compute vc rf).intBase ≤ o → o < (RAFrame.compute vc rf).size →
      F (sp0 + BitVec.ofNat 64 o)) :
    FrameOk (RAFrame.compute vc rf) (Live rf) (rf.floatMove = true) sp0 F := by
  obtain ⟨h1, h2, h3, h4⟩ := compute_facts vc rf
  have hadd : ∀ o k, sp0 + BitVec.ofNat 64 o + BitVec.ofNat 64 k = sp0 + BitVec.ofNat 64 (o + k) := by
    intro o k; rw [BitVec.add_assoc, BitVec.ofNat_add]
  -- every live slot lies in `[intBase, fmoveTmp)`
  have hin : ∀ l o, Live rf l → (RAFrame.compute vc rf).offset l = .ok o →
      (RAFrame.compute vc rf).intBase ≤ o ∧ o + slotBytes l ≤ (RAFrame.compute vc rf).fmoveTmp := by
    intro l o hD ho
    rcases live_slot hD ho with ⟨k, rfl, hk, rfl, hs⟩ | ⟨k, rfl, hk, hfs, rfl, hs⟩ <;> rw [hs]
    · by_cases hfs : rf.floatStack = true <;> simp [hfs] at h2 <;> omega
    · simp only [hfs, if_true] at h2; omega
  refine ⟨fun l l' o o' hD hD' hne ho ho' => ?_, fun l o hD ho k hk => ?_,
    fun hT l o hD ho => ?_, fun hT k hk => ?_⟩
  · have r1 := hin l o hD ho
    have r2 := hin l' o' hD' ho'
    apply Arm.mem_separate'.of_omega
    rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rcases live_slot hD ho with ⟨k, rfl, hk, rfl, hs⟩ | ⟨k, rfl, hk, hfs, rfl, hs⟩ <;>
      rcases live_slot hD' ho' with ⟨k', rfl, hk', rfl, hs'⟩ | ⟨k', rfl, hk', hfs', rfl, hs'⟩ <;>
      rw [hs, hs'] <;> (try simp only [hfs, hfs', if_true] at h2 ⊢) <;>
      (try (by_cases hkk : k = k'
            · subst hkk; exact absurd rfl hne)) <;>
      by_cases hfs2 : rf.floatStack = true <;>
      (try simp only [hfs2, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false] at *) <;> omega
  · have r1 := hin l o hD ho
    rw [hadd]; exact hF _ (by omega) (by omega)
  · have r1 := hin l o hD ho
    have := h4 hT
    apply Arm.mem_separate'.of_omega
    rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    omega
  · have := h4 hT
    rw [hadd]; exact hF _ (by omega) (by omega)

end Backend.Proof

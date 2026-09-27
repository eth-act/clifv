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
[saveBase, e1)                     float save slots, 16 bytes each
[e1, e2)                           int save slots, 8 bytes each
[fmoveTmp, fmoveTmp + 16)          float move temporary     (if used)
                                   size = alignTo _ 16
```
-/

namespace Backend.Proof

open Backend

theorem le_alignTo16 (n : Nat) : n ≤ alignTo n 16 := by
  unfold alignTo; omega

/-- The save-slot fold: entries `(r, o + w * i)` for the `i`-th register. -/
theorem foldl_slots (w : Nat) (f : List (Reg × Nat) × Nat → Reg → List (Reg × Nat) × Nat)
    (hf : ∀ acc o r, f (acc, o) r = (acc ++ [(r, o)], o + w)) :
    ∀ (rs : List Reg) (acc : List (Reg × Nat)) (o : Nat),
      rs.foldl f (acc, o) = (acc ++ (List.range rs.length).map (fun i => (rs[i]!, o + w * i)),
        o + w * rs.length)
  | [], acc, o => by simp
  | r :: rs, acc, o => by
    rw [List.foldl_cons, hf, foldl_slots w f hf rs]
    simp only [List.length_cons, Prod.mk.injEq]
    refine ⟨?_, by rw [Nat.mul_succ]; omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.append_assoc]
    congr 2 <;> simp [Nat.mul_succ] <;> intros <;> omega

theorem mem_slots {w o0 : Nat} {rs : List Reg} {r : Reg} {o : Nat}
    (h : (r, o) ∈ (List.range rs.length).map (fun i => (rs[i]!, o0 + w * i))) :
    ∃ i, i < rs.length ∧ rs[i]? = some r ∧ o = o0 + w * i := by
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨i, hi, h1, h2⟩ := h
  refine ⟨i, hi, ?_, h2.symm⟩
  rw [← h1, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

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

/-- A save-slot entry of the computed frame: its register's class fixes its size, its offset
its position. -/
theorem save_entry {vc : VCode} {rf : RFunc} {r : Reg} {o : Nat}
    (h : (RAFrame.compute vc rf).saveOff.lookup r = some o) :
    let fr := RAFrame.compute vc rf
    let sB := fr.floatBase + (if rf.floatStack then 16 * rf.spillSlots else 0)
    let fl := rf.saved.filter (·.realClass? == some .float)
    let il := rf.saved.filter (·.realClass? == some .int)
    (∃ i, i < fl.length ∧ fl[i]? = some r ∧ o = sB + 16 * i ∧ slotBytes (.save r) = 16) ∨
      (∃ i, i < il.length ∧ il[i]? = some r ∧ o = sB + 16 * fl.length + 8 * i ∧
        slotBytes (.save r) = 8) := by
  intro fr sB fl il
  have hm := lookup_mem h
  have e1 := foldl_slots 16 (fun (p : List (Reg × Nat) × Nat) r => (p.1 ++ [(r, p.2)], p.2 + 16))
    (fun _ _ _ => rfl) fl [] sB
  have e2 := foldl_slots 8 (fun (p : List (Reg × Nat) × Nat) r => (p.1 ++ [(r, p.2)], p.2 + 8))
    (fun _ _ _ => rfl) il [] (sB + 16 * fl.length)
  simp only [fr, sB, fl, il, RAFrame.compute] at hm e1 e2 ⊢
  rw [e1] at hm
  simp only [List.nil_append] at hm
  rw [e2] at hm
  simp only [List.nil_append, List.mem_append] at hm
  rcases hm with hm | hm
  · obtain ⟨i, hi, hr, ho⟩ := mem_slots hm
    have hc : r.realClass? = some .float := by
      have := List.mem_of_getElem? hr
      simpa [fl] using (List.mem_filter.1 this).2
    refine .inl ⟨i, hi, hr, ho, ?_⟩
    cases r <;> simp_all [Reg.realClass?, slotBytes]
  · obtain ⟨i, hi, hr, ho⟩ := mem_slots hm
    have hc : r.realClass? = some .int := by
      have := List.mem_of_getElem? hr
      simpa [il] using (List.mem_filter.1 this).2
    refine .inr ⟨i, hi, hr, ho, ?_⟩
    cases r <;> simp_all [Reg.realClass?, slotBytes]

theorem align_facts (x : Nat) (fm : Bool) :
    alignTo x 16 ≤ alignTo (if fm = true then alignTo x 16 + 16 else x) 16 ∧
      (fm = true → alignTo x 16 + 16 ≤ alignTo (if fm = true then alignTo x 16 + 16 else x) 16) := by
  cases fm
  · simp
  · simp only [if_true, forall_const]
    have := le_alignTo16 (alignTo x 16 + 16)
    omega

/-- The numeric layout of the computed frame. -/
theorem compute_facts (vc : VCode) (rf : RFunc) :
    let fr := RAFrame.compute vc rf
    let sB := fr.floatBase + (if rf.floatStack then 16 * rf.spillSlots else 0)
    let fl := rf.saved.filter (·.realClass? == some .float)
    let il := rf.saved.filter (·.realClass? == some .int)
    fr.intBase + 8 * rf.spillSlots ≤ fr.floatBase ∧
      sB + 16 * fl.length + 8 * il.length ≤ fr.fmoveTmp ∧ fr.fmoveTmp ≤ fr.size ∧
      (rf.floatMove = true → fr.fmoveTmp + 16 ≤ fr.size) := by
  intro fr sB fl il
  have e1 := foldl_slots 16 (fun (p : List (Reg × Nat) × Nat) r => (p.1 ++ [(r, p.2)], p.2 + 16))
    (fun _ _ _ => rfl) fl [] sB
  have e2 := foldl_slots 8 (fun (p : List (Reg × Nat) × Nat) r => (p.1 ++ [(r, p.2)], p.2 + 8))
    (fun _ _ _ => rfl) il [] (sB + 16 * fl.length)
  simp only [fr, sB, fl, il, RAFrame.compute] at e1 e2 ⊢
  rw [e1]
  simp only [List.nil_append]
  rw [e2]
  dsimp only
  refine ⟨le_alignTo16 _, le_alignTo16 _, (align_facts _ _).1, (align_facts _ _).2⟩

theorem toNat_add_ofNat {a : BitVec 64} {o : Nat} (h : a.toNat + o < 2 ^ 64) :
    (a + BitVec.ofNat 64 o).toNat = a.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

/-- A live location's slot: its offset and where it lies. -/
theorem live_slot {vc : VCode} {rf : RFunc} {l : Loc} {o : Nat} (hD : Live rf l)
    (ho : (RAFrame.compute vc rf).offset l = .ok o) :
    let fr := RAFrame.compute vc rf
    let sB := fr.floatBase + (if rf.floatStack then 16 * rf.spillSlots else 0)
    let fl := rf.saved.filter (·.realClass? == some .float)
    let il := rf.saved.filter (·.realClass? == some .int)
    (∃ k, l = .stack k .int ∧ k < rf.spillSlots ∧ o = fr.intBase + 8 * k ∧ slotBytes l = 8) ∨
    (∃ k, l = .stack k .float ∧ k < rf.spillSlots ∧ rf.floatStack = true ∧
      o = fr.floatBase + 16 * k ∧ slotBytes l = 16) ∨
    (∃ r i, l = .save r ∧ i < fl.length ∧ fl[i]? = some r ∧ o = sB + 16 * i ∧ slotBytes l = 16) ∨
    (∃ r i, l = .save r ∧ i < il.length ∧ il[i]? = some r ∧ o = sB + 16 * fl.length + 8 * i ∧
      slotBytes l = 8) := by
  intro fr sB fl il
  cases l with
  | reg r => simp [RAFrame.offset] at ho
  | stack k c =>
    cases c with
    | int =>
      simp only [RAFrame.offset, pure, Except.pure, Except.ok.injEq] at ho
      exact .inl ⟨k, rfl, hD, ho.symm, rfl⟩
    | float =>
      simp only [RAFrame.offset, pure, Except.pure, Except.ok.injEq] at ho
      exact .inr (.inl ⟨k, rfl, hD.1, hD.2, ho.symm, rfl⟩)
  | save r =>
    simp only [RAFrame.offset] at ho
    split at ho
    · rename_i o' hl
      simp only [pure, Except.pure, Except.ok.injEq] at ho
      subst ho
      rcases save_entry hl with ⟨i, hi, hr, hoe, hs⟩ | ⟨i, hi, hr, hoe, hs⟩
      · exact .inr (.inr (.inl ⟨r, i, rfl, hi, hr, hoe, hs⟩))
      · exact .inr (.inr (.inr ⟨r, i, rfl, hi, hr, hoe, hs⟩))
    · cases ho


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
  rcases live_slot hD ho with ⟨k, rfl, hk, rfl, hs⟩ | ⟨k, rfl, hk, hfs, rfl, hs⟩ |
      ⟨r, i, rfl, hi, _, rfl, hs⟩ | ⟨r, i, rfl, hi, _, rfl, hs⟩ <;> rw [hs]
  · omega
  · simp only [hfs, ite_true] at h2; omega
  all_goals by_cases hfs : rf.floatStack = true <;> simp [hfs] at h2 ⊢ <;> omega

/-- **The computed frame is laid out correctly** (for a frame that does not wrap around and
frame addresses covering `[sp0 + intBase, sp0 + size)`). -/
theorem frameOk_compute (vc : VCode) (rf : RFunc) (sp0 : BitVec 64) (F : BitVec 64 → Prop)
    (hwrap : sp0.toNat + (RAFrame.compute vc rf).size < 2 ^ 64)
    (hF : ∀ o, (RAFrame.compute vc rf).intBase ≤ o → o < (RAFrame.compute vc rf).size →
      F (sp0 + BitVec.ofNat 64 o)) :
    FrameOk (RAFrame.compute vc rf) (Live rf) (rf.floatMove = true) sp0 F := by
  obtain ⟨h1, h2, h3, h4⟩ := compute_facts vc rf
  have hib : (RAFrame.compute vc rf).intBase ≤ (RAFrame.compute vc rf).floatBase := by omega
  have hadd : ∀ o k, sp0 + BitVec.ofNat 64 o + BitVec.ofNat 64 k = sp0 + BitVec.ofNat 64 (o + k) := by
    intro o k; rw [BitVec.add_assoc, BitVec.ofNat_add]
  -- every live slot lies in `[intBase, fmoveTmp)`
  have hin : ∀ l o, Live rf l → (RAFrame.compute vc rf).offset l = .ok o →
      (RAFrame.compute vc rf).intBase ≤ o ∧ o + slotBytes l ≤ (RAFrame.compute vc rf).fmoveTmp := by
    intro l o hD ho
    rcases live_slot hD ho with ⟨k, rfl, hk, rfl, hs⟩ | ⟨k, rfl, hk, hfs, rfl, hs⟩ |
        ⟨r, i, rfl, hi, _, rfl, hs⟩ | ⟨r, i, rfl, hi, _, rfl, hs⟩ <;> rw [hs]
    · omega
    · simp only [hfs, if_true] at h2; omega
    all_goals by_cases hfs : rf.floatStack = true <;> simp [hfs] at h2 ⊢ <;> omega
  refine ⟨fun l l' o o' hD hD' hne ho ho' => ?_, fun l o hD ho k hk => ?_,
    fun hT l o hD ho => ?_, fun hT k hk => ?_⟩
  · have r1 := hin l o hD ho
    have r2 := hin l' o' hD' ho'
    apply Arm.mem_separate'.of_omega
    rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rcases live_slot hD ho with ⟨k, rfl, hk, rfl, hs⟩ | ⟨k, rfl, hk, hfs, rfl, hs⟩ |
        ⟨r, i, rfl, hi, hr, rfl, hs⟩ | ⟨r, i, rfl, hi, hr, rfl, hs⟩ <;>
      rcases live_slot hD' ho' with ⟨k', rfl, hk', rfl, hs'⟩ | ⟨k', rfl, hk', hfs', rfl, hs'⟩ |
        ⟨r', i', rfl, hi', hr', rfl, hs'⟩ | ⟨r', i', rfl, hi', hr', rfl, hs'⟩ <;>
      rw [hs, hs'] <;> (try simp only [hfs, hfs', if_true] at h2 ⊢) <;>
      (try (by_cases hkk : k = k'
            · subst hkk; exact absurd rfl hne)) <;>
      (try (by_cases hii : i = i'
            · subst hii; rw [hr] at hr'; cases hr'; exact absurd rfl hne)) <;>
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

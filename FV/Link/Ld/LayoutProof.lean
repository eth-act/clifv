import FV.Link.Ld.Layout
import FV.Arm.MinTheory
import FV.Backend.Proof.IselInterp

/-! # `lean-ld`'s planner meets its plan's conditions by construction (A1a, #409)

`assemble` (`FV/Link/Ld/Plan.lean`) checks the plan's own conditions `Plan.okB` (segments in
increasing, disjoint 64 KiB pages with `p_filesz ≤ p_memsz` and their file bytes in the body;
pieces in disjoint file ranges after the headers). On `layout`'s plans the check never fails:

* the placement (`placeSec`, a fold over the output sections sorted by segment kind) keeps the
  invariant `PInv`: the closed segments are in increasing pages with their file bytes before
  the end of the file bytes reached, and the placed parts with file bytes (`Slot.bits`) lie in
  increasing, disjoint file ranges after the headers (`placeParts_spec`, `PInv_openSeg`,
  `PInv_placeIn`, `PInv_layPre`);
* each piece is its slot's (`Lay.slotPiece`: the slot's file offset, at most its size;
  `slotPiece_some`), in placement order (`pieces_pairwise`).

**`layout_okB`**: a plan `layout` returns satisfies `Plan.okB`; hence **`assemble_layout`**:
`assemble` builds its image whenever its body can be built (only a relocation can fail).
Witness: `tinyLayout_okB` (a link of one object with one section).
-/

namespace Link.Ld

open E2E.Elf

/-! ## Alignment -/

theorem le_alignUp (n a : Nat) : n ≤ alignUp n a := by
  unfold alignUp
  have h := Nat.lt_div_mul_add (a := n + max a 1 - 1) (b := max a 1) (by omega)
  generalize (n + max a 1 - 1) / max a 1 * max a 1 = X at h ⊢
  omega

/-- The next 64 KiB page after `va`. -/
theorem alignUp_page (va : Nat) : alignUp va 0x10000 = (va + 65535) / 65536 * 65536 := by
  unfold alignUp
  have : max 0x10000 1 = 65536 := rfl
  rw [this]
  omega

/-! ## Lists -/

theorem chainB_of_pairwise {α : Type} {r : α → α → Bool} :
    ∀ {l : List α}, l.Pairwise (fun a b => r a b = true) → chainB r l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    rw [List.pairwise_cons] at h
    simp only [chainB, Bool.and_eq_true]
    exact ⟨h.1 b (List.mem_cons_self ..), chainB_of_pairwise h.2⟩

/-- `R` relates the lists' elements pairwise, in order. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {l : List α} {r : List β} : R a b → ListRel R l r → ListRel R (a :: l) (b :: r)

theorem mapM_forall₂ {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ListRel (fun a b => f a = .ok b) l r
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | error e => simp [hfa, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [hfa, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [hfa, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .cons hfa (mapM_forall₂ hl)

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, ListRel R l r → ∀ {b}, b ∈ r → ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => by cases hb
  | a :: _, _ :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right h hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall₂_pairwise {α β : Type} {R : α → β → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    (hPQ : ∀ a b a' b', R a b → R a' b' → P a a' → Q b b') :
    ∀ {l : List α} {r : List β}, ListRel R l r → l.Pairwise P → r.Pairwise Q
  | _, _, .nil, _ => .nil
  | _ :: _, _ :: _, .cons hab h, hp => by
    rw [List.pairwise_cons] at hp ⊢
    refine ⟨fun b' hb' => ?_, forall₂_pairwise hPQ h hp.2⟩
    obtain ⟨a', ha', h'⟩ := forall₂_mem_right h hb'
    exact hPQ _ _ _ _ hab h' (hp.1 a' ha')

/-! ## Placing an output section's parts -/

/-- **The parts of an output section** lie from the start address on, each at its file offset,
in increasing, disjoint file ranges up to the end reached. -/
theorem placeParts_spec (sz al : Part → Nat) (start soff out : Nat) (bits tl : Bool) :
    ∀ (ps : List Part) (a : Nat) (acc : Array Slot), start ≤ a →
      a ≤ (placeParts sz al start soff out bits tl a ps acc).1 ∧
      ∃ new : List Slot, (placeParts sz al start soff out bits tl a ps acc).2.toList = acc.toList ++ new ∧
        (∀ x ∈ new, x.bits = bits ∧ soff + (a - start) ≤ x.fo ∧
          x.fo + x.size ≤ soff + ((placeParts sz al start soff out bits tl a ps acc).1 - start)) ∧
        new.Pairwise (fun x y => x.fo + x.size ≤ y.fo)
  | [], a, acc, _ => ⟨Nat.le_refl _, [], by simp [placeParts], by simp, .nil⟩
  | p :: ps, a, acc, ha => by
    have hb := le_alignUp a (al p)
    obtain ⟨h1, new, h2, h3, h4⟩ := placeParts_spec sz al start soff out bits tl ps
      (alignUp a (al p) + sz p)
      (acc.push (Slot.mk p (alignUp a (al p)) (soff + (alignUp a (al p) - start)) (sz p) out bits tl))
      (by omega)
    simp only [placeParts]
    refine ⟨by omega, Slot.mk p (alignUp a (al p)) (soff + (alignUp a (al p) - start)) (sz p) out bits tl
      :: new, by rw [h2]; simp, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨rfl, by simp only; omega, by simp only; omega⟩
      · obtain ⟨e1, e2, e3⟩ := h3 x hx
        exact ⟨e1, by omega, e3⟩
    · refine List.Pairwise.cons (fun y hy => ?_) h4
      have := (h3 y hy).2.1
      simp only
      omega

/-! ## The placement's invariant -/

/-- **The placement's invariant**: the file bytes reached are after the headers and at most the
file offset reached; the open segment's address and file offset advance together; the closed
segments (at most the open kind's number) are in increasing pages before the open one, of
known kinds, with `p_filesz ≤ p_memsz` and their file bytes reached; the placed parts with
file bytes are in increasing, disjoint file ranges after the headers and before the end of
the file bytes reached. -/
structure PInv (st : PSt) : Prop where
  hdr : hdrSize ≤ st.fileEnd
  fe : st.fileEnd ≤ st.off
  so : st.segOff ≤ st.fileEnd
  sv : st.segVa ≤ st.va
  diff : st.va - st.segVa = st.off - st.segOff
  cur : st.cur ≤ 2
  nsegs : st.segs.size ≤ st.cur
  segs : st.segs.toList.Pairwise (fun s t => segBefore s t = true)
  segsOk : ∀ s ∈ st.segs.toList, s.kind ≤ 2 ∧ s.filesz ≤ s.memsz ∧ s.offset + s.filesz ≤ st.fileEnd
  last : ∀ s ∈ st.segs.toList, (s.vaddr + s.memsz + 65535) / 65536 ≤ st.segVa / 65536
  slots : st.slots.toList.Pairwise (fun x y => x.bits = true → y.bits = true → x.fo + x.size ≤ y.fo)
  slotsIn : ∀ x ∈ st.slots.toList, x.bits = true → hdrSize ≤ x.fo ∧ x.fo + x.size ≤ st.fileEnd

theorem PInv_init (base : Nat) : PInv (PSt.init base) where
  hdr := Nat.le_refl _
  fe := Nat.le_refl _
  so := Nat.zero_le _
  sv := by simp [PSt.init]
  diff := by simp [PSt.init]
  cur := by simp [PSt.init]
  nsegs := by simp [PSt.init]
  segs := by simp [PSt.init]
  segsOk := by simp [PSt.init]
  last := by simp [PSt.init]
  slots := by simp [PSt.init]
  slotsIn := by simp [PSt.init]

/-- **A new segment keeps the invariant** (its kind after the open one's). -/
theorem PInv_openSeg {st : PSt} (h : PInv st) {k : Nat} (hk : st.cur ≤ k) (hk2 : k ≤ 2) :
    PInv (st.openSeg k) ∧ (st.openSeg k).cur = k := by
  have hcur : (st.openSeg k).cur = k := by
    unfold PSt.openSeg; split
    · rfl
    · rename_i hne; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne; exact hne.symm
  refine ⟨?_, hcur⟩
  unfold PSt.openSeg
  by_cases hc : k = st.cur
  · subst hc; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]; exact h
  have hc' : (k != st.cur) = true := by simp [hc]
  simp only [hc', ↓reduceIte]
  have hd := h.diff; have hfe := h.fe; have hso := h.so; have hsv := h.sv
  have hpage := le_alignUp st.va 0x10000
  refine { hdr := h.hdr, fe := Nat.le_refl _, so := Nat.le_refl _, sv := Nat.le_refl _,
           diff := by simp, cur := hk2, nsegs := ?_, segs := ?_, segsOk := ?_, last := ?_,
           slots := h.slots, slotsIn := h.slotsIn }
  · simp only [Array.size_push]; have := h.nsegs; omega
  · simp only [Array.toList_push, List.pairwise_append, List.mem_singleton]
    refine ⟨h.segs, List.pairwise_singleton _ _, fun s hs t ht => ?_⟩
    subst ht
    have := h.last s hs
    simp only [segBefore, PSt.seg]
    exact decide_eq_true this
  · simp only [Array.toList_push, List.mem_append, List.mem_singleton]
    rintro s (hs | rfl)
    · exact h.segsOk s hs
    · simp only [PSt.seg]; omega
  · simp only [Array.toList_push, List.mem_append, List.mem_singleton]
    rw [alignUp_page]
    rintro s (hs | rfl)
    · have := h.last s hs
      have : st.segVa / 65536 ≤ ((st.va + 65535) / 65536 * 65536 + st.fileEnd % 65536) / 65536 :=
        Nat.div_le_div_right (by omega)
      omega
    · simp only [PSt.seg]
      omega

/-- **An output section placed keeps the invariant.** -/
theorem PInv_placeIn {st : PSt} (h : PInv st) (sz al : Part → Nat) (nb : Part → Bool)
    (ta : Nat) (s : OSec) :
    PInv (placeIn sz al nb ta st s) ∧ (placeIn sz al nb ta st s).cur = st.cur := by
  refine ⟨?_, rfl⟩
  -- the section's start, file offset, and its parts
  generalize hD : (s.name == ".tdata") = tdata
  generalize hA0 : s.parts.foldl (fun m p => max m (al p)) (if tdata then ta else 1) = a0
  generalize hT : (s.name == ".tbss") = tbss
  generalize hN : (tbss || s.name == ".bss" || s.parts.all nb) = nobits
  have hst : (if tbss = true then alignUp st.tbssVa a0 else alignUp st.va a0) =
      if tbss = true then alignUp st.tbssVa a0 else alignUp st.va a0 := rfl
  generalize hS : (if tbss = true then alignUp st.tbssVa a0 else alignUp st.va a0) = start at hst
  generalize hO : (if tbss = true then st.off else st.off + (start - st.va)) = soff
  obtain ⟨hpa, new, hnew, hin, hpw⟩ := placeParts_spec sz al start soff (st.outs.size + 1) (!nobits)
    (tdata || tbss) s.parts.toList start st.slots (Nat.le_refl _)
  generalize hR : placeParts sz al start soff (st.outs.size + 1) (!nobits) (tdata || tbss) start
    s.parts.toList st.slots = r at hpa hnew hin
  simp only [Nat.sub_self, Nat.add_zero] at hin
  have hd := h.diff; have hfe := h.fe; have hso := h.so; have hsv := h.sv; have hhdr := h.hdr
  unfold placeIn
  simp only [hD, hA0, hT, hN, hS, hO, hR]
  cases tbss with
  | true =>
    have hnb : nobits = true := by rw [← hN]; simp
    subst hnb
    simp only [↓reduceIte]
    refine { hdr := hhdr, fe := hfe, so := hso, sv := hsv, diff := hd, cur := h.cur,
             nsegs := h.nsegs, segs := h.segs, segsOk := h.segsOk, last := h.last, slots := ?_,
             slotsIn := ?_ }
    · rw [hnew, List.pairwise_append]
      refine ⟨h.slots, List.Pairwise.imp_of_mem (fun hx _ _ hb => absurd hb (by rw [(hin _ hx).1]; decide)) hpw,
        fun x _ y hy => ?_⟩
      intro _ hb; rw [(hin y hy).1] at hb; cases hb
    · rw [hnew]
      intro x hx hb
      rcases List.mem_append.1 hx with hx | hx
      · exact h.slotsIn x hx hb
      · rw [(hin x hx).1] at hb; cases hb
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hS hO ⊢
    have hs0 : st.va ≤ start := hS ▸ le_alignUp st.va a0
    refine { hdr := ?_, fe := ?_, so := ?_, sv := ?_, diff := ?_, cur := h.cur,
             nsegs := h.nsegs, segs := h.segs, segsOk := ?_, last := h.last, slots := ?_,
             slotsIn := ?_ }
    · cases nobits <;> simp <;> omega
    · cases nobits <;> simp <;> omega
    · cases nobits <;> simp <;> omega
    · simp only; omega
    · simp only; omega
    · intro x hx
      have := h.segsOk x hx
      refine ⟨this.1, this.2.1, ?_⟩
      cases nobits <;> simp <;> omega
    · rw [hnew, List.pairwise_append]
      refine ⟨h.slots, hpw.imp fun hxy _ _ => hxy, fun x hx y hy hbx hby => ?_⟩
      have := (h.slotsIn x hx hbx).2
      have := (hin y hy).2.1
      omega
    · rw [hnew]
      intro x hx hb
      rcases List.mem_append.1 hx with hx | hx
      · have := h.slotsIn x hx hb
        cases nobits <;> simp <;> omega
      · obtain ⟨e1, e2, e3⟩ := hin x hx
        cases nobits with
        | true => simp only [Bool.not_true] at e1; rw [e1] at hb; cases hb
        | false => simp; omega

/-- **The placement keeps the invariant** over output sections sorted by kind. -/
theorem PInv_foldl (sz al : Part → Nat) (nb : Part → Bool) (ta : Nat) :
    ∀ (l : List OSec) (st : PSt), PInv st → l.Pairwise (fun s t => s.seg ≤ t.seg) →
      (∀ s ∈ l, st.cur ≤ s.seg ∧ s.seg ≤ 2) → PInv (l.foldl (placeSec sz al nb ta) st)
  | [], _, h, _, _ => h
  | s :: l, st, h, hp, hk => by
    rw [List.pairwise_cons] at hp
    obtain ⟨h1, h2⟩ := PInv_openSeg h (hk s (List.mem_cons_self ..)).1 (hk s (List.mem_cons_self ..)).2
    obtain ⟨h3, h4⟩ := PInv_placeIn h1 sz al nb ta s
    refine PInv_foldl sz al nb ta l _ h3 hp.2 fun t ht => ⟨?_, (hk t (List.mem_cons_of_mem _ ht)).2⟩
    show (placeIn sz al nb ta (st.openSeg s.seg) s).cur ≤ t.seg
    rw [h4, h2]
    exact hp.1 t ht

/-! ## The sorted output sections -/

theorem arrOrder_seg (files : Array Obj) (s : OSec) : (arrOrder files s).seg = s.seg := by
  unfold arrOrder; split <;> rfl

theorem pairwise_seg_const {l : List OSec} {k : Nat} (h : ∀ s ∈ l, s.seg = k) :
    l.Pairwise (fun s t => s.seg ≤ t.seg) := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    refine List.Pairwise.cons (fun b hb => ?_) (ih fun s hs => h s (List.mem_cons_of_mem _ hs))
    rw [h a (List.mem_cons_self ..), h b (List.mem_cons_of_mem _ hb)]
    exact Nat.le_refl _

/-- **The output sections are sorted by kind**, each of a known kind. -/
theorem sortOSecs_seg (files : Array Obj) (osecs : Array OSec) :
    (sortOSecs files osecs).toList.Pairwise (fun s t => s.seg ≤ t.seg) ∧
      ∀ s ∈ (sortOSecs files osecs).toList, s.seg ≤ 2 := by
  have hm : ∀ k s, s ∈ (osecs.toList.filter (·.seg == k)).mergeSort (fun a b => !osecLt b a) →
      s.seg = k := fun k s hs => by
    have := (List.mergeSort_perm _ _).mem_iff.1 hs
    simpa using (List.mem_filter.1 this).2
  unfold sortOSecs
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.pairwise_map, List.mem_map, arrOrder_seg]
  refine ⟨?_, ?_⟩
  · simp only [List.pairwise_append]
    refine ⟨pairwise_seg_const (hm 0), ⟨pairwise_seg_const (hm 1), pairwise_seg_const (hm 2), ?_⟩, ?_⟩
    · intro a ha b hb; rw [hm _ _ ha, hm _ _ hb]; decide
    · intro a ha b hb
      rcases List.mem_append.1 hb with hb | hb <;> rw [hm _ _ ha, hm _ _ hb] <;> decide
  · rintro s ⟨t, ht, rfl⟩
    rw [arrOrder_seg]
    rcases List.mem_append.1 ht with ht | ht
    · rw [hm _ _ ht]; decide
    rcases List.mem_append.1 ht with ht | ht <;> rw [hm _ _ ht] <;> decide

/-- **The layout's placement keeps the invariant.** -/
theorem PInv_layPre (o : Opts) (st : St) (g : GcOut) : PInv (layPre o st g).pst := by
  show PInv ((sortOSecs st.files (layDecide st g).osecs).foldl _ (PSt.init o.base))
  rw [← Array.foldl_toList]
  obtain ⟨hp, hk⟩ := sortOSecs_seg st.files (layDecide st g).osecs
  exact PInv_foldl _ _ _ _ _ _ (PInv_init o.base) hp fun s hs => ⟨Nat.zero_le _, hk s hs⟩

/-! ## The pieces -/

theorem clampTo_size (n : Nat) (b : ByteArray) : (clampTo n b).size ≤ n := by
  unfold clampTo
  split
  · assumption
  · simp only [ByteArray.size_extract]; omega

theorem piece_spec (sl : Slot) (b : ByteArray) (rs : List Rel) :
    (sl.piece b rs).fo = sl.fo ∧ (sl.piece b rs).bytes.size ≤ sl.size :=
  ⟨rfl, clampTo_size _ _⟩

theorem inputPiece_some {L : Lay} {o : Opts} {st : St} {g : GcOut} {sl : Slot} {fi si : Nat}
    {p : Piece} (h : L.inputPiece o st g sl fi si = .ok (some p)) : ∃ b rs, p = sl.piece b rs := by
  unfold Lay.inputPiece at h
  dsimp only at h
  split at h
  · simp [pure, Except.pure] at h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      exact ⟨_, _, h.symm⟩

/-- **A slot's piece** is at the slot's file offset, at most its size, for a slot with file
bytes. -/
theorem slotPiece_some {L : Lay} {o : Opts} {st : St} {g : GcOut} {got : ByteArray}
    {eh : ByteArray × Array Rel} {hdr : ByteArray} {sl : Slot} {p : Piece}
    (h : L.slotPiece o st g got eh hdr sl = .ok (some p)) :
    sl.bits = true ∧ p.fo = sl.fo ∧ p.bytes.size ≤ sl.size := by
  unfold Lay.slotPiece at h
  cases hb : sl.bits
  · simp [hb, pure, Except.pure] at h
  simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨rfl, ?_⟩
  have : ∃ b rs, p = sl.piece b rs := by
    split at h
    · exact inputPiece_some h
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
         exact ⟨_, _, h.symm⟩)
      | simp [pure, Except.pure] at h
  obtain ⟨b, rs, rfl⟩ := this
  exact piece_spec sl b rs

/-- **The pieces are in increasing, disjoint file ranges**, each in a slot with file bytes. -/
theorem pieces_pairwise {L : Lay} {o : Opts} {st : St} {g : GcOut} {ps : List Piece}
    (h : L.pieces o st g = .ok ps)
    (hs : L.pst.slots.toList.Pairwise (fun x y => x.bits = true → y.bits = true → x.fo + x.size ≤ y.fo)) :
    ps.Pairwise (fun p q => p.fo + p.bytes.size ≤ q.fo) ∧
      ∀ p ∈ ps, ∃ x ∈ L.pst.slots.toList, x.bits = true ∧ p.fo = x.fo ∧ p.bytes.size ≤ x.size := by
  unfold Lay.pieces at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i eh _
  split at h
  · cases h
  rename_i qs hq
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hf := mapM_forall₂ hq
  refine ⟨?_, fun p hp => ?_⟩
  · rw [List.pairwise_filterMap]
    refine forall₂_pairwise (fun a b a' b' hab hab' hp => ?_) hf hs
    intro p hp q hq
    simp only [id_eq] at hp hq
    subst hp hq
    obtain ⟨b1, f1, s1⟩ := slotPiece_some hab
    obtain ⟨b2, f2, -⟩ := slotPiece_some hab'
    have := hp b1 b2
    omega
  · obtain ⟨op, hop, hpo⟩ := List.mem_filterMap.1 hp
    simp only [id_eq] at hpo
    subst hpo
    obtain ⟨x, hx, hxp⟩ := forall₂_mem_right hf hop
    exact ⟨x, hx, slotPiece_some hxp⟩

/-! ## The plan -/

/-- **A plan `layout` returns** is its placement's: segments, pieces, size. -/
theorem layout_eq {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (h : layout o st g = .ok (pl, m)) :
    ∃ ps, (layPre o st g).pieces o st g = .ok ps ∧ pl.segs = (layPre o st g).segs ∧
      pl.pieces = ps ∧ pl.size = (layPre o st g).pst.fileEnd := by
  unfold layout at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i ps hps
  split at h
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨ps, hps, rfl, rfl, rfl⟩

/-- **The planner meets its plan's conditions**: a plan `layout` returns satisfies `Plan.okB`
(so `assemble` never rejects it). -/
theorem layout_okB {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (h : layout o st g = .ok (pl, m)) : pl.okB = true := by
  obtain ⟨ps, hps, hsegs, hpcs, hsize⟩ := layout_eq h
  have hi := PInv_layPre o st g
  obtain ⟨hpw, hin⟩ := pieces_pairwise hps hi.slots
  have hsegs' : pl.segs = (layPre o st g).pst.segs.toList ++ [(layPre o st g).pst.seg] := by
    rw [hsegs]; exact Array.toList_push ..
  generalize (layPre o st g).pst = P at hi hin hsize hsegs'
  have hd := hi.diff; have hfe := hi.fe; have hso := hi.so; have hsv := hi.sv
  have hlen : pl.segs.length ≤ 3 := by
    rw [hsegs', List.length_append, Array.length_toList]; have := hi.nsegs; have := hi.cur
    simp; omega
  unfold Plan.okB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨?_, fun s hs => ?_⟩, ?_⟩, fun p hp => ?_⟩
  · apply chainB_of_pairwise
    rw [hsegs', List.pairwise_append]
    refine ⟨hi.segs, List.pairwise_singleton _ _, fun s hs t ht => ?_⟩
    rw [List.mem_singleton] at ht; subst ht
    simp only [segBefore, PSt.seg]
    exact decide_eq_true (hi.last s hs)
  · rw [hsegs', List.mem_append, List.mem_singleton] at hs
    rw [hsize]
    rcases hs with hs | rfl
    · have := hi.segsOk s hs
      exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩
    · simp only [PSt.seg]; have := hi.cur; omega
  · apply chainB_of_pairwise
    have hsorted : pl.sorted = pl.pieces := by
      unfold Plan.sorted
      exact List.mergeSort_of_pairwise (hpcs ▸ hpw.imp fun h => by simp; omega)
    rw [hsorted, hpcs]
    exact hpw.imp fun h => by simp only [pieceBefore, decide_eq_true_eq]; exact h
  · rw [hpcs] at hp
    obtain ⟨x, hx, hb, hfo, -⟩ := hin p hp
    have := (hi.slotsIn x hx hb).1
    unfold Plan.hdrEnd hdrSize at *
    omega

/-- **The image of `layout`'s plan**: `assemble` builds it whenever the body can be built. -/
theorem assemble_layout {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (h : layout o st g = .ok (pl, m)) {body : ByteArray}
    (hb : buildBody pl.size pl.sorted = .ok body) :
    assemble pl = .ok { entry := pl.entry, phs := pl.phdrs, body, secs := pl.secs, syms := pl.syms } := by
  unfold assemble
  simp only [layout_okB h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, hb,
    pure, Except.pure]

/-! ## Non-vacuity

A link of one object: a 4-byte `.text` section (`SHF_ALLOC | SHF_EXECINSTR`) holding `_start`. -/

/-- The object. -/
def tinyObj : Obj :=
  { name := "t.o", member := "t.o", data := ⟨#[0x1f, 0x20, 0x03, 0xd5]⟩,
    secs := #[default, { name := ".text", type := 1, flags := 6, off := 0, size := 4, link := 0,
                         info := 0, align := 4, entsize := 0 }],
    syms := #[default, { name := "_start", value := 0, size := 4, bind := 1, type := 2, shndx := 1 }],
    firstGlobal := 1, relaOf := #[none, none] }

/-- The resolved inputs: `_start` defined by the object. -/
def tinySt : St :=
  { files := #[tinyObj], disc := #[{}], syms := ({} : Std.HashMap String Def).insert "_start" (.defd 0 1 false) }

/-- Both sections live (the null one is not linked; it has no flags). -/
def tinyGc : GcOut := { live := #[#[false, true]], eh := #[#[]] }

theorem tinyLayout_ok : (layout {} tinySt tinyGc).toBool = true := by native_decide

/-- **`layout_okB`'s premise holds**: the tiny link's layout succeeds; its plan meets
`Plan.okB`. -/
theorem tinyLayout_okB : ∃ pl m, layout {} tinySt tinyGc = .ok (pl, m) ∧ pl.okB = true := by
  have h := tinyLayout_ok
  cases hl : layout {} tinySt tinyGc with
  | error e => rw [hl] at h; cases h
  | ok r => exact ⟨r.1, r.2, rfl, layout_okB (m := r.2) hl⟩

end Link.Ld

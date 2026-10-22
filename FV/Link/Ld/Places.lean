import FV.Link.Ld.BodyTotal

/-! # The places of `lean-ld`'s layout (A1c, #409)

The layout's maps from parts to places (`slotMaps`: an input section's address and output
section index, the synthesized parts' and the common symbols' addresses) are the placed parts'
(`Slot`s):

* `slotMaps_sec`: an input section with a slot has the address of one of its slots;
* `slotMaps_part`, `slotMaps_common`: likewise the GOT, `.eh_frame`, `.eh_frame_hdr` and
  common symbols (a map entry is a slot's address).

And the placement's bounds (`PB`): every placed part ends below the address reached plus the
`.tbss` allowance `K` (`.tbss` takes no address space), the ones not thread-local start at the
base or later; the address reached is at most the base, the headers and, per output section,
its parts' alignments and sizes (`secBound`) and two 64 KiB pages (`placeBound`):
**`layPre_bound`**.
-/

namespace Link.Ld

/-! ## The maps -/

abbrev SlotMaps := Array (Array Nat) × Array (Array Nat) × Std.HashMap String Nat × Std.HashMap (Nat × Nat) Nat

theorem getElem!_eq_opt {α : Type} [Inhabited α] (a : Array α) (i : Nat) : a[i]! = a[i]?.getD default := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

/-- An entry of an array of arrays after `modify f (·.set! i v)`. -/
theorem modify_set_getElem! (a : Array (Array Nat)) (f i f' i' v : Nat) :
    (a.modify f (·.set! i v))[f']![i']! =
      if f = f' ∧ i = i' ∧ ∃ h : f < a.size, i < a[f].size then v else a[f']![i']! := by
  simp only [getElem!_eq_opt, Array.getElem?_modify, Array.set!_eq_setIfInBounds]
  by_cases hf : f = f'
  · subst hf
    simp only [true_and, ↓reduceIte]
    cases ha : a[f]? with
    | none =>
      have : ¬ f < a.size := fun h => by rw [Array.getElem?_eq_getElem h] at ha; cases ha
      simp [this]
    | some row =>
      obtain ⟨hf, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
      simp only [Option.map_some, Option.getD_some, Array.getElem?_setIfInBounds]
      by_cases hi : i = i'
      · subst hi; by_cases hr : i < a[f].size <;> simp [hr, hf]
      · simp [hi]
  · simp [hf]

/-- The sizes of the maps' arrays are the files' and their sections'. -/
def SizesOk (files : Array Obj) (m : SlotMaps) : Prop :=
  m.1.size = files.size ∧ m.2.1.size = files.size ∧
    ∀ f (h : f < files.size), (m.1[f]!).size = files[f].secs.size ∧ (m.2.1[f]!).size = files[f].secs.size

theorem modify_set_size (a : Array (Array Nat)) (f i v : Nat) : (a.modify f (·.set! i v)).size = a.size :=
  Array.size_modify ..

theorem modify_set_row (a : Array (Array Nat)) (f i v f' : Nat) :
    ((a.modify f (·.set! i v))[f']!).size = (a[f']!).size := by
  simp only [getElem!_eq_opt, Array.getElem?_modify]
  split
  · cases a[f']? <;> simp
  · rfl

theorem slotStep_sizes {files : Array Obj} {m : SlotMaps} (h : SizesOk files m) (sl : Slot) :
    SizesOk files (slotStep m sl) := by
  unfold slotStep
  split
  · refine ⟨by rw [modify_set_size]; exact h.1, by rw [modify_set_size]; exact h.2.1, fun f hf => ?_⟩
    rw [modify_set_row, modify_set_row]; exact h.2.2 f hf
  all_goals exact h

/-- The fold over parts other than input section `(f, i)` keeps its entries. -/
theorem slotMaps_keep (f i : Nat) : ∀ (l : List Slot) (m : SlotMaps),
    (∀ x ∈ l, x.part ≠ .input (f, i)) →
    (l.foldl slotStep m).1[f]![i]! = m.1[f]![i]! ∧ (l.foldl slotStep m).2.1[f]![i]! = m.2.1[f]![i]!
  | [], _, _ => ⟨rfl, rfl⟩
  | x :: l, m, h => by
    obtain ⟨h1, h2⟩ := slotMaps_keep f i l (slotStep m x) fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.foldl_cons, h1, h2]
    have hx := h x (List.mem_cons_self ..)
    unfold slotStep
    split
    · rename_i f' i' hp
      rw [hp] at hx
      simp only [modify_set_getElem!]
      have : ¬ (f' = f ∧ i' = i) := fun ⟨e1, e2⟩ => hx (by rw [e1, e2])
      constructor <;> (rw [if_neg (fun ⟨e1, e2, _⟩ => this ⟨e1, e2⟩)])
    all_goals exact ⟨rfl, rfl⟩

/-- **An input section with a slot** has the address and output index of one of its slots. -/
theorem slotMaps_sec_aux {files : Array Obj} {f i : Nat} (hf : f < files.size) (hi : i < files[f].secs.size) :
    ∀ (l : List Slot) (m : SlotMaps), SizesOk files m → (∃ x ∈ l, x.part = .input (f, i)) →
      ∃ x ∈ l, x.part = .input (f, i) ∧ (l.foldl slotStep m).1[f]![i]! = x.addr ∧
        (l.foldl slotStep m).2.1[f]![i]! = x.out
  | [], _, _, ⟨_, hx, _⟩ => by cases hx
  | x :: l, m, hm, hex => by
    by_cases hl : ∃ y ∈ l, y.part = .input (f, i)
    · obtain ⟨y, hy, h1, h2, h3⟩ := slotMaps_sec_aux hf hi l (slotStep m x) (slotStep_sizes hm x) hl
      exact ⟨y, List.mem_cons_of_mem _ hy, h1, h2, h3⟩
    · have hx : x.part = .input (f, i) := by
        obtain ⟨y, hy, hp⟩ := hex
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hp
        · exact absurd ⟨y, hy, hp⟩ hl
      obtain ⟨h1, h2⟩ := slotMaps_keep f i l (slotStep m x) fun y hy hp => hl ⟨y, hy, hp⟩
      refine ⟨x, List.mem_cons_self .., hx, ?_, ?_⟩ <;> rw [List.foldl_cons]
      · have hf1 : f < m.1.size := by rw [hm.1]; exact hf
        rw [h1]; unfold slotStep; rw [hx]; simp only
        rw [modify_set_getElem!, if_pos ⟨rfl, rfl, hf1, by
          have := (hm.2.2 f hf).1; rw [getElem!_pos m.1 f hf1] at this; rw [this]; exact hi⟩]
      · have hf2 : f < m.2.1.size := by rw [hm.2.1]; exact hf
        rw [h2]; unfold slotStep; rw [hx]; simp only
        rw [modify_set_getElem!, if_pos ⟨rfl, rfl, hf2, by
          have := (hm.2.2 f hf).2; rw [getElem!_pos m.2.1 f hf2] at this; rw [this]; exact hi⟩]

theorem slotMaps_init_sizes (files : Array Obj) :
    SizesOk files (files.map fun f => Array.replicate f.secs.size 0,
      files.map fun f => Array.replicate f.secs.size 0, {}, {}) := by
  refine ⟨by simp, by simp, fun f hf => ?_⟩
  simp [getElem!_pos, hf]

/-- **An input section with a slot** has the address and output index of one of its slots. -/
theorem slotMaps_sec {files : Array Obj} {slots : Array Slot} {f i : Nat} (hf : f < files.size)
    (hi : i < files[f].secs.size) (hex : ∃ x ∈ slots.toList, x.part = .input (f, i)) :
    ∃ x ∈ slots.toList, x.part = .input (f, i) ∧ (slotMaps files slots).1[f]![i]! = x.addr ∧
      (slotMaps files slots).2.1[f]![i]! = x.out := by
  unfold slotMaps
  rw [← Array.foldl_toList]
  exact slotMaps_sec_aux hf hi _ _ (slotMaps_init_sizes files) hex

/-- **A synthesized part's address** is a slot's. -/
theorem slotMaps_part_aux (k : String) :
    ∀ (l : List Slot) (m : SlotMaps) (a : Nat), (l.foldl slotStep m).2.2.1[k]? = some a →
      m.2.2.1[k]? = some a ∨ ∃ x ∈ l, x.addr = a ∧
        ((k = "got" ∧ x.part = .got) ∨ (k = "eh" ∧ x.part = .eh) ∨ (k = "ehHdr" ∧ x.part = .ehHdr))
  | [], _, _, h => .inl h
  | x :: l, m, a, h => by
    rcases slotMaps_part_aux k l (slotStep m x) a h with h | ⟨y, hy, h1⟩
    · unfold slotStep at h
      split at h
      · exact .inl h
      · exact .inl h
      all_goals
        rename_i hp
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i hk
          simp only [Option.some.injEq] at h
          refine .inr ⟨x, List.mem_cons_self .., h, ?_⟩
          simp only [beq_iff_eq] at hk
          subst hk
          simp [hp]
        · exact .inl h
    · exact .inr ⟨y, List.mem_cons_of_mem _ hy, h1⟩

theorem slotMaps_part {files : Array Obj} {slots : Array Slot} {k : String} {a : Nat}
    (h : (slotMaps files slots).2.2.1[k]? = some a) :
    ∃ x ∈ slots.toList, x.addr = a ∧
      ((k = "got" ∧ x.part = .got) ∨ (k = "eh" ∧ x.part = .eh) ∨ (k = "ehHdr" ∧ x.part = .ehHdr)) := by
  unfold slotMaps at h
  rw [← Array.foldl_toList] at h
  rcases slotMaps_part_aux k _ _ a h with h | h
  · simp at h
  · exact h

/-- **A common symbol's address** is a slot's. -/
theorem slotMaps_common_aux (fk : Nat × Nat) :
    ∀ (l : List Slot) (m : SlotMaps) (a : Nat), (l.foldl slotStep m).2.2.2[fk]? = some a →
      m.2.2.2[fk]? = some a ∨ ∃ x ∈ l, x.addr = a ∧ x.part = .common fk.1 fk.2
  | [], _, _, h => .inl h
  | x :: l, m, a, h => by
    rcases slotMaps_common_aux fk l (slotStep m x) a h with h' | ⟨y, hy, h1⟩
    · cases hp : x.part with
      | common f k =>
        simp only [slotStep, hp, Std.HashMap.getElem?_insert] at h'
        split at h'
        · rename_i hk
          simp only [Option.some.injEq] at h'
          simp only [beq_iff_eq] at hk
          subst hk
          exact .inr ⟨x, List.mem_cons_self .., h', hp⟩
        · exact .inl h'
      | input fs => simp only [slotStep, hp] at h'; exact .inl h'
      | got => simp only [slotStep, hp] at h'; exact .inl h'
      | eh => simp only [slotStep, hp] at h'; exact .inl h'
      | ehHdr => simp only [slotStep, hp] at h'; exact .inl h'
    · exact .inr ⟨y, List.mem_cons_of_mem _ hy, h1⟩

theorem slotMaps_common {files : Array Obj} {slots : Array Slot} {fk : Nat × Nat} {a : Nat}
    (h : (slotMaps files slots).2.2.2[fk]? = some a) :
    ∃ x ∈ slots.toList, x.addr = a ∧ x.part = .common fk.1 fk.2 := by
  unfold slotMaps at h
  rw [← Array.foldl_toList] at h
  rcases slotMaps_common_aux fk _ _ a h with h | h
  · simp at h
  · exact h

end Link.Ld

namespace Link.Ld

/-! ## The placement's bounds -/

/-- A bound on an output section's extent: its start's alignment and its parts' alignments and
sizes. -/
def secBound (sz al : Part → Nat) (ta : Nat) (s : OSec) : Nat :=
  (if s.name == ".tdata" then ta else 1) + 2 * (s.parts.toList.map fun p => al p + sz p).sum

/-- **A bound on the placement's extent**: every output section's `secBound` and two 64 KiB
pages (a new segment's page and file offset). -/
def placeBound (sz al : Part → Nat) (ta : Nat) (l : List OSec) : Nat :=
  (l.map fun s => secBound sz al ta s + 2 * 65536).sum

theorem foldl_max_le (al : Part → Nat) : ∀ (ps : List Part) (m : Nat),
    ps.foldl (fun m p => max m (al p)) m ≤ m + (ps.map al).sum
  | [], m => by simp
  | p :: ps, m => by
    have := foldl_max_le al ps (max m (al p))
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    omega

theorem sum_le_sum_add {l : List Part} (f g : Part → Nat) :
    (l.map f).sum ≤ (l.map fun p => f p + g p).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, List.sum_cons]; omega

/-- **The placement's bounds** (`K`: the `.tbss` allowance): every placed part and output
section ends below the address reached plus `K`; the parts not thread-local start at the base
or later; the address reached is at least the base and the `.tbss` start. -/
structure PB (base K : Nat) (st : PSt) : Prop where
  va : base ≤ st.va
  tbss : st.tbssVa ≤ st.va
  slots : ∀ x ∈ st.slots.toList, x.addr + x.size ≤ st.va + K ∧ (x.tls = false → base ≤ x.addr)
  outs : ∀ s ∈ st.outs.toList, s.addr + s.size ≤ st.va + K

theorem PB_init (base K : Nat) : PB base K (PSt.init base) where
  va := by simp [PSt.init]
  tbss := by simp [PSt.init]
  slots := by simp [PSt.init]
  outs := by simp [PSt.init]

theorem PB_openSeg {base K : Nat} {st : PSt} (h : PB base K st) (k : Nat) :
    PB base K (st.openSeg k) ∧ (st.openSeg k).va ≤ st.va + 2 * 65536 := by
  unfold PSt.openSeg
  split
  · have hp := le_alignUp st.va 0x10000
    have hq := alignUp_le st.va 0x10000
    have := Nat.mod_lt st.fileEnd (show 0 < 0x10000 by decide)
    refine ⟨{ va := ?_, tbss := ?_, slots := fun x hx => ?_, outs := fun s hs => ?_ }, ?_⟩
    · have := h.va; simp only; omega
    · have := h.tbss; simp only; omega
    · have := h.slots x hx; simp only; exact ⟨by have := this.1; omega, this.2⟩
    · have := h.outs s hs; simp only; omega
    · simp only; omega
  · exact ⟨h, by omega⟩

theorem PB_placeIn {base K : Nat} {st : PSt} (h : PB base K st) (sz al : Part → Nat)
    (nb : Part → Bool) (ta : Nat) (s : OSec) (hK : s.name = ".tbss" → secBound sz al ta s ≤ K) :
    PB base K (placeIn sz al nb ta st s) ∧ (placeIn sz al nb ta st s).va ≤ st.va + secBound sz al ta s := by
  have hb := placeParts_bound sz al
  have hm := placeParts_mem sz al
  have hA : s.parts.foldl (fun m p => max m (al p)) (if s.name == ".tdata" then ta else 1) ≤
      (if s.name == ".tdata" then ta else 1) + (s.parts.toList.map al).sum := by
    rw [← Array.foldl_toList]; exact foldl_max_le al _ _
  have hS := sum_le_sum_add (l := s.parts.toList) al sz
  generalize hD : (s.name == ".tdata") = tdata at hA ⊢
  generalize hA0 : s.parts.foldl (fun m p => max m (al p)) (if tdata then ta else 1) = a0 at hA ⊢
  generalize hT : (s.name == ".tbss") = tbss
  generalize hN : (tbss || s.name == ".bss" || s.parts.all nb) = nobits
  have hsec : secBound sz al ta s = (if tdata then ta else 1) + 2 * (s.parts.toList.map fun p => al p + sz p).sum := by
    unfold secBound; rw [hD]
  generalize hS0 : (if tbss = true then alignUp st.tbssVa a0 else alignUp st.va a0) = start
  generalize hO : (if tbss = true then st.off else st.off + (start - st.va)) = soff
  have hpb := hb start soff (st.outs.size + 1) (!nobits) (tdata || tbss) s.parts.toList start st.slots
  have hpe := placeParts_mem.placeParts_end sz al start soff (st.outs.size + 1) (!nobits) (tdata || tbss)
    s.parts.toList start st.slots
  have hpm := hm start soff (st.outs.size + 1) (!nobits) (tdata || tbss) s.parts.toList start st.slots
  generalize hR : placeParts sz al start soff (st.outs.size + 1) (!nobits) (tdata || tbss) start
    s.parts.toList st.slots = r at hpb hpe hpm
  unfold placeIn
  simp only [hD, hA0, hT, hN, hS0, hO, hR]
  have hva := h.va; have htb := h.tbss
  cases tbss with
  | true =>
    have htd : tdata = false := by
      cases tdata
      · rfl
      · simp only [beq_iff_eq] at hD hT; rw [hD] at hT; exact absurd hT (by decide)
    subst htd
    simp only [↓reduceIte, Bool.false_eq_true] at hS0 hsec hA ⊢
    have hK' := hK (by simpa using hT)
    have h1 := le_alignUp st.tbssVa a0
    have h2 := alignUp_le st.tbssVa a0
    refine ⟨{ va := hva, tbss := ?_, slots := fun x hx => ?_, outs := fun o ho => ?_ }, by omega⟩
    · exact htb
    · rcases hpm x hx with hx | ⟨-, h3, -, -, h5, -, -, h8⟩
      · exact h.slots x hx
      · refine ⟨by simp only; rw [hsec] at hK'; omega, fun h0 => ?_⟩
        rw [h3] at h0; simp at h0
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · exact h.outs o ho
      · simp only; rw [hsec] at hK'; omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hS0 ⊢
    have h1 := le_alignUp st.va a0
    have h2 := alignUp_le st.va a0
    have hinit : (if tdata = true then ta else 1) ≤ secBound sz al ta s := by rw [hsec]; omega
    refine ⟨{ va := ?_, tbss := ?_, slots := fun x hx => ?_, outs := fun o ho => ?_ }, by rw [hsec]; omega⟩
    · simp only; omega
    · cases tdata <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · rcases hpm x hx with hx | ⟨-, -, -, -, h5, -, -, h8⟩
      · have := h.slots x hx; simp only; exact ⟨by omega, fun h0 => by have := this.2 h0; omega⟩
      · simp only; exact ⟨by omega, fun _ => by omega⟩
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · have := h.outs o ho; simp only; omega
      · simp only; omega

theorem PB_foldl {base K : Nat} (sz al : Part → Nat) (nb : Part → Bool) (ta : Nat) :
    ∀ (l : List OSec) (st : PSt), PB base K st → (∀ s ∈ l, s.name = ".tbss" → secBound sz al ta s ≤ K) →
      PB base K (l.foldl (placeSec sz al nb ta) st) ∧
        (l.foldl (placeSec sz al nb ta) st).va ≤ st.va + placeBound sz al ta l
  | [], _, h, _ => ⟨h, by simp [placeBound]⟩
  | s :: l, st, h, hK => by
    obtain ⟨h1, e1⟩ := PB_openSeg h s.seg
    obtain ⟨h2, e2⟩ := PB_placeIn h1 sz al nb ta s (hK s (List.mem_cons_self ..))
    obtain ⟨h3, e3⟩ := PB_foldl sz al nb ta l _ h2 fun t ht => hK t (List.mem_cons_of_mem _ ht)
    refine ⟨h3, ?_⟩
    simp only [List.foldl_cons, placeBound, List.map_cons, List.sum_cons] at e3 ⊢
    have : placeSec sz al nb ta st s = placeIn sz al nb ta (st.openSeg s.seg) s := rfl
    rw [this]
    omega

end Link.Ld

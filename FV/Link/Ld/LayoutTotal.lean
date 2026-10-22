import FV.Link.Ld.LayoutProof

/-! # `lean-ld`'s planner accepts its resolved inputs (A1b, #409)

`layout` (`FV/Link/Ld/Layout.lean`) fails only when a symbol has no value — a reference to a
section `--gc-sections` discarded, an undefined non-weak name that is not linker-defined — or
when the entry is not placed. `layRefsB` decides the absence of both on the layout's decisions
(`layDecide`: the output sections and their parts, the kept `.eh_frame` records, the GOT's
symbols; `sortOSecs`: their order), which read no address:

* `refOkB`: a symbol in a live section or an input `.eh_frame`, absolute, common, undefined
  weak, or a linker-defined name (`synthKnownB`: `__start_X`/`__stop_X` of an output section
  `X`, or one of `synthNames`);
* `entryOkB`: the entry is defined in a live section;
* `layRefsB`: `entryOkB`, and `refOkB` for every GOT symbol, every relocation of a kept
  `.eh_frame` record and every relocation of an input section of an output section.

**`layout_ok`**: `layRefsB o st g = true → ∃ pl m, layout o st g = .ok (pl, m)`. Witness:
`tinyLayRefs` (the one-object link of `FV/Link/Ld/LayoutProof.lean`).
-/

namespace Link.Ld

/-! ## The conditions -/

/-- The linker-defined names `synthFixed` always gives a value. -/
def synthNames : List String :=
  ["__init_array_start", "__init_array_end", "__fini_array_start", "__fini_array_end",
   "__preinit_array_start", "__preinit_array_end", "_end", "end", "__end", "_etext", "etext",
   "__etext", "_edata", "edata", "__bss_start", "__ehdr_start", "__executable_start",
   "_GLOBAL_OFFSET_TABLE_"]

/-- **A linker-defined name with a value** (`names`: the output sections' names). -/
def synthKnownB (names : List String) (n : String) : Bool :=
  if n.startsWith "__start_" then names.contains (n.drop 8).toString
  else if n.startsWith "__stop_" then names.contains (n.drop 7).toString
  else synthNames.contains n

/-- **Symbol `j` of file `fi` has a value**: in a live section or an input `.eh_frame`,
absolute, common, undefined weak, or linker-defined. -/
def refOkB (st : St) (g : GcOut) (names : List String) (fi j : Nat) : Bool :=
  match st.target fi j with
  | .sec t _ _ => (g.live[t.1]?.bind (·[t.2]?)).getD false || (g.eh[t.1]!.findIdx? (·.sec == t.2)).isSome
  | .undef n w => w || synthKnownB names n
  | _ => true

/-- **The entry is defined in a live section.** -/
def entryOkB (o : Opts) (st : St) (g : GcOut) : Bool :=
  match st.syms[o.entry]? with
  | some (.defd f k _) =>
    let sy := st.files[f]!.syms[k]!
    sy.inSec && g.live[f]![sy.shndx]!
  | _ => false

/-- The relocations of a kept `.eh_frame` record. -/
def ehRelas (g : GcOut) (e : EhOut) : Array Rela :=
  match g.eh[e.file]![e.ei]? with
  | some es => es.relasIn e.piece.off (e.piece.off + e.piece.size)
  | none => #[]

/-- **The layout's references resolve**: the entry is placed; every GOT symbol, every
relocation of a kept `.eh_frame` record and of an input section in an output section has a
value. Decided on the layout's decisions (`layDecide`, `sortOSecs`), no address. -/
def layRefsB (o : Opts) (st : St) (g : GcOut) : Bool :=
  let D := layDecide st g
  let sorted := sortOSecs st.files D.osecs
  let names := sorted.toList.map (·.name)
  entryOkB o st g &&
  D.gotSyms.all (fun x => refOkB st g names x.1 x.2) &&
  D.ehs.all (fun e => (ehRelas g e).all fun r => refOkB st g names e.file r.sym) &&
  sorted.all fun s => s.parts.all fun p => match p with
    | .input (fi, si) => (st.files[fi]!.relas si).all fun r => refOkB st g names fi r.sym
    | _ => true

/-! ## Monadic folds that never fail -/

theorem list_foldlM_ok {α β ε : Type} {f : β → α → Except ε β} :
    ∀ {l : List α} (init : β), (∀ b, ∀ a ∈ l, ∃ b', f b a = .ok b') → ∃ b', l.foldlM f init = .ok b'
  | [], init, _ => ⟨init, rfl⟩
  | a :: l, init, h => by
    obtain ⟨b1, h1⟩ := h init a (List.mem_cons_self ..)
    obtain ⟨b2, h2⟩ := list_foldlM_ok (l := l) b1 fun b x hx => h b x (List.mem_cons_of_mem _ hx)
    exact ⟨b2, by rw [List.foldlM_cons, h1]; exact h2⟩

theorem array_foldlM_ok {α β ε : Type} {f : β → α → Except ε β} {l : Array α} (init : β)
    (h : ∀ b, ∀ a ∈ l, ∃ b', f b a = .ok b') : ∃ b', l.foldlM f init = .ok b' := by
  rw [← Array.foldlM_toList]
  exact list_foldlM_ok init fun b a ha => h b a (Array.mem_toList_iff.1 ha)

theorem list_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ bs, l.mapM f = .ok bs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := list_mapM_ok (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs, bind, Except.bind, pure, Except.pure]⟩

/-! ## The placement's output sections and parts -/

theorem alignUp_le (n a : Nat) : alignUp n a ≤ n + a := by
  unfold alignUp
  have h := Nat.div_mul_le_self (n + max a 1 - 1) (max a 1)
  have : max a 1 - 1 ≤ a := by omega
  omega

theorem alignUp_dvd (n a : Nat) : alignUp n a % max a 1 = 0 := by
  unfold alignUp; exact Nat.mul_mod_left _ _

/-- **The parts placed** lie between the start and the end reached, aligned, at their sizes,
with the section's output index and flags. -/
theorem placeParts_mem (sz al : Part → Nat) (start soff out : Nat) (bits tl : Bool) :
    ∀ (ps : List Part) (a : Nat) (acc : Array Slot) (x : Slot),
      x ∈ (placeParts sz al start soff out bits tl a ps acc).2.toList → x ∈ acc.toList ∨
        (x.part ∈ ps ∧ x.tls = tl ∧ x.out = out ∧ x.bits = bits ∧ a ≤ x.addr ∧
          x.addr % max (al x.part) 1 = 0 ∧ x.size = sz x.part ∧
          x.addr + x.size ≤ (placeParts sz al start soff out bits tl a ps acc).1)
  | [], _, _, _, h => .inl h
  | p :: ps, a, acc, x, h => by
    have hb := le_alignUp a (al p)
    have he := placeParts_end sz al start soff out bits tl ps (alignUp a (al p) + sz p)
      (acc.push (Slot.mk p (alignUp a (al p)) (soff + (alignUp a (al p) - start)) (sz p) out bits tl))
    rcases placeParts_mem sz al start soff out bits tl ps _ _ x h with h | h
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact .inl h
      · refine .inr ⟨List.mem_cons_self .., rfl, rfl, rfl, hb, alignUp_dvd _ _, rfl, ?_⟩
        simp only [placeParts]; exact he
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
      exact .inr ⟨List.mem_cons_of_mem _ h1, h2, h3, h4, by omega, h6, h7, h8⟩
where
  placeParts_end (sz al : Part → Nat) (start soff out : Nat) (bits tl : Bool) :
      ∀ (ps : List Part) (a : Nat) (acc : Array Slot), a ≤ (placeParts sz al start soff out bits tl a ps acc).1
    | [], _, _ => Nat.le_refl _
    | p :: ps, a, acc => by
      have := placeParts_end sz al start soff out bits tl ps (alignUp a (al p) + sz p)
        (acc.push (Slot.mk p (alignUp a (al p)) (soff + (alignUp a (al p) - start)) (sz p) out bits tl))
      have := le_alignUp a (al p)
      simp only [placeParts]; omega

/-- The end reached: at most the start and every part's alignment and size. -/
theorem placeParts_bound (sz al : Part → Nat) (start soff out : Nat) (bits tl : Bool) :
    ∀ (ps : List Part) (a : Nat) (acc : Array Slot),
      (placeParts sz al start soff out bits tl a ps acc).1 ≤ a + (ps.map fun p => al p + sz p).sum
  | [], _, _ => by simp [placeParts]
  | p :: ps, a, acc => by
    have := placeParts_bound sz al start soff out bits tl ps (alignUp a (al p) + sz p)
      (acc.push (Slot.mk p (alignUp a (al p)) (soff + (alignUp a (al p) - start)) (sz p) out bits tl))
    have := alignUp_le a (al p)
    simp only [placeParts, List.map_cons, List.sum_cons]; omega

/-- The placement's output sections are the sections placed, in order; its parts are theirs. -/
theorem foldl_placeSec (sz al : Part → Nat) (nb : Part → Bool) (ta : Nat) :
    ∀ (l : List OSec) (st : PSt),
      (l.foldl (placeSec sz al nb ta) st).outs.toList.map (·.name) = st.outs.toList.map (·.name) ++ l.map (·.name) ∧
      ∀ x ∈ (l.foldl (placeSec sz al nb ta) st).slots.toList, x ∈ st.slots.toList ∨ ∃ s ∈ l, x.part ∈ s.parts
  | [], st => by simp
  | s :: l, st => by
    obtain ⟨h1, h2⟩ := foldl_placeSec sz al nb ta l (placeSec sz al nb ta st s)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [List.foldl_cons, h1]
      simp [placeSec, placeIn, PSt.openSeg]
      split <;> simp
    · rcases h2 x hx with h | ⟨t, ht, hp⟩
      · simp only [placeSec, placeIn] at h
        rcases placeParts_mem _ _ _ _ _ _ _ _ _ _ x h with h | h
        · left
          unfold PSt.openSeg at h
          split at h <;> exact h
        · exact .inr ⟨s, List.mem_cons_self .., Array.mem_toList_iff.1 h.1⟩
      · exact .inr ⟨t, List.mem_cons_of_mem _ ht, hp⟩

theorem layPre_outs (o : Opts) (st : St) (g : GcOut) :
    (layPre o st g).pst.outs.toList.map (·.name) = (layPre o st g).sorted.toList.map (·.name) := by
  show ((sortOSecs st.files (layDecide st g).osecs).foldl _ (PSt.init o.base)).outs.toList.map _ = _
  rw [← Array.foldl_toList, (foldl_placeSec _ _ _ _ _ _).1]
  simp [PSt.init]
  rfl

theorem layPre_slots (o : Opts) (st : St) (g : GcOut) :
    ∀ x ∈ (layPre o st g).pst.slots.toList, ∃ s ∈ (layPre o st g).sorted.toList, x.part ∈ s.parts := by
  intro x hx
  have := (foldl_placeSec (LayD.partSize (layDecide st g) st.files) (LayD.partAlign st.files)
    (LayD.partNb st.files) (tlsAlignOf (LayD.partAlign st.files) (sortOSecs st.files (layDecide st g).osecs))
    (sortOSecs st.files (layDecide st g).osecs).toList (PSt.init o.base)).2 x
    (by rw [Array.foldl_toList]; exact hx)
  rcases this with h | h
  · simp [PSt.init] at h
  · exact h

/-! ## Symbol values -/

theorem outRange_some {L : Lay} {n : String} (h : (L.pst.outs.toList.map (·.name)).contains n = true) :
    (L.outRange n).isSome = true := by
  unfold Lay.outRange
  simp only [Option.isSome_map]
  rw [List.contains_iff_mem, List.mem_map] at h
  obtain ⟨s, hs, rfl⟩ := h
  rw [Option.isSome_iff_exists]
  rw [← Array.find?_toList]
  exact Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨s, hs, by simp⟩)

theorem synth_some {L : Lay} {o : Opts} {n : String}
    (h : synthKnownB (L.pst.outs.toList.map (·.name)) n = true) : (L.synth o n).isSome = true := by
  unfold synthKnownB at h
  unfold Lay.synth
  split
  · simp only [Option.isSome_map]; rename_i h1; simp only [h1, ↓reduceIte] at h; exact outRange_some h
  split
  · simp only [Option.isSome_map]; rename_i h1 h2; simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
    exact outRange_some h
  rename_i h1 h2
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, synthNames, List.contains_iff_mem, List.mem_cons,
    List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp [Lay.synthFixed]

theorem value_ok {L : Lay} {o : Opts} {st : St} {g : GcOut} {fi j : Nat}
    (h : refOkB st g (L.pst.outs.toList.map (·.name)) fi j = true) :
    ∃ v, L.value o st g fi j = .ok v := by
  unfold refOkB at h
  unfold Lay.value
  split
  · rename_i t x tl ht
    rw [ht] at h
    simp only [Bool.or_eq_true] at h
    split
    · exact ⟨_, rfl⟩
    · rename_i hl
      rcases h with h | h
      · exact absurd h hl
      · split
        · dsimp only
          split
          · split
            · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩
          · exact ⟨_, rfl⟩
        · rename_i hn; rw [hn] at h; cases h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i n w ht
    rw [ht] at h
    simp only [Bool.or_eq_true] at h
    split
    · exact ⟨_, rfl⟩
    · rename_i hs
      rcases h with h | h
      · simp [h, pure, Except.pure]
      · have := synth_some (o := o) h
        rw [hs] at this; cases this

theorem relIn_ok {L : Lay} {o : Opts} {st : St} {g : GcOut} {fi : Nat} {r : Rela} {P : Nat}
    (h : refOkB st g (L.pst.outs.toList.map (·.name)) fi r.sym = true) :
    ∃ ri, L.relIn o st g fi r P = .ok ri := by
  obtain ⟨v, hv⟩ := value_ok (o := o) h
  unfold Lay.relIn
  simp only [hv, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

/-! ## The layout succeeds -/

theorem gotBytes_ok {L : Lay} {o : Opts} {st : St} {g : GcOut}
    (h : ∀ x ∈ L.gotSyms, refOkB st g (L.pst.outs.toList.map (·.name)) x.1 x.2 = true) :
    ∃ b, L.gotBytes o st g = .ok b := by
  unfold Lay.gotBytes
  refine array_foldlM_ok _ fun b x hx => ?_
  obtain ⟨v, hv⟩ := value_ok (o := o) (h x hx)
  simp only [hv, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

theorem ehOut_ok {L : Lay} {o : Opts} {st : St} {g : GcOut}
    (h : ∀ e ∈ L.ehs, ∀ r ∈ ehRelas g e, refOkB st g (L.pst.outs.toList.map (·.name)) e.file r.sym = true) :
    ∃ b, L.ehOut o st g = .ok b := by
  unfold Lay.ehOut
  refine array_foldlM_ok _ fun acc e he => ?_
  unfold Lay.ehRec
  split
  · exact ⟨_, rfl⟩
  · rename_i es hes
    have hr : ∀ r ∈ es.relasIn e.piece.off (e.piece.off + e.piece.size),
        refOkB st g (L.pst.outs.toList.map (·.name)) e.file r.sym = true := fun r hr =>
      h e he r (by unfold ehRelas; rw [hes]; exact hr)
    obtain ⟨rt, hrt⟩ := array_foldlM_ok (f := L.ehRel o st g e) (acc.2.1, acc.2.2) fun b r hrm => by
      obtain ⟨ri, hri⟩ := relIn_ok (o := o) (P := L.ehAddr + e.out + (r.off - e.piece.off)) (hr r hrm)
      obtain ⟨v, hv⟩ := value_ok (o := o) (hr r hrm)
      unfold Lay.ehRel
      simp only [hri, bind, Except.bind]
      split
      · simp only [hv]; exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    simp only [hrt, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩

theorem list_mapM_ne_error {α β ε : Type} {f : α → Except ε β} {l : List α} {e : ε}
    (h : ∀ a ∈ l, ∃ b, f a = .ok b) : l.mapM f ≠ .error e := by
  obtain ⟨bs, hbs⟩ := list_mapM_ok h
  rw [hbs]; exact fun h => by cases h

theorem inputPiece_ok {L : Lay} {o : Opts} {st : St} {g : GcOut} {sl : Slot} {fi si : Nat}
    (h : ∀ r ∈ st.files[fi]!.relas si, refOkB st g (L.pst.outs.toList.map (·.name)) fi r.sym = true) :
    ∃ p, L.inputPiece o st g sl fi si = .ok p := by
  unfold Lay.inputPiece
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · simp only [bind, Except.bind]
    split
    · rename_i err herr
      refine absurd herr (list_mapM_ne_error fun r hr => ?_)
      obtain ⟨ri, hri⟩ := relIn_ok (o := o) (P := L.secAddr[fi]![si]! + r.off) (h r (Array.mem_toList_iff.1 hr))
      simp only [hri, Except.mapError]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- **The planner accepts**: when the layout's references resolve (`layRefsB`), `layout`
returns a plan. -/
theorem layout_ok {o : Opts} {st : St} {g : GcOut} (h : layRefsB o st g = true) :
    ∃ pl m, layout o st g = .ok (pl, m) := by
  have hn := layPre_outs o st g
  generalize hL : layPre o st g = L at hn
  have hsorted : L.sorted = sortOSecs st.files (layDecide st g).osecs := by rw [← hL]; rfl
  have hgot : L.gotSyms = (layDecide st g).gotSyms := by rw [← hL]; rfl
  have hehs : L.ehs = (layDecide st g).ehs := by rw [← hL]; rfl
  have hslots := layPre_slots o st g
  rw [hL] at hslots
  unfold layRefsB at h
  simp only [Bool.and_eq_true, Array.all_eq_true'] at h
  obtain ⟨⟨⟨hentry, hg⟩, he⟩, hs⟩ := h
  rw [← hsorted, ← hn] at hg he hs
  rw [← hgot] at hg
  rw [← hehs] at he
  obtain ⟨got, hgot'⟩ := gotBytes_ok (L := L) (o := o) (st := st) (g := g) fun x hx => hg x hx
  obtain ⟨eh, heh⟩ := ehOut_ok (L := L) (o := o) (st := st) (g := g) fun e he' r hr =>
    he e he' r hr
  have hps : ∃ ps, L.pieces o st g = .ok ps := by
    unfold Lay.pieces
    simp only [hgot', heh, bind, Except.bind]
    obtain ⟨qs, hqs⟩ := list_mapM_ok (l := L.pst.slots.toList)
      (f := L.slotPiece o st g got (eh.1, eh.2.1) (L.ehHdrBytes eh.2.2)) fun sl hsl => by
      unfold Lay.slotPiece
      split
      · exact ⟨_, rfl⟩
      · split
        · rename_i fs hp
          obtain ⟨s, hs', hpart⟩ := hslots sl hsl
          have := hs s (Array.mem_toList_iff.1 hs') sl.part hpart
          rw [hp] at this
          exact inputPiece_ok fun r hr => Array.all_eq_true'.1 this r hr
        all_goals exact ⟨_, rfl⟩
    simp only [hqs, pure, Except.pure]
    exact ⟨_, rfl⟩
  obtain ⟨ps, hps⟩ := hps
  have hent : ∃ e, L.entry o st g = .ok e := by
    unfold entryOkB at hentry
    unfold Lay.entry
    split
    · rename_i f k w hk
      rw [hk] at hentry
      simp only [Bool.and_eq_true] at hentry
      simp only [hentry.1, hentry.2, Bool.and_self, ↓reduceIte, pure, Except.pure]
      exact ⟨_, rfl⟩
    · rename_i hk
      split at hentry
      · rename_i f k w hk'; exact absurd hk' (hk f k w)
      · cases hentry
  obtain ⟨e, he⟩ := hent
  unfold layout
  simp only [hL, hps, he, bind, Except.bind, pure, Except.pure]
  exact ⟨_, _, rfl⟩

/-! ## Non-vacuity -/

theorem tinyLayRefs : layRefsB {} tinySt tinyGc = true := by native_decide

/-- **`layout_ok`'s premise holds** on the one-object link. -/
theorem layout_ok_witness : ∃ pl m, layout {} tinySt tinyGc = .ok (pl, m) := layout_ok tinyLayRefs

end Link.Ld

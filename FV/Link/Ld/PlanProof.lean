module

public import FV.Link.Ld.Layout
public import FV.Link.Ld.BuildProof
public import FV.Link.Ld.File0

@[expose] public section

/-! # The plan's program headers and body (L2b stage 3e)

`assemble` (`FV/Link/Ld/Plan.lean`) builds the image of a plan whose conditions `Plan.okB` hold.
From them:

* `assemble_ok`, `link_ok`: a successful link's image is its plan's (`Plan.phdrs`, `buildBody`
  of the sorted pieces), its headers and tables fit (`hdrFitsB`, `tabsFitB`);
* `sorted_pairwise`, `mem_sorted`: the sorted pieces are the plan's, in disjoint file ranges;
* `segIn_phdrs`: an address of a segment is in that segment's `PT_LOAD` header (the segments'
  pages are disjoint);
* **`staticB_phdrs`**: the program headers are a static executable's (`staticB`);
* **`tpOff_phdrs`**: every value has a thread-pointer offset (`PT_TLS` is always there);
* **`regionPhsB_plan`**: the region condition holds of a region inside the `R E` segment's file
  bytes (`Plan.regionInB`), with `offsetOf_plan` its file offset's bound.
-/

namespace Link.Ld

open E2E E2E.Elf E2E.BinCheck Link

/-! ## Chains -/

theorem chainB_pairwise {α : Type} {r : α → α → Bool}
    (htr : ∀ a b c, r a b = true → r b c = true → r a c = true) :
    ∀ {l : List α}, chainB r l = true → l.Pairwise (fun a b => r a b = true)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [chainB, Bool.and_eq_true] at h
    have ih := chainB_pairwise htr (l := b :: rest) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact htr _ _ _ h.1 (List.rel_of_pairwise_cons ih hc)

theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: _, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha | ha <;> rcases List.mem_cons.1 hb with hb | hb
    · exact absurd (ha.trans hb.symm) hne
    · exact .inl (ha ▸ h.1 b hb)
    · exact .inr (hb ▸ h.1 a ha)
    · exact pairwise_mem_ne h.2 ha hb hne

theorem segBefore_trans {s t u : Seg} (h1 : segBefore s t = true) (h2 : segBefore t u = true) :
    segBefore s u = true := by
  simp only [segBefore, decide_eq_true_eq] at *
  omega

theorem pieceBefore_trans {p q u : Piece} (h1 : pieceBefore p q = true) (h2 : pieceBefore q u = true) :
    pieceBefore p u = true := by
  simp only [pieceBefore, decide_eq_true_eq] at *
  omega

/-! ## The plan's conditions -/

/-- `Plan.okB`'s parts. -/
theorem okB_parts {pl : Plan} (h : pl.okB = true) :
    pl.segs.Pairwise (fun s t => segBefore s t = true) ∧
    (∀ s ∈ pl.segs, s.kind ≤ 2 ∧ s.filesz ≤ s.memsz ∧ s.offset + s.filesz ≤ pl.size) ∧
    pl.sorted.Pairwise PieceDisj ∧ (∀ p ∈ pl.pieces, pl.hdrEnd ≤ p.fo) := by
  simp only [Plan.okB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, hk⟩, hp⟩, hh⟩ := h
  refine ⟨chainB_pairwise (r := segBefore) (fun _ _ _ => segBefore_trans) hs,
    fun s hs => ⟨(hk s hs).1.1, (hk s hs).1.2, (hk s hs).2⟩, ?_, hh⟩
  exact (chainB_pairwise (r := pieceBefore) (fun _ _ _ => pieceBefore_trans) hp).imp fun h => by
    simp only [pieceBefore, decide_eq_true_eq] at h
    exact .inl h

theorem mem_sorted {pl : Plan} {p : Piece} : p ∈ pl.sorted ↔ p ∈ pl.pieces :=
  (List.mergeSort_perm _ _).mem_iff

/-! ## The image of a plan -/

theorem body_size : ∀ {ps : List Piece} {body body' : ByteArray}, ps.foldlM bodyStep body = .ok body' →
    body'.size = body.size
  | [], _, _, h => by cases h; rfl
  | _ :: _, _, _, h => by
    obtain ⟨b1, h1, h2⟩ := body_foldlM_cons h
    rw [body_size h2, bodyStep_size h1]

theorem buildBody_size {size : Nat} {ps : List Piece} {body : ByteArray}
    (h : buildBody size ps = .ok body) : body.size = size := by
  rw [body_size h]
  show (Array.replicate size (0 : UInt8)).size = size
  simp

/-- **The image of a plan**: its program headers and the body of its pieces. -/
theorem assemble_ok {pl : Plan} {img : Img} (h : assemble pl = .ok img) :
    pl.okB = true ∧ buildBody pl.size pl.sorted = .ok img.body ∧ img.phs = pl.phdrs ∧
      img.entry = pl.entry ∧ img.secs = pl.secs ∧ img.syms = pl.syms := by
  unfold assemble at h
  by_cases hok : pl.okB = true
  · simp only [hok, Bool.not_true] at h
    cases hb : buildBody pl.size pl.sorted with
    | error e => simp [hb, bind, Except.bind] at h
    | ok body =>
      simp [hb, bind, Except.bind, pure, Except.pure] at h
      subst h
      exact ⟨hok, rfl, rfl, rfl, rfl, rfl⟩
  · simp [hok, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- **A successful link's image is its plan's**, with headers and tables that fit. -/
theorem link_ok {o : Opts} {ins : List Input} {r : LinkOut} (h : link o ins = .ok r) :
    assemble r.plan = .ok r.img ∧ r.img.hdrFitsB = true ∧ r.img.tabsFitB = true := by
  unfold link at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i x hl
  split at h
  · cases h
  rename_i img ha
  by_cases h1 : img.hdrFitsB = true
  · by_cases h2 : img.tabsFitB = true
    · simp [h1, h2, pure, Except.pure] at h
      subst h
      exact ⟨ha, h1, h2⟩
    · simp [h1, h2, throw, throwThe, MonadExceptOf.throw] at h
  · simp [h1, throw, throwThe, MonadExceptOf.throw] at h

/-! ## The program headers -/

theorem phdrs_length (pl : Plan) : pl.phdrs.length = pl.segs.length + 4 := by
  simp [Plan.phdrs]

theorem hdrEnd_eq (pl : Plan) : pl.hdrEnd = 64 + 56 * pl.phdrs.length := by
  rw [phdrs_length]; rfl

theorem find_seg : ∀ {segs : List Seg}, segs.Pairwise (fun s t => segBefore s t = true) →
    ∀ {s : Seg} {x : Nat}, s ∈ segs → s.vaddr ≤ x → x < s.vaddr + s.memsz →
      segs.find? (isLoad x ∘ Seg.ph) = some s
  | [], _, _, _, hs, _, _ => by cases hs
  | t :: rest, hp, s, x, hs, h1, h2 => by
    rw [List.pairwise_cons] at hp
    by_cases ht : t.vaddr ≤ x ∧ x < t.vaddr + t.memsz
    · rw [List.find?_cons_of_pos (by simp [isLoad, Seg.ph, ht.1, ht.2])]
      rcases List.mem_cons.1 hs with rfl | hs
      · rfl
      · have := hp.1 s hs
        simp only [segBefore, decide_eq_true_eq] at this
        omega
    · rw [List.find?_cons_of_neg (by
        simp only [Function.comp_apply, isLoad, Seg.ph, beq_self_eq_true, Bool.true_and,
          Bool.and_eq_true]
        exact fun h => ht ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩)]
      rcases List.mem_cons.1 hs with rfl | hs
      · exact absurd ⟨h1, h2⟩ ht
      · exact find_seg hp.2 hs h1 h2

/-- **An address of a segment is in that segment's `PT_LOAD` header.** -/
theorem segIn_phdrs {pl : Plan} (hp : pl.segs.Pairwise (fun s t => segBefore s t = true)) {s : Seg}
    (hs : s ∈ pl.segs) {x : Nat} (h1 : s.vaddr ≤ x) (h2 : x < s.vaddr + s.memsz) :
    segIn pl.phdrs x = some s.ph := by
  unfold segIn Plan.phdrs
  rw [List.find?_cons_of_neg (by simp [isLoad]), List.find?_append, List.find?_map,
    find_seg hp hs h1 h2]
  rfl

theorem filter_phdrs (pl : Plan) : pl.phdrs.filter (·.type == 1) = pl.segs.map Seg.ph := by
  simp [Plan.phdrs, List.filter_map, Seg.ph, Function.comp_def]
  rw [List.filter_eq_self.2 fun _ _ => rfl]

/-- **The program headers are a static executable's.** -/
theorem staticB_phdrs {pl : Plan} (h : pl.okB = true) {e : Ehdr} (h2 : e.type = 2)
    (h183 : e.machine = 183) : staticB e pl.phdrs = true := by
  obtain ⟨hp, hs, -, -⟩ := okB_parts h
  have hpi := List.pairwise_iff_getElem.1 hp
  unfold staticB
  rw [filter_phdrs]
  simp only [Bool.and_eq_true, beq_iff_eq, h2, h183, true_and, List.all_eq_true]
  refine ⟨fun q hq => ?_, fun ⟨q, i⟩ hx => ?_⟩
  · simp only [Plan.phdrs, List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | ⟨s, -, rfl⟩ | rfl | rfl | rfl | hq <;> simp_all [Seg.ph]
  · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨s, hs1, rfl⟩ := hx
    obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.1 hs1
    refine ⟨decide_eq_true (hs _ (List.mem_of_getElem? hs1)).2.1,
      fun ⟨q', j⟩ hy => ?_⟩
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map, Option.map_eq_some_iff] at hy
    obtain ⟨t, ht1, rfl⟩ := hy
    obtain ⟨hj, htj⟩ := List.getElem?_eq_some_iff.1 ht1
    simp only [Bool.or_eq_true, beq_iff_eq, pagesApart, Seg.ph]
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have := hpi _ _ hi hj hlt
      rw [hsi, htj] at this
      simp only [segBefore, decide_eq_true_eq] at this
      exact .inr (.inl (decide_eq_true this))
    · exact .inl heq
    · have := hpi _ _ hj hi hgt
      rw [hsi, htj] at this
      simp only [segBefore, decide_eq_true_eq] at this
      exact .inr (.inr (decide_eq_true this))

/-- The thread-pointer offset of the start of a TLS block aligned to `al` (AArch64: after the
16-byte TCB). -/
def tlsBase (al : Nat) : Nat := (16 + max al 1 - 1) / max al 1 * max al 1

/-- **Every value has a thread-pointer offset** (`PT_TLS` is always there). -/
theorem tpOff_phdrs (pl : Plan) (v : Nat) : tpOff pl.phdrs v = some (tlsBase pl.tlsAlign + v) := by
  unfold tpOff Plan.phdrs
  rw [List.find?_cons_of_neg (by simp), List.find?_append, List.find?_map,
    List.find?_eq_none.2 (fun s _ => by simp [Seg.ph])]
  rfl

/-! ## The region -/

/-- **The region `[R, R + n)` lies in the `R E` segment's file bytes** (after the headers). -/
def Plan.regionInB (pl : Plan) (R n : Nat) : Bool :=
  pl.segs.any fun s => s.kind == 1 && decide (s.vaddr ≤ R) && decide (R < s.vaddr + s.memsz) &&
    decide (R + n ≤ s.vaddr + s.filesz) && decide (pl.hdrEnd ≤ s.offset + (R - s.vaddr))

theorem regionInB_seg {pl : Plan} {R n : Nat} (h : pl.regionInB R n = true) :
    ∃ s ∈ pl.segs, s.kind = 1 ∧ s.vaddr ≤ R ∧ R < s.vaddr + s.memsz ∧ R + n ≤ s.vaddr + s.filesz ∧
      pl.hdrEnd ≤ s.offset + (R - s.vaddr) := by
  simp only [Plan.regionInB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨s, hs, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩ := h
  exact ⟨s, hs, h1, h2, h3, h4, h5⟩

/-- The region's file offset and its end. -/
theorem offsetOf_plan {pl : Plan} (h : pl.okB = true) {R n : Nat} (hr : pl.regionInB R n = true) :
    pl.hdrEnd ≤ offsetOf pl.phdrs R ∧ offsetOf pl.phdrs R + n ≤ pl.size := by
  obtain ⟨hp, hk, -, -⟩ := okB_parts h
  obtain ⟨s, hs, -, h2, h3, h4, h5⟩ := regionInB_seg hr
  have := (hk s hs).2.2
  simp only [offsetOf, segIn_phdrs hp hs h2 h3, Seg.ph]
  omega

/-- **The region condition holds of a region in the `R E` segment's file bytes.** -/
theorem regionPhsB_plan {pl : Plan} (h : pl.okB = true) {R n size : Nat}
    (hr : pl.regionInB R n = true) (hsz : pl.size ≤ size) :
    regionPhsB pl.phdrs R n (offsetOf pl.phdrs R) size = true := by
  obtain ⟨hp, hk, -, -⟩ := okB_parts h
  obtain ⟨s, hs, h1, h2, h3, h4, h5⟩ := regionInB_seg hr
  obtain ⟨-, hfm, hfs⟩ := hk s hs
  have hoff := offsetOf_plan h hr
  have hl := hdrEnd_eq pl
  unfold regionPhsB
  rw [segIn_phdrs hp hs h2 h3]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq]
  refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, fun q hq => ?_⟩⟩
  · simp [notW, Seg.ph, Seg.flags, h1]
  · exact h4
  · exact hfm
  · simp only [offsetOf, segIn_phdrs hp hs h2 h3]
  · simp only [Plan.phdrs, List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | ⟨t, ht, rfl⟩ | rfl | rfl | rfl | hq
    · exact .inl (.inl (.inr (by simp)))
    · by_cases hts : t = s
      · subst hts; exact .inl (.inl (.inl rfl))
      · rcases pairwise_mem_ne hp ht hs hts with hb | hb <;>
          simp only [segBefore, decide_eq_true_eq] at hb <;> simp only [Seg.ph]
        · exact .inl (.inr (by omega))
        · exact .inr (by omega)
    all_goals first | exact .inl (.inl (.inr (by simp))) | simp at *

end Link.Ld

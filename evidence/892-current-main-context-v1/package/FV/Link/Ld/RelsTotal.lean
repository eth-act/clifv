import FV.Link.Ld.RelocTotal

/-! # Every relocation of `lean-ld`'s plan applies (A1d, #409)

`relsInB` decides, without computing an address, that every relocation `lean-ld` resolves
passes the checks of `relCheckB` (`FV/Link/Ld/RelocTotal.lean`):

* `secRelsB`: each relocation of an input section placed in an output section (unless
  `SHT_NOBITS`) patches bytes inside the section (whose bytes are in its file), its symbol has a
  kind (`tgtOf`) and `relCheckB` holds with the place in `[base, top]` (`[0, top]` in the TLS
  template);
* `ehRelsB`: each relocation of a kept `.eh_frame` record patches bytes inside the record and
  `relCheckB` holds with the place in `[0, top + eh]`;
* the layout's address-free conditions `dOkB`.

**`layout_relsOk`**: then every piece of `layout`'s plan has `relsOkB`, so `assemble` succeeds
(`assemble_layout_ok`, `FV/Link/Ld/BodyTotal.lean`).
-/

namespace Link.Ld

/-! ## The checks -/

/-- **The relocation checks of input section `t`** (`B`: the bounds, `sorted`: the output
sections): its bytes in its file, each relocation inside the section, with a symbol kind, passing
`relCheckB` (the place in `[base, top]`, `[0, top]` inside the TLS template; same section `t`;
4-aligned when the section's alignment and the offset are). `SHT_NOBITS`: no piece. -/
def secRelsB (st : St) (g : GcOut) (B : Bnd) (sorted : Array OSec) (t : SecId) : Bool :=
  let f := st.files[t.1]!
  let s := f.secs[t.2]!
  s.type == shtNobits ||
    (decide (t.1 < st.files.size) && decide (t.2 < f.secs.size) && decide (s.off + s.size ≤ f.data.size) &&
      (f.relas t.2).all fun r => decide (r.off + relocWidth r.type ≤ s.size) &&
        match tgtOf st g sorted t.1 r.sym with
        | some k => relCheckB B (al4B st.files) r.type k r.addend
            (if (secsOf sorted (.input t)).all (!tlsName ·) then (B.base : Int) else 0) B.top
            (some (t, r.off)) (al4B st.files t && r.off % 4 == 0)
        | none => false)

/-- **The relocation checks of a kept `.eh_frame` record** `e`: each relocation inside the
record, with a symbol kind, passing `relCheckB` (the place in `[0, top + eh]`). -/
def ehRelsB (st : St) (g : GcOut) (B : Bnd) (sorted : Array OSec) (e : EhOut) : Bool :=
  (ehRelas g e).all fun r =>
    decide (e.piece.off ≤ r.off ∧ r.off + relocWidth r.type ≤ e.piece.off + e.piece.size) &&
    match tgtOf st g sorted e.file r.sym with
    | some k => relCheckB B (al4B st.files) r.type k r.addend 0 (B.top + B.eh) none false
    | none => false

/-- **The relocations of the layout apply**: the address-free conditions `dOkB`, every kept
`.eh_frame` record's relocations (`ehRelsB`) and every placed input section's (`secRelsB`).
Decided on the layout's decisions (`layDecide`, `sortOSecs`) and the bounds `bndOf`, no
address. -/
def relsInB (o : Opts) (st : St) (g : GcOut) : Bool :=
  let D := layDecide st g
  let sorted := sortOSecs st.files D.osecs
  let B := bndOf o st g
  dOkB D sorted && D.ehs.all (ehRelsB st g B sorted) &&
    sorted.all fun s => s.parts.all fun p => match p with
      | .input t => secRelsB st g B sorted t
      | _ => true

/-! ## The pieces' relocations -/

theorem clampTo_size_eq {n : Nat} {b : ByteArray} (h : n ≤ b.size) : (clampTo n b).size = n := by
  unfold clampTo
  split
  · omega
  · simp only [ByteArray.size_extract]; omega

/-- **An input section's piece**: its section's bytes, each relocation an input relocation
resolved at the section's address. -/
theorem inputPiece_rels {L : Lay} {o : Opts} {st : St} {g : GcOut} {sl : Slot} {fi si : Nat}
    {p : Piece} (h : L.inputPiece o st g sl fi si = .ok (some p)) :
    (st.files[fi]!.secs[si]!.type == shtNobits) = false ∧
    p.bytes = clampTo sl.size (st.files[fi]!.data.extract st.files[fi]!.secs[si]!.off
      (st.files[fi]!.secs[si]!.off + st.files[fi]!.secs[si]!.size)) ∧
    ∀ rel ∈ p.rels, ∃ r ∈ (st.files[fi]!.relas si).toList, rel.off = r.off ∧ rel.ty = r.type ∧
      L.relIn o st g fi r (L.secAddr[fi]![si]! + r.off) = .ok rel.ri := by
  unfold Lay.inputPiece at h
  dsimp only at h
  split at h
  · simp [pure, Except.pure] at h
  · rename_i hnb
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i rs hrs
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      simp only [Slot.piece]
      refine ⟨Bool.eq_false_iff.2 hnb, trivial, fun rel hrel => ?_⟩
      have hrel' : rel ∈ rs := (List.mergeSort_perm rs _).mem_iff.1 hrel
      obtain ⟨r, hr, hfr⟩ := forall₂_mem_right (mapM_forall₂ hrs) hrel'
      refine ⟨r, hr, ?_⟩
      split at hfr
      · cases hfr
      · rename_i ri hri
        simp only [pure, Except.pure, Except.ok.injEq] at hfr
        subst hfr
        cases hrl : L.relIn o st g fi r (L.secAddr[fi]![si]! + r.off) with
        | error e => rw [hrl] at hri; cases hri
        | ok ri' =>
          rw [hrl] at hri
          simp only [Except.mapError, Except.ok.injEq] at hri
          subst hri
          exact ⟨rfl, rfl, rfl⟩

section
variable {o : Opts} {st : St} {g : GcOut}

/-- **An input section's piece's relocations apply** under `secRelsB`. -/
theorem inputPiece_relsOk (hf : LFacts o st g) (hd : dOkB (layDecide st g) (layPre o st g).sorted = true)
    {x : Slot} (hx : x ∈ (layPre o st g).pst.slots.toList) {t : SecId} (hxp : x.part = .input t)
    {p : Piece} (hp : (layPre o st g).inputPiece o st g x t.1 t.2 = .ok (some p))
    (hc : secRelsB st g (bndOf o st g) (layPre o st g).sorted t = true) : p.relsOkB = true := by
  obtain ⟨hnb, hbytes, hrels⟩ := inputPiece_rels hp
  obtain ⟨s, hs, hps, -, hsz, -⟩ := layPre_slot o st g hx
  rw [hxp] at hps hsz
  unfold secRelsB at hc
  simp only [hnb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true'] at hc
  obtain ⟨⟨⟨h1, h2⟩, hdata⟩, hall⟩ := hc
  have e1 : st.files[t.1]! = st.files[t.1] := getElem!_pos st.files t.1 h1
  rw [e1] at h2
  have hne : secsOf (layPre o st g).sorted (.input t) ≠ [] :=
    List.ne_nil_of_mem (mem_secsOf.2 ⟨hs, hps⟩)
  obtain ⟨y, -, -, hya, -, hysz, hyal, hytop, hybase, -⟩ := secAddr_spec hf h1 h2 hne
  have hsec : st.files[t.1]!.secs[t.2]! = st.files[t.1].secs[t.2] := by
    rw [e1]; exact getElem!_pos st.files[t.1].secs t.2 h2
  have hsz' : x.size = st.files[t.1]!.secs[t.2]!.size := by
    rw [hsz]; simp [LayD.partSize]
  have hbs : p.bytes.size = st.files[t.1]!.secs[t.2]!.size := by
    rw [hbytes, clampTo_size_eq, hsz']
    simp only [ByteArray.size_extract]; omega
  unfold Piece.relsOkB
  rw [List.all_eq_true]
  intro rel hrel
  obtain ⟨r, hr, hoff, hty, hri⟩ := hrels rel hrel
  have hrc := hall r (Array.mem_toList_iff.1 hr)
  obtain ⟨hw, hk⟩ := hrc
  split at hk
  · rename_i k htk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by rw [hoff, hty, hbs]; exact hw, ?_⟩
    rw [hty]
    have hysz' : y.size = st.files[t.1]!.secs[t.2]!.size := by rw [hysz, hsec]
    refine relIn_relocOkB hf hd hri htk hk ?_ (fun t' off h' => ?_) (fun h4 => ?_)
    · rw [hya]
      constructor
      · split
        · rename_i hall'
          have := hybase hall'
          push_cast; omega
        · push_cast; omega
      · push_cast; omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rfl
    · simp only [Bool.and_eq_true, beq_iff_eq] at h4
      obtain ⟨ha4, ho4⟩ := h4
      simp only [al4B, beq_iff_eq, hsec] at ha4
      rw [hya]
      have := mod4_of hyal ha4
      omega
  · cases hk

/-- **The output `.eh_frame`'s relocations apply** under `ehRelsB`. -/
theorem ehPiece_relsOk (hf : LFacts o st g) (hd : dOkB (layDecide st g) (layPre o st g).sorted = true)
    {x : Slot} (hx : x ∈ (layPre o st g).pst.slots.toList) (hxp : x.part = .eh)
    {res : ByteArray × Array Rel × Array (Nat × Nat)} (hres : (layPre o st g).ehOut o st g = .ok res)
    (hc : ∀ e ∈ (layDecide st g).ehs, ehRelsB st g (bndOf o st g) (layPre o st g).sorted e = true) :
    (x.piece res.1 res.2.1.toList).relsOkB = true := by
  obtain ⟨-, -, -, hes⟩ := dOk_parts hd
  have het : (layPre o st g).ehTotal = (layDecide st g).ehTotal := rfl
  obtain ⟨hsize, hrels⟩ := ehOut_spec (L := layPre o st g)
    (fun e he => by have := hes e he; rw [het]; omega) hres
  rw [het] at hsize
  obtain ⟨-, -, -, -, hsz, -⟩ := layPre_slot o st g hx
  rw [hxp] at hsz
  have hsz' : x.size = (layDecide st g).ehTotal := by rw [hsz]; rfl
  have hbs : (x.piece res.1 res.2.1.toList).bytes.size = (layDecide st g).ehTotal := by
    show (clampTo x.size res.1).size = _
    rw [hsz', clampTo_size_eq hsize]
  unfold Piece.relsOkB
  rw [List.all_eq_true]
  intro rel hrel
  obtain ⟨e, he, r, hr, hoff, hty, hri⟩ := hrels rel hrel
  have he' : e ∈ (layDecide st g).ehs := Array.mem_toList_iff.1 he
  have hrc := Array.all_eq_true'.1 (by have := hc e he'; unfold ehRelsB at this; exact this) r
    (Array.mem_toList_iff.1 hr)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrc
  obtain ⟨⟨hlo, hw⟩, hk⟩ := hrc
  have hee := hes e he'
  split at hk
  · rename_i k htk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by rw [hoff, hty, hbs]; omega, ?_⟩
    rw [hty]
    have hea : (layPre o st g).ehAddr ≤ (bndOf o st g).top := partAddr_le hf "eh"
    have heh : (bndOf o st g).eh = (layDecide st g).ehTotal := rfl
    refine relIn_relocOkB hf hd hri htk hk ⟨by omega, by omega⟩ (fun _ _ h' => by cases h')
      (fun h4 => by cases h4)
  · cases hk

/-- **Every piece of `layout`'s plan has relocations that apply** when `relsInB` holds. -/
theorem layout_relsOk {pl : Plan} {m : String} (h : layout o st g = .ok (pl, m))
    (hr : relsInB o st g = true) : ∀ p ∈ pl.pieces, p.relsOkB = true := by
  obtain ⟨ps, hps, -, hpcs, -⟩ := layout_eq h
  unfold relsInB at hr
  simp only [Bool.and_eq_true, Array.all_eq_true'] at hr
  obtain ⟨⟨hd, heh⟩, hsec⟩ := hr
  have hf : LFacts o st g := lfacts hd
  have hd' : dOkB (layDecide st g) (layPre o st g).sorted = true := hd
  unfold Lay.pieces at hps
  simp only [bind, Except.bind] at hps
  split at hps
  · cases hps
  rename_i got _
  split at hps
  · cases hps
  rename_i res hres
  split at hps
  · cases hps
  rename_i qs hq
  simp only [pure, Except.pure, Except.ok.injEq] at hps
  subst hps
  intro p hp
  rw [hpcs] at hp
  obtain ⟨op, hop, hpo⟩ := List.mem_filterMap.1 hp
  simp only [id_eq] at hpo
  subst hpo
  obtain ⟨x, hx, hxp⟩ := forall₂_mem_right (mapM_forall₂ hq) hop
  unfold Lay.slotPiece at hxp
  split at hxp
  · simp [pure, Except.pure] at hxp
  split at hxp
  · rename_i fs hpart
    obtain ⟨s, hs, hps, -⟩ := layPre_slot o st g hx
    have := hsec s (Array.mem_toList_iff.1 hs) x.part hps
    rw [hpart] at this
    exact inputPiece_relsOk hf hd' hx hpart hxp this
  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hxp
    subst hxp; rfl
  · rename_i hpart
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hxp
    subst hxp
    exact ehPiece_relsOk hf hd' hx hpart hres fun e he => heh e he
  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hxp
    subst hxp; rfl
  · simp [pure, Except.pure] at hxp

end

end Link.Ld

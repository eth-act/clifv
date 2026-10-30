import FV.Link.Ld.BodyTotal
import FV.Link.Ld.Places

/-! # `lean-ld`'s relocations apply on inputs within bounds (A1c, #409)

The relocations of `lean-ld`'s pieces are resolved at the layout's addresses. Without computing
an address, the inputs give bounds on them (`Bnd`, from the layout's decisions `layDecide` and
the output sections' order `sortOSecs` only): every placed part lies in `[base, top]` (`top`:
the base, the headers and twice the parts' alignments and sizes and two pages per output
section, `layPre_bound`); the thread-local ones in `[tls, tls + TD + TB]` (`TI`).

Each relocation's symbol is classified without addresses (`tgtOf`: a section placed outside or
inside the TLS template, an input `.eh_frame`, an absolute value, a common symbol, a
linker-defined name, an undefined weak symbol), with an interval of its value (`sIv`); the
place's interval follows from its section. `relCheckB` decides that every value in the
intervals is in the relocation type's range (and that branch targets are 4-aligned), so the
resolved relocation is (`relocOkB`, **`relIn_relocOkB`**).
-/

namespace Link.Ld

/-! ## Every part is placed -/

theorem placeParts_grow (sz al : Part → Nat) (start soff out : Nat) (bits tl : Bool) :
    ∀ (ps : List Part) (a : Nat) (acc : Array Slot),
      (∀ x ∈ acc.toList, x ∈ (placeParts sz al start soff out bits tl a ps acc).2.toList) ∧
      ∀ p ∈ ps, ∃ x ∈ (placeParts sz al start soff out bits tl a ps acc).2.toList, x.part = p
  | [], _, _ => ⟨fun _ h => h, fun _ h => by cases h⟩
  | p :: ps, a, acc => by
    obtain ⟨h1, h2⟩ := placeParts_grow sz al start soff out bits tl ps (alignUp a (al p) + sz p)
      (acc.push (Slot.mk p (alignUp a (al p)) (soff + (alignUp a (al p) - start)) (sz p) out bits tl))
    simp only [placeParts]
    refine ⟨fun x hx => h1 x (by simp [hx]), fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨Slot.mk q (alignUp a (al q)) (soff + (alignUp a (al q) - start)) (sz q) out bits tl,
        h1 _ (by simp), rfl⟩
    · exact h2 q hq

theorem foldl_grow (sz al : Part → Nat) (nb : Part → Bool) (ta : Nat) :
    ∀ (l : List OSec) (st : PSt),
      (∀ x ∈ st.slots.toList, x ∈ (l.foldl (placeSec sz al nb ta) st).slots.toList) ∧
      ∀ s ∈ l, ∀ p ∈ s.parts, ∃ x ∈ (l.foldl (placeSec sz al nb ta) st).slots.toList, x.part = p
  | [], _ => ⟨fun _ h => h, fun _ h => by cases h⟩
  | s :: l, st => by
    obtain ⟨h1, h2⟩ := foldl_grow sz al nb ta l (placeSec sz al nb ta st s)
    have hs : placeSec sz al nb ta st s = placeIn sz al nb ta (st.openSeg s.seg) s := rfl
    have hpg := placeParts_grow sz al
    refine ⟨fun x hx => h1 x ?_, fun t ht p hp => ?_⟩
    · rw [hs]; unfold placeIn
      refine (hpg _ _ _ _ _ _ _ _).1 x ?_
      unfold PSt.openSeg; split <;> exact hx
    · rcases List.mem_cons.1 ht with rfl | ht
      · obtain ⟨x, hx, hp'⟩ := (hpg _ _ _ _ _ _ _ (st.openSeg t.seg).slots).2 p (Array.mem_toList_iff.2 hp)
        refine ⟨x, h1 x ?_, hp'⟩
        rw [hs]; unfold placeIn; exact hx
      · exact h2 t ht p hp

/-- **Every part of an output section has a slot.** -/
theorem layPre_complete (o : Opts) (st : St) (g : GcOut) {s : OSec} (hs : s ∈ (layPre o st g).sorted.toList)
    {p : Part} (hp : p ∈ s.parts) : ∃ x ∈ (layPre o st g).pst.slots.toList, x.part = p := by
  have := (foldl_grow ((layDecide st g).partSize st.files) (LayD.partAlign st.files) (LayD.partNb st.files)
    (tlsAlignOf (LayD.partAlign st.files) (sortOSecs st.files (layDecide st g).osecs))
    (sortOSecs st.files (layDecide st g).osecs).toList (PSt.init o.base)).2 s hs p hp
  rw [Array.foldl_toList] at this
  exact this

/-! ## The bounds -/

/-- **The inputs' bounds**, from the layout's decisions and the output sections' order. -/
structure Bnd where
  base : Nat
  top : Nat
  TD : Nat
  TB : Nat
  eh : Nat
  got : Nat
  deriving Repr

/-- The bounds of a link (`top`: `base + hdrSize + 2 * placeBound`). -/
def bndOf (o : Opts) (st : St) (g : GcOut) : Bnd :=
  let D := layDecide st g
  let sorted := sortOSecs st.files D.osecs
  let sz := D.partSize st.files
  let al := LayD.partAlign st.files
  let ta := tlsAlignOf al sorted
  { base := o.base, top := o.base + hdrSize + 2 * placeBound sz al ta sorted.toList,
    TD := namedBound sz al ta ".tdata" sorted.toList, TB := namedBound sz al ta ".tbss" sorted.toList,
    eh := D.ehTotal, got := D.gotSyms.size }

/-- A TLS template section's name. -/
def tlsName (s : OSec) : Bool := s.name == ".tdata" || s.name == ".tbss"

/-- The output sections holding part `p`. -/
def secsOf (sorted : Array OSec) (p : Part) : List OSec :=
  sorted.toList.filter fun s => s.parts.toList.any fun q => decide (q = p)

theorem mem_secsOf {sorted : Array OSec} {p : Part} {s : OSec} :
    s ∈ secsOf sorted p ↔ s ∈ sorted.toList ∧ p ∈ s.parts := by
  simp only [secsOf, List.mem_filter, List.any_eq_true, decide_eq_true_eq, Array.mem_toList_iff]
  exact ⟨fun ⟨h1, q, hq, e⟩ => ⟨h1, e ▸ hq⟩, fun ⟨h1, h2⟩ => ⟨h1, p, h2, rfl⟩⟩

/-- **The layout's address-free conditions** (`dOkB`): the `.eh_frame` records' and inputs'
offsets within the output `.eh_frame`, the GOT's slots within the GOT, `.tdata` once and before
`.tbss`. -/
def dOkB (D : LayD) (sorted : Array OSec) : Bool :=
  D.pieceOut.toList.all (fun e => decide (e.2 ≤ D.ehTotal)) &&
  D.ehStart.toList.all (fun e => decide (e.2 ≤ D.ehTotal)) &&
  D.gotSlot.toList.all (fun e => decide (e.2 < D.gotSyms.size)) &&
  D.ehs.all (fun e => decide (e.out + e.piece.size ≤ D.ehTotal)) &&
  tlsOrderB false sorted.toList && sorted.toList.any (·.name == ".tdata")

/-! ## The layout's facts from the bounds -/

/-- The facts of a layout the relocation checks use. -/
structure LFacts (o : Opts) (st : St) (g : GcOut) : Prop where
  pb : PB o.base (placeBound ((layDecide st g).partSize st.files) (LayD.partAlign st.files)
      (tlsAlignOf (LayD.partAlign st.files) (layPre o st g).sorted) (layPre o st g).sorted.toList)
      (layPre o st g).pst
  va : (layPre o st g).pst.va + placeBound ((layDecide st g).partSize st.files) (LayD.partAlign st.files)
      (tlsAlignOf (LayD.partAlign st.files) (layPre o st g).sorted) (layPre o st g).sorted.toList ≤ (bndOf o st g).top
  ti : TI (bndOf o st g).TD (bndOf o st g).TB true (layPre o st g).pst
  pinv : PInv (layPre o st g).pst

theorem namedBound_le {sz al : Part → Nat} {ta : Nat} {n : String} {l : List OSec} {s : OSec} (hs : s ∈ l)
    (hn : s.name = n) : secBound sz al ta s ≤ namedBound sz al ta n l := by
  unfold namedBound
  exact le_sum_of_mem (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simp [hn]⟩, rfl⟩)

theorem lfacts {o : Opts} {st : St} {g : GcOut}
    (hd : dOkB (layDecide st g) (sortOSecs st.files (layDecide st g).osecs) = true) : LFacts o st g := by
  obtain ⟨h1, h2⟩ := layPre_bound o st g
  simp only [dOkB, Bool.and_eq_true] at hd
  obtain ⟨⟨-, hord⟩, hany⟩ := hd
  have hti := TI_foldl (sz := (layDecide st g).partSize st.files) (al := LayD.partAlign st.files)
    (nb := LayD.partNb st.files)
    (ta := tlsAlignOf (LayD.partAlign st.files) (sortOSecs st.files (layDecide st g).osecs))
    (TD := (bndOf o st g).TD) (TB := (bndOf o st g).TB)
    (sortOSecs st.files (layDecide st g).osecs).toList false (PSt.init o.base) (TI_init _ _ _) hord
    (fun s hs hn => namedBound_le hs hn) (fun s hs hn => namedBound_le hs hn)
  rw [hany, Bool.false_or, Array.foldl_toList] at hti
  refine ⟨h1, ?_, hti, PInv_layPre o st g⟩
  show _ ≤ o.base + hdrSize + 2 * _
  have := h2
  have e : (layPre o st g).sorted = sortOSecs st.files (layDecide st g).osecs := rfl
  rw [e] at this ⊢
  omega

/-! ## Values -/

/-- Every name `synthTable` lists. -/
def synthAllNames : List String := synthNames ++ ["__eh_frame_start", "__eh_frame_hdr_start"]

/-- A name the linker may define (`Lay.synth`). -/
def synthMaybeB (n : String) : Bool :=
  n.startsWith "__start_" || n.startsWith "__stop_" || synthAllNames.contains n

theorem synthTable_names (L : Lay) (o : Opts) : (L.synthTable o).map (·.1) = synthAllNames := rfl

theorem lookup_none {l : List (String × Option Nat)} {a : String} (h : a ∉ l.map (·.1)) : l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hk : (a == k) = false := by simp [h.1]
    simp only [List.lookup, hk]
    exact ih h.2

theorem synth_none {L : Lay} {o : Opts} {n : String} (h : synthMaybeB n = false) : L.synth o n = none := by
  simp only [synthMaybeB, Bool.or_eq_false_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Lay.synth
  rw [if_neg (by simp [h1]), if_neg (by simp [h2])]
  unfold Lay.synthFixed
  rw [lookup_none (by rw [synthTable_names]; simpa using h3)]
  rfl

/-- **What a relocation's symbol is**, without addresses. -/
inductive Tgt where
  | img (t : SecId) (x : Nat)
  | tls (x : Nat)
  | eh (x : Nat)
  | abs (v : Nat)
  | common
  | synth
  | weak
  deriving Repr

/-- The kind of symbol `j` of file `fi` (`none`: no value, or in sections of both kinds). -/
def tgtOf (st : St) (g : GcOut) (sorted : Array OSec) (fi j : Nat) : Option Tgt :=
  let names := sorted.toList.map (·.name)
  match st.target fi j with
  | .sec t x _ =>
    if (g.live[t.1]?.bind (·[t.2]?)).getD false then
      if h : t.1 < st.files.size then
        if t.2 < st.files[t.1].secs.size && decide (x ≤ st.files[t.1].secs[t.2]!.size) &&
            !(secsOf sorted (.input t)).isEmpty then
          if (secsOf sorted (.input t)).all (!tlsName ·) then some (.img t x)
          else if (secsOf sorted (.input t)).all tlsName then some (.tls x)
          else none
        else none
      else none
    else if (g.eh[t.1]!.findIdx? (·.sec == t.2)).isSome then some (.eh x) else none
  | .abs v => some (.abs v)
  | .common _ _ => some .common
  | .undef n w => if synthKnownB names n then some .synth else if w && !synthMaybeB n then some .weak else none

/-- The interval of a value of a symbol of kind `k` (thread-local ones: none). -/
def sIv (B : Bnd) : Tgt → Option (Int × Int)
  | .img _ _ => some (B.base, B.top)
  | .tls _ => none
  | .eh x => some (0, B.top + B.eh + x)
  | .abs v => some (v, v)
  | .common => some (0, B.top)
  | .synth => some (0, B.top)
  | .weak => some (0, 0)

/-! ## The places' bounds -/

section
variable {o : Opts} {st : St} {g : GcOut}

theorem top_of (hf : LFacts o st g) {x : Slot} (hx : x ∈ (layPre o st g).pst.slots.toList) :
    x.addr + x.size ≤ (bndOf o st g).top := by
  have := (hf.pb.slots x hx).1; have := hf.va; omega

/-- **An input section in output sections** has a slot's address: in `[base, top]` outside the
TLS template, in it inside. -/
theorem secAddr_spec (hf : LFacts o st g) {t : SecId} (h1 : t.1 < st.files.size)
    (h2 : t.2 < st.files[t.1].secs.size) (hne : secsOf (layPre o st g).sorted (.input t) ≠ []) :
    ∃ x ∈ (layPre o st g).pst.slots.toList, x.part = .input t ∧
      (layPre o st g).secAddr[t.1]![t.2]! = x.addr ∧ (layPre o st g).secOut[t.1]![t.2]! = x.out ∧
      x.size = st.files[t.1].secs[t.2].size ∧
      x.addr % max (max st.files[t.1].secs[t.2].align 1) 1 = 0 ∧
      x.addr + x.size ≤ (bndOf o st g).top ∧
      ((secsOf (layPre o st g).sorted (.input t)).all (!tlsName ·) = true → (bndOf o st g).base ≤ x.addr) ∧
      ((secsOf (layPre o st g).sorted (.input t)).all tlsName = true →
        (layPre o st g).pst.tls.1 ≤ x.addr ∧
          x.addr + x.size ≤ (layPre o st g).pst.tls.1 + (bndOf o st g).TD + (bndOf o st g).TB) := by
  obtain ⟨s0, hs0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hs0', hp0⟩ := mem_secsOf.1 hs0
  obtain ⟨y, hy, hyp⟩ := layPre_complete o st g hs0' hp0
  obtain ⟨x, hx, hxp, ha, ho⟩ := slotMaps_sec (files := st.files) h1 h2 ⟨y, hy, hyp⟩
  obtain ⟨s, hs, hps, htls, hsz, hal⟩ := layPre_slot o st g hx
  have hss : s ∈ secsOf (layPre o st g).sorted (.input t) := mem_secsOf.2 ⟨hs, hxp ▸ hps⟩
  rw [hxp] at hsz hal
  have hsz' : x.size = st.files[t.1].secs[t.2].size := by
    rw [hsz]; simp [LayD.partSize, getElem!_pos, h1, h2]
  have hal' : x.addr % max (max st.files[t.1].secs[t.2].align 1) 1 = 0 := by
    rw [← hal]; simp [LayD.partAlign, getElem!_pos, h1, h2]
  refine ⟨x, hx, hxp, ha, ho, hsz', hal', top_of hf hx, fun hall => ?_, fun hall => ?_⟩
  · have := List.all_eq_true.1 hall s hss
    exact (hf.pb.slots x hx).2 (by rw [htls]; simpa [tlsName] using this)
  · have := List.all_eq_true.1 hall s hss
    exact hf.ti.slots rfl x hx (by rw [htls]; simpa [tlsName] using this)

theorem partAddr_le (hf : LFacts o st g) (k : String) :
    (layPre o st g).partAddr.getD k 0 ≤ (bndOf o st g).top := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h : (layPre o st g).partAddr[k]? with
  | none => exact Nat.zero_le _
  | some a =>
    obtain ⟨x, hx, rfl, -⟩ := slotMaps_part (files := st.files) h
    have := top_of hf hx; simp only [Option.getD_some]; omega

theorem partAddr_some (hf : LFacts o st g) {k : String} {a : Nat} (h : (layPre o st g).partAddr[k]? = some a) :
    a ≤ (bndOf o st g).top := by
  have := partAddr_le hf k
  rw [Std.HashMap.getD_eq_getD_getElem?, h] at this; exact this

theorem commonAddr_le (hf : LFacts o st g) (fk : Nat × Nat) :
    (layPre o st g).commonAddr.getD fk 0 ≤ (bndOf o st g).top := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h : (layPre o st g).commonAddr[fk]? with
  | none => exact Nat.zero_le _
  | some a =>
    obtain ⟨x, hx, rfl, -⟩ := slotMaps_common (files := st.files) h
    have := top_of hf hx; simp only [Option.getD_some]; omega

theorem outRange_le (hf : LFacts o st g) {n : String} {a b : Nat} (h : (layPre o st g).outRange n = some (a, b)) :
    a ≤ (bndOf o st g).top ∧ b ≤ (bndOf o st g).top := by
  unfold Lay.outRange at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨s, hs, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hm := Array.mem_of_find?_eq_some hs
  have := hf.pb.outs s (Array.mem_toList_iff.2 hm)
  have := hf.va
  omega

theorem segs_le (hf : LFacts o st g) {s : Seg} (hs : s ∈ (layPre o st g).segs) :
    s.vaddr + s.memsz ≤ (bndOf o st g).top ∧ s.vaddr + s.filesz ≤ (bndOf o st g).top := by
  have hsg : (layPre o st g).segs = ((layPre o st g).pst.segs.push (layPre o st g).pst.seg).toList := rfl
  rw [hsg, Array.toList_push, List.mem_append, List.mem_singleton] at hs
  have hi := hf.pinv
  have := hf.va
  have hsv := hi.sv; have hd := hi.diff; have hfe := hi.fe; have hso := hi.so
  rcases hs with hs | rfl
  · have h1 := hi.last s hs
    have h2 := (hi.segsOk s hs).2.1
    have : s.vaddr + s.memsz ≤ (layPre o st g).pst.segVa := by
      have := Nat.div_mul_le_self (layPre o st g).pst.segVa 65536
      have := Nat.lt_div_mul_add (a := s.vaddr + s.memsz + 65535) (b := 65536) (by decide)
      have : (s.vaddr + s.memsz + 65535) / 65536 * 65536 ≤ (layPre o st g).pst.segVa / 65536 * 65536 :=
        Nat.mul_le_mul_right _ h1
      omega
    omega
  · simp only [PSt.seg]; omega

theorem lookup_mem {l : List (String × Option Nat)} {a : String} {b : Option Nat} :
    l.lookup a = some b → (a, b) ∈ l := by
  induction l with
  | nil => intro h; cases h
  | cons p l ih =>
    intro h
    obtain ⟨k, v⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk; cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem lastSeg_mem (o : Opts) (st : St) (g : GcOut) (d : Seg) :
    (layPre o st g).segs.getLastD d ∈ (layPre o st g).segs := by
  have hsg : (layPre o st g).segs = ((layPre o st g).pst.segs.push (layPre o st g).pst.seg).toList := rfl
  rw [hsg, Array.toList_push, List.getLastD_eq_getLast?, List.getLast?_append]
  simp

theorem arrBound_le (hf : LFacts o st g) (k : String) (e : Bool) :
    (layPre o st g).arrBound k e ≤ (bndOf o st g).top := by
  have hl := segs_le hf (lastSeg_mem o st g default)
  unfold Lay.arrBound
  dsimp only
  split
  · rename_i a b hab; have := outRange_le hf hab; split <;> omega
  · exact hl.2

theorem synthTable_le (hf : LFacts o st g) (hb : o.base ≤ (bndOf o st g).top) :
    ∀ e ∈ (layPre o st g).synthTable o, ∀ v, e.2 = some v → v ≤ (bndOf o st g).top := by
  have hl := segs_le hf (lastSeg_mem o st g default)
  have htext : (((layPre o st g).segs.find? (·.kind == 1)).map fun s => s.vaddr + s.memsz).getD 0 ≤
      (bndOf o st g).top := by
    cases hfd : (layPre o st g).segs.find? (·.kind == 1) with
    | none => exact Nat.zero_le _
    | some s => exact (segs_le hf (List.mem_of_find?_eq_some hfd)).1
  have hbss : ((layPre o st g).outRange ".bss").elim
      (((layPre o st g).segs.getLastD default).vaddr + ((layPre o st g).segs.getLastD default).filesz) (·.1) ≤
      (bndOf o st g).top := by
    cases hb2 : (layPre o st g).outRange ".bss" with
    | none => exact hl.2
    | some ab => exact (outRange_le hf hb2).1
  intro e he v hv
  unfold Lay.synthTable at he
  generalize (layPre o st g).segs.getLastD default = ls at hl hbss he
  generalize (((layPre o st g).segs.find? (·.kind == 1)).map fun s => s.vaddr + s.memsz).getD 0 = te at htext he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> simp only [Option.some.injEq] at hv
  · subst hv; exact arrBound_le hf _ _
  · subst hv; exact arrBound_le hf _ _
  · subst hv; exact arrBound_le hf _ _
  · subst hv; exact arrBound_le hf _ _
  · subst hv; exact arrBound_le hf _ _
  · subst hv; exact arrBound_le hf _ _
  · subst hv; exact hl.1
  · subst hv; exact hl.1
  · subst hv; exact hl.1
  · subst hv; exact htext
  · subst hv; exact htext
  · subst hv; exact htext
  · subst hv; exact hl.2
  · subst hv; exact hl.2
  · subst hv; exact hbss
  · subst hv; exact hb
  · subst hv; exact hb
  · subst hv; exact partAddr_le hf _
  · exact partAddr_some hf hv
  · exact partAddr_some hf hv

theorem synth_le (hf : LFacts o st g) {n : String} {v : Nat} (h : (layPre o st g).synth o n = some v)
    (hb : o.base ≤ (bndOf o st g).top) : v ≤ (bndOf o st g).top := by
  unfold Lay.synth at h
  split at h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
    exact (outRange_le hf hab).1
  split at h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
    exact (outRange_le hf hab).2
  unfold Lay.synthFixed at h
  rw [Option.join_eq_some_iff] at h
  exact synthTable_le hf hb _ (lookup_mem h) v rfl

end

/-! ## A symbol's value in its interval -/

/-- **A value in its kind's interval** (`tls1`: the TLS template's start). -/
def ValIn (B : Bnd) (tls1 : Nat) (k : Tgt) (S : Int) (uw : Bool) : Prop :=
  match k with
  | .tls _ => uw = false ∧ (tls1 : Int) ≤ S ∧ S ≤ tls1 + B.TD + B.TB
  | .weak => uw = true ∧ S = 0
  | k => uw = false ∧ ∀ lo hi, sIv B k = some (lo, hi) → lo ≤ S ∧ S ≤ hi

section
variable {o : Opts} {st : St} {g : GcOut}

theorem dOk_parts {D : LayD} {sorted : Array OSec} (h : dOkB D sorted = true) :
    (∀ (k : Nat × Nat × Nat) (v : Nat), D.pieceOut[k]? = some v → v ≤ D.ehTotal) ∧
    (∀ (k : Nat × Nat) (v : Nat), D.ehStart[k]? = some v → v ≤ D.ehTotal) ∧
    (∀ (k : String) (v : Nat), D.gotSlot[k]? = some v → v < D.gotSyms.size) ∧
    (∀ e ∈ D.ehs, e.out + e.piece.size ≤ D.ehTotal) := by
  simp only [dOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := h
  exact ⟨fun k v hk => h1 (k, v) (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hk),
    fun k v hk => h2 (k, v) (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hk),
    fun k v hk => h3 (k, v) (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hk), h4⟩

/-- **A symbol's value lies in its kind's interval.** -/
theorem value_in (hf : LFacts o st g) (hd : dOkB (layDecide st g) (layPre o st g).sorted = true)
    (hb : o.base ≤ (bndOf o st g).top) {fi j : Nat} {k : Tgt}
    (hk : tgtOf st g (layPre o st g).sorted fi j = some k) {S : Int} {uw : Bool}
    (hv : (layPre o st g).value o st g fi j = .ok (S, uw)) :
    ValIn (bndOf o st g) (layPre o st g).pst.tls.1 k S uw := by
  obtain ⟨hpo, hes, -, -⟩ := dOk_parts hd
  have heh : (bndOf o st g).eh = (layDecide st g).ehTotal := rfl
  unfold tgtOf at hk
  unfold Lay.value at hv
  dsimp only at hk hv
  split at hk
  · rename_i t x tl htg
    rw [htg] at hv
    simp only at hv
    split at hk
    · rename_i hlive
      rw [if_pos hlive] at hv
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      split at hk
      · rename_i h1
        split at hk
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
          obtain ⟨⟨h2, hx⟩, hne⟩ := hc
          obtain ⟨y, -, -, ha, -, hsz, -, htop, himg, htls⟩ := secAddr_spec hf h1 h2 hne
          rw [getElem!_pos st.files[t.1].secs t.2 h2] at hx
          split at hk
          · rename_i hall
            cases hk
            refine ⟨rfl, fun lo hi hiv => ?_⟩
            simp only [sIv, Option.some.injEq, Prod.mk.injEq] at hiv
            obtain ⟨rfl, rfl⟩ := hiv
            have := himg hall
            rw [ha]
            constructor <;> push_cast <;> omega
          · split at hk
            · rename_i _ hall
              cases hk
              obtain ⟨e1, e2⟩ := htls hall
              refine ⟨rfl, ?_, ?_⟩ <;> rw [ha] <;> push_cast <;> omega
            · cases hk
        · cases hk
      · cases hk
    · rename_i hlive
      rw [if_neg hlive] at hv
      split at hk
      · cases hk
        refine ⟨?_, fun lo hi hiv => ?_⟩
        · split at hv
          · split at hv
            · split at hv <;> (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv; exact hv.2.symm)
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv; exact hv.2.symm
          · cases hv
        · simp only [sIv, Option.some.injEq, Prod.mk.injEq] at hiv
          obtain ⟨rfl, rfl⟩ := hiv
          have hea := partAddr_le hf "eh"
          split at hv
          · rename_i ei hei
            split at hv
            · rename_i p hp
              have hpx := Array.find?_some hp
              simp only [decide_eq_true_eq] at hpx
              split at hv
              · rename_i q hq
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
                obtain ⟨rfl, -⟩ := hv
                have := hpo _ _ hq
                unfold Lay.ehAddr; push_cast; constructor <;> omega
              · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
                obtain ⟨rfl, -⟩ := hv
                have : (layPre o st g).ehStart.getD (t.1, ei) 0 ≤ (layDecide st g).ehTotal := by
                  rw [Std.HashMap.getD_eq_getD_getElem?]
                  cases hs : (layPre o st g).ehStart[(t.1, ei)]? with
                  | none => exact Nat.zero_le _
                  | some v => exact hes _ _ hs
                unfold Lay.ehAddr; push_cast; constructor <;> omega
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
              obtain ⟨rfl, -⟩ := hv
              have : (layPre o st g).ehStart.getD (t.1, ei) 0 ≤ (layDecide st g).ehTotal := by
                rw [Std.HashMap.getD_eq_getD_getElem?]
                cases hs : (layPre o st g).ehStart[(t.1, ei)]? with
                | none => exact Nat.zero_le _
                | some v => exact hes _ _ hs
              unfold Lay.ehAddr; push_cast; constructor <;> omega
          · cases hv
      · cases hk
  · rename_i v htg
    rw [htg] at hv
    cases hk
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ⟨rfl, fun lo hi hiv => ?_⟩
    simp only [sIv, Option.some.injEq, Prod.mk.injEq] at hiv
    obtain ⟨rfl, rfl⟩ := hiv
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  · rename_i f k' htg
    rw [htg] at hv
    cases hk
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ⟨rfl, fun lo hi hiv => ?_⟩
    simp only [sIv, Option.some.injEq, Prod.mk.injEq] at hiv
    obtain ⟨rfl, rfl⟩ := hiv
    have := commonAddr_le hf (f, k')
    push_cast; constructor <;> omega
  · rename_i n w htg
    rw [htg] at hv
    simp only at hv
    split at hk
    · rename_i hsy
      cases hk
      have hs := synth_some (L := layPre o st g) (o := o) (n := n)
        (by rw [layPre_outs]; exact hsy)
      split at hv
      · rename_i v hv'
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        refine ⟨rfl, fun lo hi hiv => ?_⟩
        simp only [sIv, Option.some.injEq, Prod.mk.injEq] at hiv
        obtain ⟨rfl, rfl⟩ := hiv
        have := synth_le hf hv' hb
        push_cast; constructor <;> omega
      · rename_i hn; rw [hn] at hs; cases hs
    · split at hk
      · rename_i hsy hw
        cases hk
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
        rw [synth_none hw.2] at hv
        · simp only at hv
          rw [if_pos hw.1] at hv
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨rfl, rfl⟩ := hv
          exact ⟨rfl, rfl⟩
      · cases hk

/-- **A value in a placed section** is the section's address plus the offset. -/
theorem value_img (hf : LFacts o st g) {fi j : Nat} {t : SecId} {x : Nat}
    (hk : tgtOf st g (layPre o st g).sorted fi j = some (.img t x)) {S : Int} {uw : Bool}
    (hv : (layPre o st g).value o st g fi j = .ok (S, uw)) :
    ∃ h1 : t.1 < st.files.size, ∃ h2 : t.2 < st.files[t.1].secs.size,
      S = ((layPre o st g).secAddr[t.1]![t.2]! + x : Nat) ∧ x ≤ st.files[t.1].secs[t.2].size ∧
      (bndOf o st g).base ≤ (layPre o st g).secAddr[t.1]![t.2]! ∧
      (layPre o st g).secAddr[t.1]![t.2]! + st.files[t.1].secs[t.2].size ≤ (bndOf o st g).top ∧
      (layPre o st g).secAddr[t.1]![t.2]! % max (max st.files[t.1].secs[t.2].align 1) 1 = 0 := by
  unfold tgtOf at hk
  unfold Lay.value at hv
  dsimp only at hk hv
  split at hk
  · rename_i t' x' tl htg
    rw [htg] at hv
    simp only at hv
    split at hk
    · rename_i hlive
      rw [if_pos hlive] at hv
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      split at hk
      · rename_i h1
        split at hk
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
          obtain ⟨⟨h2, hx⟩, hne⟩ := hc
          obtain ⟨y, -, -, ha, -, hsz, hal, htop, himg, -⟩ := secAddr_spec hf h1 h2 hne
          rw [getElem!_pos st.files[t'.1].secs t'.2 h2] at hx
          split at hk
          · rename_i hall
            simp only [Option.some.injEq, Tgt.img.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            refine ⟨h1, h2, rfl, hx, ?_, ?_, ?_⟩ <;> rw [ha]
            · exact himg hall
            · rw [← hsz]; exact htop
            · exact hal
          · split at hk <;> cases hk
        · cases hk
      · cases hk
    · split at hk <;> cases hk
  · cases hk
  · cases hk
  · split at hk
    · cases hk
    · split at hk <;> cases hk

end

/-! ## The relocation checks -/

/-- Types whose value `relocVal` never rejects. -/
def freeTy (ty : Nat) : Bool :=
  [0, 257, 260, 263, 264, 265, 266, 267, 268, 269, 276, 277, 278, 284, 285, 286, 299, 312, 542, 551,
    563, 564, 569].contains ty

/-- Types whose value and place must lie in `[0, 2 ^ 31)`. -/
def farTy (ty : Nat) : Bool := [258, 261, 275, 311].contains ty

/-- PC-relative branches and `adr`: their ranges. -/
def nearRange (ty : Nat) : Option Int :=
  if ty == 274 || ty == 280 then some (2 ^ 20) else if ty == 279 then some (2 ^ 15)
  else if ty == 282 || ty == 283 then some (2 ^ 27) else none

/-- TLS types: their bounds on the thread-pointer offset. -/
def tlsRange (ty : Nat) : Option Int :=
  if ty == 541 || ty == 562 then some (2 ^ 32) else if ty == 549 then some (2 ^ 24)
  else if ty == 550 then some 4096 else none

/-- A section's address is a multiple of 4 (its alignment is). -/
def al4B (files : Array Obj) (t : SecId) : Bool := max (max files[t.1]!.secs[t.2]!.align 1) 1 % 4 == 0

/-- **A relocation's checks**, without addresses: `ty` its type, `k` its symbol's kind, `A` its
addend, its place in `[pLo, pHi]`; `same`: the place's section and offset (an input section's
relocation); `pal4`: the place is a multiple of 4. -/
def relCheckB (B : Bnd) (al4 : SecId → Bool) (ty : Nat) (k : Tgt) (A : Int) (pLo pHi : Int)
    (same : Option (SecId × Nat)) (pal4 : Bool) : Bool :=
  if freeTy ty then true
  else if farTy ty then
    (match k with | .tls _ => false | _ => true) &&
    (match sIv B k with | some (lo, hi) => decide (0 ≤ lo + A ∧ hi + A < 2 ^ 31) | none => false) &&
    decide (0 ≤ pLo ∧ pHi < 2 ^ 31) &&
    (ty != 311 || decide (0 ≤ A ∧ (B.top : Int) + 8 * B.got + A < 2 ^ 31))
  else match nearRange ty with
  | some R =>
    let al := ty == 282 || ty == 283
    match k with
    | .weak => true
    | .img t x =>
      match same with
      | some (s, off) =>
        if s = t then decide (-R ≤ x + A - off ∧ x + A - off < R) && (!al || (x + A - off) % 4 == 0)
        else al && decide (-R ≤ B.base + A - pHi ∧ B.top + A - pLo < R ∧ (B.base : Int) ≤ pLo) &&
          al4 t && x % 4 == 0 && A % 4 == 0 && pal4
      | none => al && decide (-R ≤ B.base + A - pHi ∧ B.top + A - pLo < R ∧ (B.base : Int) ≤ pLo) &&
          al4 t && x % 4 == 0 && A % 4 == 0 && pal4
    | _ => false
  | none =>
    match tlsRange ty with
    | some R =>
      (match k with | .tls _ => true | _ => false) && decide (0 ≤ 16 + A ∧ 16 + 2 * (B.TD : Int) + B.TB + A < R)
    | none => false

/-- The value `relIn` resolves for a symbol of value `S` (`uw`: undefined weak). -/
def adjS (ty : Nat) (S : Int) (uw : Bool) (A P : Int) : Int :=
  if uw && branchType ty then P + 4 - A else if uw && (ty == 275 || ty == 274) then P - A else S

theorem page_div {x P : Int} (hx : 0 ≤ x ∧ x < 2 ^ 31) (hP : 0 ≤ P ∧ P < 2 ^ 31) :
    -2 ^ 20 ≤ (page x - page P) / 4096 ∧ (page x - page P) / 4096 < 2 ^ 20 := by
  unfold page; omega

/-- **The checks are sound**: a relocation passing `relCheckB`, its symbol's value in its
kind's interval, its place in `[pLo, pHi]`, its GOT slot in `[0, top + 8 got]`, the TLS base in
`[16, 16 + TD]`, has a value in its type's range. -/
theorem relocOkB_of {B : Bnd} {al4 : SecId → Bool} {ty : Nat} {k : Tgt} {A pLo pHi : Int}
    {same : Option (SecId × Nat)} {pal4 : Bool} (hc : relCheckB B al4 ty k A pLo pHi same pal4 = true)
    {S P G tpb : Int} {tls1 : Nat} {uw : Bool} (hval : ValIn B tls1 k S uw) (hP : pLo ≤ P ∧ P ≤ pHi)
    (hG : 0 ≤ G ∧ G ≤ B.top + 8 * B.got) (htpb : 16 ≤ tpb ∧ tpb ≤ 16 + B.TD)
    (hsec : ∀ t x, k = .img t x → ∃ sa : Int, S = sa + x ∧ B.base ≤ sa ∧ sa + x ≤ B.top ∧
      (al4 t = true → sa % 4 = 0) ∧ ∀ off, same = some (t, off) → P = sa + off)
    (hp4 : pal4 = true → P % 4 = 0) :
    relocOkB ty { S := adjS ty S uw A P, A, P, G, tp := tpb + (adjS ty S uw A P + A - tls1) } = true := by
  unfold relCheckB at hc
  split at hc
  · rename_i hf
    simp only [freeTy, List.contains_iff_mem, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  split at hc
  · rename_i _ hfar
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.or_eq_true] at hc
    obtain ⟨⟨⟨hk, hiv⟩, hp⟩, h311⟩ := hc
    simp only [farTy, List.contains_iff_mem, List.mem_cons, List.mem_nil_iff, or_false] at hfar
    -- the value: S, or for 275 of a weak symbol the place
    have hS : ∀ lo hi, sIv B k = some (lo, hi) → (ty ≠ 275 ∨ uw = false) →
        lo ≤ adjS ty S uw A P ∧ adjS ty S uw A P ≤ hi := by
      intro lo hi hlh h275
      have hbt : branchType ty = false := by
        rcases hfar with rfl | rfl | rfl | rfl <;> rfl
      cases k with
      | tls _ => cases hk
      | weak =>
        obtain ⟨rfl, rfl⟩ := hval
        simp only [sIv, Option.some.injEq, Prod.mk.injEq] at hlh
        obtain ⟨rfl, rfl⟩ := hlh
        rcases h275 with h | h
        · have h274 : ty ≠ 274 := by
            intro e; subst e; omega
          simp [adjS, hbt, h, h274]
        · cases h
      | _ =>
        obtain ⟨rfl, hv⟩ := hval
        simp only [adjS, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hv lo hi hlh
    revert hiv
    split
    · rename_i lo hi hlh
      intro hiv
      simp only [decide_eq_true_eq] at hiv
      rcases hfar with rfl | rfl | rfl | rfl
      · have := hS lo hi hlh (.inl (by decide)); simp only [relocOkB, decide_eq_true_eq]; omega
      · have := hS lo hi hlh (.inl (by decide)); simp only [relocOkB, decide_eq_true_eq]; omega
      · simp only [relocOkB, decide_eq_true_eq]
        by_cases hw : uw = true
        · subst hw
          have : adjS 275 S true A P = P - A := by simp [adjS, branchType]
          rw [this]; exact page_div (by omega) (by omega)
        · have := hS lo hi hlh (.inr (by simpa using hw))
          exact page_div (by omega) (by omega)
      · simp only [relocOkB, decide_eq_true_eq]
        have := h311.resolve_left (by decide)
        exact page_div (by omega) (by omega)
    · intro h; cases h
  split at hc
  · rename_i _ _ R hR
    unfold nearRange at hR
    have hty : ((ty = 274 ∨ ty = 280) ∧ R = 2 ^ 20) ∨ (ty = 279 ∧ R = 2 ^ 15) ∨
        ((ty = 282 ∨ ty = 283) ∧ R = 2 ^ 27) := by
      split at hR
      · rename_i h; simp only [Option.some.injEq] at hR; simp only [Bool.or_eq_true, beq_iff_eq] at h
        exact .inl ⟨h, hR.symm⟩
      split at hR
      · rename_i h; simp only [Option.some.injEq] at hR; simp only [beq_iff_eq] at h
        exact .inr (.inl ⟨h, hR.symm⟩)
      split at hR
      · rename_i h; simp only [Option.some.injEq] at hR; simp only [Bool.or_eq_true, beq_iff_eq] at h
        exact .inr (.inr ⟨h, hR.symm⟩)
      · cases hR
    cases k with
    | weak =>
      obtain ⟨rfl, rfl⟩ := hval
      rcases hty with ⟨h | h, rfl⟩ | ⟨h, rfl⟩ | ⟨h | h, rfl⟩ <;> subst h <;>
        simp [relocOkB, adjS, branchType] <;> omega
    | img t x =>
      dsimp only at hc
      obtain ⟨sa, hSe, hb, ht, ha4, hsame⟩ := hsec t x rfl
      obtain ⟨rfl, -⟩ := hval
      have hadj : adjS ty S false A P = S := by simp [adjS]
      rw [hadj]
      -- the distance and its alignment
      have key : -R ≤ S + A - P ∧ S + A - P < R ∧
          ((ty = 282 ∨ ty = 283) → (S + A - P) % 4 = 0) := by
        have cross : ((ty == 282 || ty == 283) && decide (-R ≤ B.base + A - pHi ∧ B.top + A - pLo < R ∧
            (B.base : Int) ≤ pLo) && al4 t && x % 4 == 0 && A % 4 == 0 && pal4) = true →
            -R ≤ S + A - P ∧ S + A - P < R ∧ ((ty = 282 ∨ ty = 283) → (S + A - P) % 4 = 0) := by
          intro hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨⟨⟨⟨hal, h1, h2, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
          have := ha4 h4; have := hp4 h7
          refine ⟨by omega, by omega, fun _ => by omega⟩
        cases hso : same with
        | none => rw [hso] at hc; exact cross hc
        | some so =>
          obtain ⟨s', off⟩ := so
          rw [hso] at hc
          simp only at hc
          by_cases hst : s' = t
          · subst hst
            rw [if_pos rfl] at hc
            have hPe := hsame off hso
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
              beq_iff_eq] at hc
            obtain ⟨⟨h1, h2⟩, h3⟩ := hc
            refine ⟨by omega, by omega, fun hal => ?_⟩
            rcases h3 with h3 | h3
            · rcases hal with rfl | rfl <;> simp at h3
            · have : S + A - P = x + A - off := by omega
              rw [this]; exact h3
          · rw [if_neg hst] at hc
            exact cross hc
      rcases hty with ⟨h | h, rfl⟩ | ⟨h, rfl⟩ | ⟨h | h, rfl⟩ <;> subst h <;>
        simp only [relocOkB, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] <;>
        first | omega | (exact ⟨by omega, key.2.2 (by simp)⟩)
    | _ => simp at hc
  · split at hc
    · rename_i _ _ _ R hR
      unfold tlsRange at hR
      cases k with
      | tls x =>
        obtain ⟨rfl, h1, h2⟩ := hval
        simp only [Bool.true_and, decide_eq_true_eq] at hc
        have hadj : adjS ty S false A P = S := by simp [adjS]
        rw [hadj]
        split at hR
        · rename_i h; simp only [Option.some.injEq] at hR; subst hR
          simp only [Bool.or_eq_true, beq_iff_eq] at h
          rcases h with rfl | rfl <;> simp only [relocOkB, decide_eq_true_eq] <;> omega
        split at hR
        · rename_i h; simp only [Option.some.injEq] at hR; subst hR
          simp only [beq_iff_eq] at h; subst h
          simp only [relocOkB, decide_eq_true_eq]; omega
        split at hR
        · rename_i h; simp only [Option.some.injEq] at hR; subst hR
          simp only [beq_iff_eq] at h; subst h
          simp only [relocOkB, decide_eq_true_eq]; omega
        · cases hR
      | _ => simp at hc
    · cases hc

/-! ## The pieces' relocations -/

theorem list_foldlM_inv {α β ε : Type} {f : β → α → Except ε β} {I : β → Prop} {l : List α}
    (hstep : ∀ b a b', a ∈ l → I b → f b a = .ok b' → I b') :
    ∀ (init res : β), I init → l.foldlM f init = .ok res → I res := by
  induction l with
  | nil => intro init res hi h; cases h; exact hi
  | cons a l ih =>
    intro init res hi h
    rw [List.foldlM_cons] at h
    cases h1 : f init a with
    | error e => rw [h1] at h; cases h
    | ok b =>
      rw [h1] at h
      exact ih (fun b x b' hx => hstep b x b' (List.mem_cons_of_mem _ hx)) b res
        (hstep init a b (List.mem_cons_self ..) hi h1) h

theorem array_foldlM_inv {α β ε : Type} {f : β → α → Except ε β} {I : β → Prop} {l : Array α}
    (hstep : ∀ b a b', a ∈ l → I b → f b a = .ok b' → I b') (init res : β) (hi : I init)
    (h : l.foldlM f init = .ok res) : I res := by
  rw [← Array.foldlM_toList] at h
  exact list_foldlM_inv (fun b a b' ha => hstep b a b' (Array.mem_toList_iff.1 ha)) init res hi h

theorem place_size_ge {dest b : ByteArray} {o : Nat} (h : o ≤ dest.size) : dest.size ≤ (place dest o b).size := by
  have h' : o ≤ dest.data.size := h
  show dest.data.size ≤ (place dest o b).data.size
  simp only [place, ByteArray.copySlice, Array.size_append, Array.size_extract]
  omega

/-- A relocation of the output `.eh_frame`: a kept record's relocation at its place. -/
def EhRelOf (L : Lay) (o : Opts) (st : St) (g : GcOut) (rel : Rel) : Prop :=
  ∃ e ∈ L.ehs.toList, ∃ r ∈ (ehRelas g e).toList, rel.off = e.out + (r.off - e.piece.off) ∧ rel.ty = r.type ∧
    L.relIn o st g e.file r (L.ehAddr + e.out + (r.off - e.piece.off)) = .ok rel.ri

/-- **The output `.eh_frame`**: at least its size, its relocations the kept records'. -/
theorem ehOut_spec {L : Lay} {o : Opts} {st : St} {g : GcOut} (hout : ∀ e ∈ L.ehs, e.out ≤ L.ehTotal)
    {res : ByteArray × Array Rel × Array (Nat × Nat)} (h : L.ehOut o st g = .ok res) :
    L.ehTotal ≤ res.1.size ∧ ∀ rel ∈ res.2.1.toList, EhRelOf L o st g rel := by
  unfold Lay.ehOut at h
  refine array_foldlM_inv (I := fun acc => L.ehTotal ≤ acc.1.size ∧ ∀ rel ∈ acc.2.1.toList, EhRelOf L o st g rel)
    (fun acc e acc' he hi hstep => ?_) _ _ ⟨by simp [ByteArray.size], by simp⟩ h
  unfold Lay.ehRec at hstep
  split at hstep
  · simp only [pure, Except.pure, Except.ok.injEq] at hstep; subst hstep; exact hi
  · rename_i es hes
    simp only [bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i rt hrt
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      refine ⟨Nat.le_trans hi.1 (place_size_ge (Nat.le_trans (hout e he) hi.1)), ?_⟩
      refine array_foldlM_inv (I := fun a => ∀ rel ∈ a.1.toList, EhRelOf L o st g rel)
        (fun b r b' hr hb hst => ?_) _ _ hi.2 hrt
      unfold Lay.ehRel at hst
      simp only [bind, Except.bind] at hst
      split at hst
      · cases hst
      · rename_i ri hri
        have hnew : ∀ rel ∈ (b.1.push { off := e.out + (r.off - e.piece.off), ty := r.type, ri }).toList,
            EhRelOf L o st g rel := by
          intro rel hrel
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrel
          rcases hrel with hrel | rfl
          · exact hb rel hrel
          · exact ⟨e, Array.mem_toList_iff.2 he, r, by unfold ehRelas; rw [hes]; exact Array.mem_toList_iff.2 hr,
              rfl, rfl, hri⟩
        split at hst
        · split at hst
          · cases hst
          · simp only [pure, Except.pure, Except.ok.injEq] at hst; subst hst; exact hnew
        · simp only [pure, Except.pure, Except.ok.injEq] at hst; subst hst; exact hnew

theorem mod4_of {a m : Nat} (h1 : a % m = 0) (h2 : m % 4 = 0) : a % 4 = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h2) (Nat.dvd_of_mod_eq_zero h1))

section
variable {o : Opts} {st : St} {g : GcOut}

/-- **A resolved relocation passing the checks is in its type's range.** -/
theorem relIn_relocOkB (hf : LFacts o st g) (hd : dOkB (layDecide st g) (layPre o st g).sorted = true)
    {fi : Nat} {r : Rela} {P : Nat} {ri : RelIn} (h : (layPre o st g).relIn o st g fi r P = .ok ri)
    {k : Tgt} (hk : tgtOf st g (layPre o st g).sorted fi r.sym = some k) {pLo pHi : Int}
    {same : Option (SecId × Nat)} {pal4 : Bool}
    (hc : relCheckB (bndOf o st g) (al4B st.files) r.type k r.addend pLo pHi same pal4 = true)
    (hP : pLo ≤ P ∧ P ≤ pHi)
    (hsame : ∀ t off, same = some (t, off) → P = (layPre o st g).secAddr[t.1]![t.2]! + off)
    (hp4 : pal4 = true → P % 4 = 0) : relocOkB r.type ri = true := by
  have hb : o.base ≤ (bndOf o st g).top := by show o.base ≤ o.base + _ + _; omega
  obtain ⟨-, -, hgs, -⟩ := dOk_parts hd
  unfold Lay.relIn at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i Su hv
  obtain ⟨S, uw⟩ := Su
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hval := value_in hf hd hb hk hv
  -- the GOT slot's address
  have hG : (0 : Int) ≤ (((layPre o st g).gotSlot[gotKey st.files fi r.sym]?.map fun k =>
      ((layPre o st g).partAddr.getD "got" 0 + 8 * k : Nat)).getD 0 : Nat) ∧
      ((((layPre o st g).gotSlot[gotKey st.files fi r.sym]?.map fun k =>
      ((layPre o st g).partAddr.getD "got" 0 + 8 * k : Nat)).getD 0 : Nat) : Int) ≤
        (bndOf o st g).top + 8 * (bndOf o st g).got := by
    refine ⟨by omega, ?_⟩
    cases hgk : (layPre o st g).gotSlot[gotKey st.files fi r.sym]? with
    | none => simp; omega
    | some k' =>
      have := hgs _ _ hgk
      have := partAddr_le hf "got"
      have hgot : (bndOf o st g).got = (layDecide st g).gotSyms.size := rfl
      simp only [Option.map_some, Option.getD_some]
      push_cast; omega
  have htpb : (16 : Int) ≤ (alignUp 16 (layPre o st g).pst.tls.2.2.2.2 : Nat) ∧
      ((alignUp 16 (layPre o st g).pst.tls.2.2.2.2 : Nat) : Int) ≤ 16 + (bndOf o st g).TD := by
    have h1 := le_alignUp 16 (layPre o st g).pst.tls.2.2.2.2
    have h2 := alignUp_le 16 (layPre o st g).pst.tls.2.2.2.2
    have h3 := (hf.ti.start rfl).2.2
    constructor <;> push_cast <;> omega
  have := relocOkB_of hc hval hP hG htpb
    (fun t x hkt => ?_) (fun h4 => by have := hp4 h4; omega)
  · exact this
  · subst hkt
    obtain ⟨h1, h2, hS, hx, hb', htop, hal⟩ := value_img hf hk hv
    refine ⟨((layPre o st g).secAddr[t.1]![t.2]! : Int), by rw [hS]; push_cast; rfl, by exact_mod_cast hb',
      by have := hx; push_cast; omega, fun ha => ?_, fun off hso => by rw [hsame t off hso]; push_cast; rfl⟩
    simp only [al4B, beq_iff_eq, getElem!_pos st.files t.1 h1, getElem!_pos st.files[t.1].secs t.2 h2] at ha
    have := mod4_of hal ha
    omega

end

end Link.Ld

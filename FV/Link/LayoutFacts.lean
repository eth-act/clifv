import FV.Link.Layout
import FV.Backend.Proof.EncodeLayout

/-! # Facts about the placement (L2b, `FV/Link/Layout.lean`)

What the placement gives, for the proofs that the Lean linker's output satisfies the linker's
facts (`FV/Link/LayoutProof.lean`) and the code part of `BinOk` (`FV/Link/ImageProof.lean`):

* `pipeT_layout`: a successful pipeline's artifact is the layout of its assembly, at its base.
* `offs_getElem!`, `offs_sep`, `offs_end`: the offsets are the spans of the preceding functions;
  each function's words and its gap word end before the next function and within the region.
* `offsA_ge`, `offsA_sep`, `offsA_end`, `offsA_mod4`, `offsA_aligned`: the same for the aligned
  offsets (#1061), each a multiple of its alignment; `offsA_nil`, `endA_nil`: without
  alignments they are `offs` and `span`.
* `nodupB_sound`: the hash-set duplicate check decides `Nodup`.
* `PlaceOk`, `placeOk_of`: `placeOkB` unfolded.
* `baseOf_name`, `addrs_name`: with `placeOkB`, the load and link-map address of the `i`-th
  placed function is `R + offsA_i`.
* `tab_length`, `names_getElem!`, `tab_placed`: the compiled table consists of the placed
  functions, with the placement's names and sizes.
-/

namespace Link

open E2E E2E.LinkCheck Backend

/-! ## The pipeline -/

/-- A successful pipeline's artifact: the layout of its assembly and its load address. -/
theorem pipeT_layout {f : Clif.Function} {k : Nat} {b : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeT f k b o = .ok a) : a.fa.layout = .ok a.fb ∧ a.base = b := by
  unfold pipeT pipeTWithLowering at h
  simp only [id] at h
  rw [Backend.Stock.D0.defaultLower_eq_legacy] at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare vc with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h3] at h
  · cases h
  rcases h4 : emitFunc k af with _ | fa <;> simp only [h4] at h
  · cases h
  rcases h5 : fa.layout with _ | fb <;> simp only [h5] at h
  · cases h
  cases h
  exact ⟨h5, rfl⟩

/-! ## Offsets -/

theorem span_cons (n : Nat) (ns : List Nat) : span (n :: ns) = 4 * n + 4 + span ns := by
  simp [span]

theorem span_append (l₁ l₂ : List Nat) : span (l₁ ++ l₂) = span l₁ + span l₂ := by
  simp [span]

theorem offs_length : ∀ (ns : List Nat) (o : Nat), (offs ns o).length = ns.length
  | [], _ => rfl
  | _ :: ns, _ => by simp [offs, offs_length ns]

/-- The offset of the `i`-th function: `o` plus the span of the preceding ones. -/
theorem offs_getElem! : ∀ {ns : List Nat} {o i : Nat}, i < ns.length →
    (offs ns o)[i]! = o + span (ns.take i)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | n :: ns, o, 0, _ => by simp [offs, span]
  | n :: ns, o, i + 1, h => by
    have ih := offs_getElem! (ns := ns) (o := o + 4 * n + 4) (i := i) (by simp at h; omega)
    simp only [offs, List.take_succ_cons, span_cons]
    simp only [getElem!_def, List.getElem?_cons_succ] at ih ⊢
    rw [ih]
    omega

theorem span_take_succ {ns : List Nat} {i : Nat} (h : i < ns.length) :
    span (ns.take (i + 1)) = span (ns.take i) + 4 * ns[i]! + 4 := by
  rw [List.take_add_one, span_append, List.getElem?_eq_getElem h, getElem!_pos ns i h]
  simp [span]
  omega

theorem span_take_le (ns : List Nat) (i : Nat) : span (ns.take i) ≤ span ns := by
  conv => rhs; rw [← List.take_append_drop i ns]
  rw [span_append]
  omega

theorem span_take_mono {ns : List Nat} {i j : Nat} (h : i ≤ j) :
    span (ns.take i) ≤ span (ns.take j) := by
  have := span_take_le (ns.take j) i
  rwa [List.take_take, Nat.min_eq_left h] at this

/-- **The functions do not overlap**: the `i`-th function's words and gap word end before the
`i'`-th function. -/
theorem offs_sep {ns : List Nat} {o i i' : Nat} (hi : i < i') (hi' : i' < ns.length) :
    (offs ns o)[i]! + 4 * ns[i]! + 4 ≤ (offs ns o)[i']! := by
  rw [offs_getElem! (by omega), offs_getElem! hi', Nat.add_assoc, Nat.add_assoc,
    ← Nat.add_assoc (span _), ← span_take_succ (by omega)]
  have := span_take_mono (ns := ns) (show i + 1 ≤ i' by omega)
  omega

/-- **The functions are in the region**: the `i`-th function's words and gap word end within
`span ns` of `o`. -/
theorem offs_end {ns : List Nat} {o i : Nat} (hi : i < ns.length) :
    (offs ns o)[i]! + 4 * ns[i]! + 4 ≤ o + span ns := by
  rw [offs_getElem! hi, Nat.add_assoc, Nat.add_assoc, ← Nat.add_assoc (span _),
    ← span_take_succ hi]
  have := span_take_le ns (i + 1)
  omega

/-- Every offset is a multiple of 4 (from a multiple of 4). -/
theorem offs_mod4 {ns : List Nat} {o i : Nat} (ho : o % 4 = 0) (hi : i < ns.length) :
    (offs ns o)[i]! % 4 = 0 := by
  rw [offs_getElem! hi]
  have : ∀ l : List Nat, span l % 4 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons n l ih => rw [span_cons]; omega
  have := this (ns.take i)
  omega

/-! ## Aligned offsets (#1061) -/

theorem alignW_ge (o a : Nat) : o ≤ alignW o a := by
  unfold alignW; omega

theorem alignW_mod4 (o a : Nat) : alignW o a % 4 = o % 4 := by
  unfold alignW; omega

theorem alignW_four (o : Nat) : alignW o 4 = o := by
  unfold alignW; omega

/-- **A word-aligned offset rounded to an alignment `a` (a positive multiple of a word) is a
multiple of `a`.** -/
theorem alignW_dvd {o a : Nat} (ho : o % 4 = 0) (ha : a % 4 = 0) (hpos : 0 < a) :
    alignW o a % a = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, o = 4 * q := ⟨o / 4, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, a = 4 * w := ⟨a / 4, by omega⟩
  have hw : 0 < w := by omega
  have e1 : 4 * q / 4 = q := by omega
  have e2 : 4 * w / 4 = w := by omega
  simp only [alignW, e1, e2]
  rw [show 4 * q + 4 * ((w - q % w) % w) = 4 * (q + (w - q % w) % w) by omega,
    Nat.mul_mod_mul_left]
  have hr := Nat.mod_lt q hw
  have hd := Nat.mod_add_div q w
  by_cases h0 : q % w = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.add_zero, h0]
  · rw [Nat.mod_eq_of_lt (show w - q % w < w by omega)]
    have : q + (w - q % w) = w * (q / w + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.mul_mod_right]

theorem offsA_length : ∀ (ns as : List Nat) (o : Nat), (offsA ns as o).length = ns.length
  | [], _, _ => rfl
  | _ :: ns, as, _ => by simp [offsA, offsA_length ns]

theorem endA_ge : ∀ (ns as : List Nat) (o : Nat), o ≤ endA ns as o
  | [], _, _ => Nat.le_refl _
  | n :: ns, as, o => by
    have := endA_ge ns as.tail (alignW o (as.headD 4) + 4 * n + 4)
    have := alignW_ge o (as.headD 4)
    simp only [endA]
    omega

theorem endA_mod4 : ∀ (ns as : List Nat) (o : Nat), o % 4 = 0 → endA ns as o % 4 = 0
  | [], _, _, h => h
  | n :: ns, as, o, h => by
    simp only [endA]
    exact endA_mod4 ns as.tail _ (by have := alignW_mod4 o (as.headD 4); omega)

/-- Every aligned offset is at least the start. -/
theorem offsA_ge : ∀ {ns as : List Nat} {o i : Nat}, i < ns.length → o ≤ (offsA ns as o)[i]!
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n :: ns, as, o, 0, _ => by
    simp only [offsA, List.getElem!_cons_zero]
    exact alignW_ge _ _
  | n :: ns, as, o, i + 1, h => by
    simp only [offsA, List.getElem!_cons_succ]
    have := offsA_ge (ns := ns) (as := as.tail) (o := alignW o (as.headD 4) + 4 * n + 4) (i := i)
      (by simp at h; omega)
    have := alignW_ge o (as.headD 4)
    omega

/-- **The aligned functions do not overlap**: the `i`-th function's words and gap word end
before the `i'`-th function. -/
theorem offsA_sep : ∀ {ns as : List Nat} {o i i' : Nat}, i < i' → i' < ns.length →
    (offsA ns as o)[i]! + 4 * ns[i]! + 4 ≤ (offsA ns as o)[i']!
  | [], _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, _, _, 0, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n :: ns, as, o, 0, i' + 1, _, h => by
    simp only [offsA, List.getElem!_cons_zero, List.getElem!_cons_succ]
    exact offsA_ge (by simp at h; omega)
  | n :: ns, as, o, i + 1, i' + 1, hi, h => by
    simp only [offsA, List.getElem!_cons_succ]
    exact offsA_sep (by omega) (by simp at h; omega)

/-- **The aligned functions are in the region**: the `i`-th function's words and gap word end
by `endA ns as o`. -/
theorem offsA_end : ∀ {ns as : List Nat} {o i : Nat}, i < ns.length →
    (offsA ns as o)[i]! + 4 * ns[i]! + 4 ≤ endA ns as o
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n :: ns, as, o, 0, _ => by
    simp only [offsA, endA, List.getElem!_cons_zero]
    exact endA_ge _ _ _
  | n :: ns, as, o, i + 1, h => by
    simp only [offsA, endA, List.getElem!_cons_succ]
    exact offsA_end (by simp at h; omega)

/-- Every aligned offset is a multiple of 4 (from a multiple of 4). -/
theorem offsA_mod4 : ∀ {ns as : List Nat} {o i : Nat}, o % 4 = 0 → i < ns.length →
    (offsA ns as o)[i]! % 4 = 0
  | [], _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n :: ns, as, o, 0, ho, _ => by
    simp only [offsA, List.getElem!_cons_zero]
    have := alignW_mod4 o (as.headD 4)
    omega
  | n :: ns, as, o, i + 1, ho, h => by
    simp only [offsA, List.getElem!_cons_succ]
    exact offsA_mod4 (by have := alignW_mod4 o (as.headD 4); omega) (by simp at h; omega)

/-- **Each function starts at its alignment** (#1061): the `i`-th aligned offset from a
multiple of 4 is a multiple of the `i`-th alignment, when that is a positive multiple of 4. -/
theorem offsA_aligned : ∀ {ns as : List Nat} {o i : Nat}, o % 4 = 0 → i < ns.length →
    as.getD i 4 % 4 = 0 → 0 < as.getD i 4 → (offsA ns as o)[i]! % as.getD i 4 = 0
  | [], _, _, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n :: ns, as, o, 0, ho, _, h4, hp => by
    simp only [offsA, List.getElem!_cons_zero]
    have e : as.getD 0 4 = as.headD 4 := by cases as <;> rfl
    rw [e] at h4 hp ⊢
    exact alignW_dvd ho h4 hp
  | n :: ns, as, o, i + 1, ho, h, h4, hp => by
    simp only [offsA, List.getElem!_cons_succ]
    have e : as.getD (i + 1) 4 = as.tail.getD i 4 := by cases as <;> simp
    rw [e] at h4 hp ⊢
    exact offsA_aligned (by have := alignW_mod4 o (as.headD 4); omega) (by simp at h; omega) h4 hp

/-- Without alignments the aligned offsets are `offs`. -/
theorem offsA_nil : ∀ (ns : List Nat) (o : Nat), offsA ns [] o = offs ns o
  | [], _ => rfl
  | n :: ns, o => by
    simp only [offsA, offs, List.headD_nil, List.tail_nil, alignW_four, offsA_nil ns]

/-- Without alignments the end is the start plus `span`. -/
theorem endA_nil : ∀ (ns : List Nat) (o : Nat), endA ns [] o = o + span ns
  | [], o => by simp [endA, span]
  | n :: ns, o => by
    simp only [endA, List.headD_nil, List.tail_nil, alignW_four, endA_nil ns, span_cons]
    omega

/-! ## Association lists -/

theorem lookup_getElem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {j : Nat} (hj : j < l.length), (l.map (·.1)).Nodup →
      l.lookup l[j].1 = some l[j].2
  | [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | (k, v) :: l, 0, _, _ => by simp
  | (k, v) :: l, j + 1, hj, hn => by
    have hj' : j < l.length := by simp at hj; omega
    simp only [List.map_cons, List.nodup_cons] at hn
    have hne : (l[j].1 == k) = false := beq_eq_false_iff_ne.2 fun e =>
      hn.1 (e ▸ List.mem_map.2 ⟨l[j], List.getElem_mem _, rfl⟩)
    simp only [List.getElem_cons_succ]
    rw [List.lookup_cons, hne]
    exact lookup_getElem hj' hn.2

theorem lookup_append_some {α β : Type} [BEq α] {l₁ l₂ : List (α × β)} {a : α} {b : β}
    (h : l₁.lookup a = some b) : (l₁ ++ l₂).lookup a = some b := by
  rw [List.lookup_append, h]
  rfl

/-! ## The placement's conditions -/

/-- `nodupGo` decides `Nodup`, of elements none of which is in the set. -/
theorem nodupGo_sound : ∀ {l : List String} {s : Std.HashSet String}, nodupGo l s = true →
    l.Nodup ∧ ∀ x ∈ l, s.contains x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil⟩
  | x :: xs, s, h => by
    simp only [nodupGo, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨ih1, ih2⟩ := nodupGo_sound h.2
    have hin : ∀ y ∈ xs, (x == y) = false ∧ s.contains y = false := fun y hy => by
      have := ih2 y hy
      rw [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
      exact this
    refine ⟨List.nodup_cons.2 ⟨fun hx => ?_, ih1⟩, fun y hy => ?_⟩
    · simpa using (hin x hx).1
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h.1
      · exact (hin y hy).2

theorem nodupB_sound {l : List String} (h : nodupB l = true) : l.Nodup := (nodupGo_sound h).1

/-- `placeOkB` unfolded. -/
structure PlaceOk (S : LinkSpec) : Prop where
  nodup : S.names.Nodup
  namesLen : S.names.length = S.funcs.length
  sizesLen : S.sizes.length = S.funcs.length
  sizesPos : ∀ n ∈ S.sizes, 0 < n
  pos : 0 < S.R
  align : S.R % 4 = 0
  fits : S.R + S.size < 2 ^ 64
  outside : ∀ e ∈ S.outside, e.2 % 2 ^ 64 < S.R ∨ S.R + S.size ≤ e.2 % 2 ^ 64

theorem placeOk_of {S : LinkSpec} (hp : S.placeOkB = true) : PlaceOk S := by
  simp only [LinkSpec.placeOkB, clearOfB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hp
  exact ⟨nodupB_sound h1, h2, h3, h4, h5, h6, h7, h8⟩

namespace LinkSpec

variable {S : LinkSpec}

@[simp] theorem input_funcs : S.input.funcs = S.funcs := rfl
@[simp] theorem input_addrs : S.input.addrs = S.addrs := rfl
@[simp] theorem input_aliases : S.input.aliases = [] := rfl
@[simp] theorem input_raStar : S.input.raStar = S.R + S.size := rfl
@[simp] theorem input_syms :
    S.input.syms = S.symNames.filterMap fun n => (S.addrs.lookup n).map (n, ·) := rfl

/-- The `i`-th placed function's offset, gap word included, ends within the region. -/
theorem off_end (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    (offsA S.sizes S.aligns 0)[i]! + 4 * S.sizes[i]! + 4 ≤ S.size :=
  offsA_end (by rw [hP.sizesLen]; exact hi)

/-- The `i`-th and `i'`-th placed functions (`i < i'`) do not overlap. -/
theorem off_sep (hP : PlaceOk S) {i i' : Nat} (hi : i < i') (hi' : i' < S.funcs.length) :
    (offsA S.sizes S.aligns 0)[i]! + 4 * S.sizes[i]! + 4 ≤ (offsA S.sizes S.aligns 0)[i']! :=
  offsA_sep hi (by rw [hP.sizesLen]; exact hi')

theorem names_nodup (hP : PlaceOk S) : S.names.Nodup := hP.nodup

/-- **The link map of a placed function**: its placed address. -/
theorem addrs_name (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    S.addrs.lookup S.names[i]! = some (S.R + (offsA S.sizes S.aligns 0)[i]!) := by
  have hl : i < S.progAddrs.length := by
    simp [progAddrs, offsA_length, hi, hP.sizesLen, hP.namesLen]
  have hm : S.progAddrs.map (·.1) = S.names := by
    rw [progAddrs]
    exact List.map_fst_zip (by simp [offsA_length, hP.sizesLen, hP.namesLen])
  have := lookup_getElem hl (hm ▸ names_nodup hP)
  have e1 : S.progAddrs[i].1 = S.names[i]! := by
    simp [progAddrs, getElem!_pos S.names i (by rw [hP.namesLen]; exact hi)]
  have e2 : S.progAddrs[i].2 = S.R + (offsA S.sizes S.aligns 0)[i]! := by
    simp [progAddrs, getElem!_pos (offsA S.sizes S.aligns 0) i
      (by simpa [offsA_length, hP.sizesLen] using hi)]
  rw [e1, e2] at this
  exact lookup_append_some this

/-- **The load address of a placed function** is its placed address. -/
theorem baseOf_name (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    S.input.baseOf S.names[i]! = S.R + (offsA S.sizes S.aligns 0)[i]! := by
  unfold LinkInput.baseOf LinkInput.addrOf
  simp only [input_aliases, List.lookup_nil, Option.getD_none, input_addrs, addrs_name hP hi,
    Option.getD_some]

end LinkSpec

/-! ## The compiled table -/

open LinkSpec

theorem tab_length (S : LinkSpec) :
    (tabOf S.input.resultsT).length = S.funcs.length := by
  simp [tabOf, LinkInput.resultsT]

/-- The `i`-th placed function's name is the placement's (`namesOkB`). -/
theorem names_getElem! {S : LinkSpec} (hn : S.namesOkB (tabOf S.input.resultsT) = true) {i : Nat}
    (hi : i < S.funcs.length) : S.names[i]! = S.funcs[i].func.name := by
  have hs' := congrArg (·[i]?) (of_decide_eq_true hn)
  simp only [tabOf, LinkInput.resultsT, input_funcs, List.map_map, List.getElem?_map,
    List.getElem?_take, hi, ite_true, List.getElem?_eq_getElem hi,
    Option.map_some, Function.comp_def] at hs'
  rw [getElem!_pos S.names i (List.getElem?_eq_some_iff.1 hs'.symm).1]
  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hs'.symm)

/-- The `i`-th entry of the compiled table: the `i`-th function of the input, compiled at its
load address (`hr`: the pipeline accepts every function). -/
theorem tab_entry {S : LinkSpec} (hr : S.input.resultsT.all (·.2.toBool) = true) {i : Nat}
    (hi : i < S.funcs.length) :
    ∃ fi a, S.funcs[i]? = some fi ∧
      pipeT fi.func fi.k (BitVec.ofNat 64 (S.input.baseOf fi.func.name)) (raJ fi.ra fi.j) =
        .ok a ∧ (tabOf S.input.resultsT)[i]? = some (fi.func, a) := by
  have hl : i < S.funcs.length := hi
  let fi := S.funcs[i]
  refine ⟨fi, getOk (pipeT fi.func fi.k (BitVec.ofNat 64 (S.input.baseOf fi.func.name))
    (raJ fi.ra fi.j)), List.getElem?_eq_getElem hl, ?_, ?_⟩
  · apply getOk_eq
    have hl' : i < S.input.resultsT.length := by simpa [LinkInput.resultsT] using hl
    have := List.all_eq_true.1 hr _ (List.getElem_mem hl')
    simpa only [LinkInput.resultsT, List.getElem_map, input_funcs] using this
  · simp only [tabOf, LinkInput.resultsT, input_funcs, List.map_map, List.getElem?_map,
      List.getElem?_eq_getElem hl]
    rfl

/-- **A placed function's entry**: the `i`-th function, at its placed address, with the
placement's name (`namesOkB`) and `sizes[i]` words (`sizesOkB`), compiled by the pipeline (its
layout). -/
theorem tab_placed {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) :
    ∀ i < S.funcs.length, ∃ e, (tabOf S.input.resultsT)[i]? = some e ∧
      e.2.base = BitVec.ofNat 64 (S.R + (offsA S.sizes S.aligns 0)[i]!) ∧
      e.2.fb.words.size = S.sizes[i]! ∧ e.1.name = S.names[i]! ∧
      e.2.fa.layout = .ok e.2.fb := by
  intro i hi
  have hP := placeOk_of hp
  obtain ⟨fi, a, hfi, ha, ht⟩ := tab_entry hr (i := i) (by omega)
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hfi
  subst hfi
  have hn := names_getElem! hn hi
  obtain ⟨hl, hb⟩ := pipeT_layout ha
  refine ⟨_, ht, ?_, ?_, hn.symm, hl⟩
  · rw [hb, ← hn, baseOf_name hP hi]
  · have hs' := congrArg (·[i]?) (of_decide_eq_true hs)
    simp only [List.getElem?_map, List.getElem?_take, hi, ite_true, ht, Option.map_some] at hs'
    have hi' : i < S.sizes.length := by rw [hP.sizesLen]; exact hi
    rw [getElem!_pos S.sizes i hi', ← Option.some.inj (hs'.trans (List.getElem?_eq_getElem hi'))]

end Link

import FV.Link.Layout
import FV.Backend.Proof.EncodeLayout

/-! # Facts about the placement (L2b, `FV/Link/Layout.lean`)

What the placement gives, for the proofs that the Lean linker's output satisfies the linker's
facts (`FV/Link/LayoutProof.lean`) and the code part of `BinOk` (`FV/Link/ImageProof.lean`):

* `pipeT_layout`: a successful pipeline's artifact is the layout of its assembly, at its base.
* `offs_getElem!`, `offs_sep`, `offs_end`: the offsets are the spans of the preceding functions;
  each function's words and its gap word end before the next function and within the region.
* `PlaceOk`, `placeOk_of`: `placeOkB` unfolded.
* `baseOf_name`, `baseOf_alias`: with `placeOkB`, the load address (`LinkInput.baseOf`) of the
  `i`-th placed function is `R + offs_i`; an alias's is its function's.
* `tab_length`, `tab_placed`, `tab_alias`: the compiled table (`tabOf S.input.resultsT`): the
  placed functions first, each at its placed address with `sizes[i]` words (`sizesOkB`), then
  the aliases, each at its function's address.
-/

namespace Link

open E2E E2E.LinkCheck Backend

/-! ## The pipeline -/

/-- A successful pipeline's artifact: the layout of its assembly and its load address. -/
theorem pipeT_layout {f : Clif.Function} {k : Nat} {b : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeT f k b o = .ok a) : a.fa.layout = .ok a.fb ∧ a.base = b := by
  unfold pipeT at h
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

theorem lookup_none {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α}, a ∉ l.map (·.1) → l.lookup a = none
  | [], _, _ => rfl
  | (k, v) :: l, a, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup_cons, beq_eq_false_iff_ne.2 h.1]
    exact lookup_none h.2

theorem lookup_append_some {α β : Type} [BEq α] {l₁ l₂ : List (α × β)} {a : α} {b : β}
    (h : l₁.lookup a = some b) : (l₁ ++ l₂).lookup a = some b := by
  rw [List.lookup_append, h]
  rfl

theorem lookup_append_none {α β : Type} [BEq α] {l₁ l₂ : List (α × β)} {a : α}
    (h : l₁.lookup a = none) : (l₁ ++ l₂).lookup a = l₂.lookup a := by
  rw [List.lookup_append, h]
  rfl

/-! ## The placement's conditions -/

/-- `placeOkB` unfolded. -/
structure PlaceOk (S : LinkSpec) : Prop where
  nodup : (S.names ++ S.aliases.map (·.1)).Nodup
  nodupFns : (S.aliases.map (·.2)).Nodup
  aliasFn : ∀ p ∈ S.aliases, p.2 ∈ S.names
  aliasFns : S.aliasFns.map (·.func.name) = S.aliases.map (·.1)
  sizesLen : S.sizes.length = S.funcs.length
  sizesPos : ∀ n ∈ S.sizes, 0 < n
  pos : 0 < S.R
  align : S.R % 4 = 0
  fits : S.R + S.size < 2 ^ 64
  outside : ∀ e ∈ S.outside, e.2 % 2 ^ 64 < S.R ∨ S.R + S.size ≤ e.2 % 2 ^ 64

theorem placeOk_of {S : LinkSpec} (hp : S.placeOkB = true) : PlaceOk S := by
  simp only [LinkSpec.placeOkB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hp
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

namespace LinkSpec

variable {S : LinkSpec}

@[simp] theorem input_funcs : S.input.funcs = S.funcs ++ S.aliasFns := rfl
@[simp] theorem input_addrs : S.input.addrs = S.addrs := rfl
@[simp] theorem input_aliases : S.input.aliases = S.aliases := rfl
@[simp] theorem input_raStar : S.input.raStar = S.R + S.size := rfl
@[simp] theorem input_syms :
    S.input.syms = S.symNames.filterMap fun n => (S.addrs.lookup n).map (n, ·) := rfl

@[simp] theorem names_length : S.names.length = S.funcs.length := List.length_map ..

/-- A placed function's size is positive. -/
theorem sizes_pos (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) : 0 < S.sizes[i]! := by
  have hi' : i < S.sizes.length := by rw [hP.sizesLen]; exact hi
  rw [getElem!_pos S.sizes i hi']
  exact hP.sizesPos _ (List.getElem_mem hi')

theorem names_getElem! {i : Nat} (hi : i < S.funcs.length) :
    S.names[i]! = S.funcs[i].func.name := by
  rw [getElem!_pos S.names i (by simpa using hi)]
  simp [names]

/-- The `i`-th placed function's offset, gap word included, ends within the region. -/
theorem off_end (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    (offs S.sizes 0)[i]! + 4 * S.sizes[i]! + 4 ≤ S.size := by
  have := offs_end (o := 0) (ns := S.sizes) (by rw [hP.sizesLen]; exact hi)
  simpa [LinkSpec.size] using this

/-- The `i`-th and `i'`-th placed functions (`i < i'`) do not overlap. -/
theorem off_sep (hP : PlaceOk S) {i i' : Nat} (hi : i < i') (hi' : i' < S.funcs.length) :
    (offs S.sizes 0)[i]! + 4 * S.sizes[i]! + 4 ≤ (offs S.sizes 0)[i']! :=
  offs_sep hi (by rw [hP.sizesLen]; exact hi')

theorem names_nodup (hP : PlaceOk S) : S.names.Nodup := (List.nodup_append.1 hP.nodup).1

/-- Distinct placed functions have distinct names. -/
theorem names_inj (hP : PlaceOk S) {i i' : Nat} (hi : i < S.funcs.length)
    (hi' : i' < S.funcs.length) (h : S.names[i]! = S.names[i']!) : i = i' := by
  rw [getElem!_pos S.names i (by simpa using hi), getElem!_pos S.names i' (by simpa using hi')]
    at h
  exact (names_nodup hP).getElem_inj.1 h

/-- **The link map of a placed function**: its placed address. -/
theorem addrs_name (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    S.addrs.lookup S.names[i]! = some (S.R + (offs S.sizes 0)[i]!) := by
  have hl : i < S.progAddrs.length := by
    simp [progAddrs, offs_length, hi, hP.sizesLen]
  have hm : S.progAddrs.map (·.1) = S.names := by
    rw [progAddrs]
    exact List.map_fst_zip (by simp [offs_length, hP.sizesLen])
  have := lookup_getElem hl (hm ▸ names_nodup hP)
  have e1 : S.progAddrs[i].1 = S.names[i]! := by
    simp [progAddrs, getElem!_pos S.names i (by simpa using hi)]
  have e2 : S.progAddrs[i].2 = S.R + (offs S.sizes 0)[i]! := by
    simp [progAddrs, getElem!_pos (offs S.sizes 0) i (by simpa [offs_length, hP.sizesLen] using hi)]
  rw [e1, e2] at this
  exact lookup_append_some (lookup_append_some this)

/-- A placed function's name is not an alias. -/
theorem aliases_name (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    S.aliases.lookup S.names[i]! = none := by
  refine lookup_none fun hm => ?_
  have hn := (List.nodup_append.1 hP.nodup).2.2
  exact hn _ (by rw [getElem!_pos S.names i (by simpa using hi)]; exact List.getElem_mem _) _ hm
    rfl

/-- **The load address of a placed function** is its placed address. -/
theorem baseOf_name (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    S.input.baseOf S.names[i]! = S.R + (offs S.sizes 0)[i]! := by
  unfold LinkInput.baseOf LinkInput.addrOf
  rw [input_aliases, aliases_name hP hi, Option.getD_none, input_addrs, addrs_name hP hi,
    Option.getD_some]

/-- An alias names a placed function. -/
theorem alias_index (hP : PlaceOk S) {j : Nat} (hj : j < S.aliases.length) :
    ∃ i < S.funcs.length, S.names[i]! = S.aliases[j].2 := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 (hP.aliasFn _ (List.getElem_mem hj))
  exact ⟨i, by simpa using hi, by rw [getElem!_pos S.names i hi]; exact e⟩

/-- **The load address of an alias** is its function's placed address. -/
theorem baseOf_alias (hP : PlaceOk S) {j : Nat} (hj : j < S.aliases.length) {i : Nat}
    (hi : i < S.funcs.length) (he : S.names[i]! = S.aliases[j].2) :
    S.input.baseOf S.aliases[j].1 = S.R + (offs S.sizes 0)[i]! := by
  have hn : (S.aliases.map (·.1)).Nodup := (List.nodup_append.1 hP.nodup).2.1
  have hl := lookup_getElem hj hn
  simp only [LinkInput.baseOf, LinkInput.addrOf, input_aliases, input_addrs, hl,
    Option.getD_some, ← he, addrs_name hP hi]

end LinkSpec

/-! ## The compiled table -/

open LinkSpec

theorem tab_length (S : LinkSpec) :
    (tabOf S.input.resultsT).length = S.funcs.length + S.aliasFns.length := by
  simp [tabOf, LinkInput.resultsT]

/-- The `i`-th entry of the compiled table: the `i`-th function of the input, compiled at its
load address (`hr`: the pipeline accepts every function). -/
theorem tab_entry {S : LinkSpec} (hr : S.input.resultsT.all (·.2.toBool) = true) {i : Nat}
    (hi : i < S.funcs.length + S.aliasFns.length) :
    ∃ fi a, (S.funcs ++ S.aliasFns)[i]? = some fi ∧
      pipeT fi.func fi.k (BitVec.ofNat 64 (S.input.baseOf fi.func.name)) (raJ fi.ra fi.j) =
        .ok a ∧ (tabOf S.input.resultsT)[i]? = some (fi.func, a) := by
  have hl : i < (S.funcs ++ S.aliasFns).length := by simpa using hi
  let fi := (S.funcs ++ S.aliasFns)[i]
  refine ⟨fi, getOk (pipeT fi.func fi.k (BitVec.ofNat 64 (S.input.baseOf fi.func.name))
    (raJ fi.ra fi.j)), List.getElem?_eq_getElem hl, ?_, ?_⟩
  · apply getOk_eq
    have hl' : i < S.input.resultsT.length := by simpa [LinkInput.resultsT] using hl
    have := List.all_eq_true.1 hr _ (List.getElem_mem hl')
    simpa only [LinkInput.resultsT, List.getElem_map, input_funcs] using this
  · simp only [tabOf, LinkInput.resultsT, input_funcs, List.map_map, List.getElem?_map,
      List.getElem?_eq_getElem hl]
    rfl

/-- **A placed function's entry**: the `i`-th function, at its placed address, with
`sizes[i]` words (`sizesOkB`), compiled by the pipeline (its layout). -/
theorem tab_placed {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) :
    ∀ i < S.funcs.length, ∃ e, (tabOf S.input.resultsT)[i]? = some e ∧
      e.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      e.2.fb.words.size = S.sizes[i]! ∧ e.1.name = S.names[i]! ∧
      e.2.fa.layout = .ok e.2.fb := by
  intro i hi
  have hP := placeOk_of hp
  obtain ⟨fi, a, hfi, ha, ht⟩ := tab_entry hr (i := i) (by omega)
  rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, Option.some.injEq] at hfi
  subst hfi
  have hn := names_getElem! hi
  obtain ⟨hl, hb⟩ := pipeT_layout ha
  refine ⟨_, ht, ?_, ?_, hn.symm, hl⟩
  · rw [hb, ← hn, baseOf_name hP hi]
  · have hs' := congrArg (·[i]?) (of_decide_eq_true hs)
    simp only [List.getElem?_map, List.getElem?_take, hi, ite_true, ht, Option.map_some] at hs'
    have hi' : i < S.sizes.length := by rw [hP.sizesLen]; exact hi
    rw [getElem!_pos S.sizes i hi', ← Option.some.inj (hs'.trans (List.getElem?_eq_getElem hi'))]

/-- **An alias's entry** sits at its function's address: the `j`-th alias (entry
`funcs.length + j`) is the alias of the `i`-th placed function, at the same base. -/
theorem tab_alias {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) :
    ∀ j < S.aliasFns.length, ∃ e ef, (tabOf S.input.resultsT)[S.funcs.length + j]? = some e ∧
      (∃ i < S.funcs.length, (tabOf S.input.resultsT)[i]? = some ef) ∧
      e.2.base = ef.2.base ∧ S.input.aliases.lookup e.1.name = some ef.1.name := by
  intro j hj
  have hP := placeOk_of hp
  have hjl : j < S.aliases.length := by
    have := congrArg List.length hP.aliasFns
    simp only [List.length_map] at this
    omega
  obtain ⟨fi, a, hfi, ha, ht⟩ := tab_entry hr (i := S.funcs.length + j) (by omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hj, Option.some.injEq] at hfi
  subst hfi
  have hname : S.aliasFns[j].func.name = S.aliases[j].1 := by
    have := congrArg (·[j]?) hP.aliasFns
    simpa [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjl] using this
  obtain ⟨i, hi, hni⟩ := alias_index hP hjl
  obtain ⟨ef, htf, hbf, -, hnf, -⟩ := tab_placed hp hr hs i hi
  refine ⟨_, ef, ht, ⟨i, hi, htf⟩, ?_, ?_⟩
  · rw [hbf, (pipeT_layout ha).2, hname, baseOf_alias hP hjl hi hni]
  · have hn : (S.aliases.map (·.1)).Nodup := (List.nodup_append.1 hP.nodup).2.1
    simp only [input_aliases, hname, lookup_getElem hjl hn, hnf, hni]

end Link

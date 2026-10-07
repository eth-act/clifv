import FV.Link.Total
import FV.Link.RelocProof

/-! # Self-call aliases in `leanLink`'s totality (L1b): the linker's side

`cargo fv`'s self-call alias of a placed function `f` (name `n`) is the function `f__fvself`
(name `a`): `f`'s CLIF with the extern `a` (`f`'s self-call) renamed to `n` and the function
renamed to `a` (`FVTest/Link/LeanLinkMain.lean`: `{ fi with clif := … }`, so the same index
`k` and the same `lean-regalloc` answer `ra`/`j`). `leanLink` checks the alias's compiled code
against `f`'s (`aliasOkB`, `aliasShapeB`) and the code map with the shared code (`codeMapB`).

**`leanLink_total_alias`**: `leanLink` succeeds with aliases from

* the input conditions `aliasInB` (each alias's `k`, `ra`, `j` are its function's) and
  `aliasSymsB` (no alias name in the CLIF image's symbol names `symNames`: no function takes an
  alias's address), both decided on the driver's data;
* **`AliasOut S`: facts about the compiler's output, NOT proven here** (stated as a hypothesis;
  docs/TO-PROVE.md "L1", open):
  - `pipe`: on an alias and its function the pipeline `pipeT` (same index, load address and
    oracle answer) gives the same words, lines alike up to the names of `bl` (`a`/`n`), and
    relocations alike up to the symbols of `call26` relocations (`a`/`n`) (`AliasPipeOut`).
    This is the renaming invariance of `pipeT` (the alias is `f` renamed) together with the
    fact that `a` and `n` appear in `f`'s code only as `bl` targets;
  - `blr`: every compiled function declaring an alias (other than the alias) calls through a
    register only through other symbols' GOT entries (`blrGotB`, `noBlrB`'s second part).

Everything else is proven: from `AliasPipeOut`, the alias's resolved words are its function's
(`resolveWord_alias`: a `call26` to `a` and to `n` both resolve to `n`'s address, `baseOf`;
a partner lookup never meets a `call26`, `relocsOkB`), the raw words and call lines are
(`aliasShape_alias`), the code map holds (`codeMap_alias`: an alias shares its function's
slot, two slots are disjoint, the alias's link-map address is fresh and `noBlrB` holds).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-! ## The alias facts about the compiler's output (not proven) -/

/-- `R` holds of two lists element by element (same length). -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {x : α} {y : β} {l : List α} {l' : List β} : R x y → Forall₂ R l l' →
      Forall₂ R (x :: l) (y :: l')

/-- An alias's laid-out line and its function's: the same, or calls `bl` of the alias's two
names `a`, `n` (with the same trap code). -/
def LineAlike (a n : String) (l l' : Line) : Prop :=
  l = l' ∨ ∃ s s' t, l = .ins (.bl s) t ∧ l' = .ins (.bl s') t ∧ (s = a ∨ s = n) ∧
    (s' = a ∨ s' = n)

/-- An alias's relocation and its function's: the same, or `call26` relocations at the same
offset of the alias's two names. -/
def RelocAlike (a n : String) (r r' : Reloc) : Prop :=
  r = r' ∨ (r.offset = r'.offset ∧ r.type = .call26 ∧ r'.type = .call26 ∧ (r.sym = a ∨ r.sym = n) ∧
    (r'.sym = a ∨ r'.sym = n))

/-- **The alias's compiled code is its function's** up to the names `a`, `n` of calls. -/
structure AliasArt (a n : String) (ea ef : Art) : Prop where
  words : ea.fb.words = ef.fb.words
  lines : Forall₂ (LineAlike a n) ea.fa.lines.toList ef.fa.lines.toList
  relocs : Forall₂ (RelocAlike a n) ea.fb.relocs ef.fb.relocs

/-- The compiler's pipeline on the alias `fa` (name `a`) and its function `f` (name `n`), with
the same index, load address and oracle answer, gives code alike (`AliasArt`). -/
def AliasPipeOut (a n : String) (fa f : Clif.Function) : Prop :=
  ∀ (k : Nat) (b : BitVec 64) (o : Lean.Json) (ea ef : Art),
    pipeT fa k b o = .ok ea → pipeT f k b o = .ok ef → AliasArt a n ea ef

namespace LinkSpec

/-- **Input condition**: each alias's index `k` and `lean-regalloc` answer (`ra`, `j`) are its
function's (the driver builds the alias as `{ fi with clif := … }`). -/
def aliasInB (S : LinkSpec) : Bool :=
  (List.range S.aliasFns.length).all fun j => (List.range S.funcs.length).all fun i =>
    S.names[i]! != S.aliases[j]!.2 ||
      (S.funcs[i]!.k == S.aliasFns[j]!.k && S.funcs[i]!.ra == S.aliasFns[j]!.ra &&
        S.funcs[i]!.j == S.aliasFns[j]!.j)

/-- **Input condition**: no alias name is a name the CLIF image needs a symbol for (no function
takes an alias's address). -/
def aliasSymsB (S : LinkSpec) : Bool := S.aliases.all fun q => !S.symNames.contains q.1

end LinkSpec

/-- **The alias facts about the compiler's output — NOT proven** (the open part of the alias
totality; docs/TO-PROVE.md "L1"): `pipe`, the alias's code is its function's up to the call
names (`AliasPipeOut`: the renaming invariance of `pipeT`, and `a`, `n` only as `bl` targets
in `f`'s code); `blr`, every function declaring an alias calls through a register only through
other symbols' GOT entries (`blrGotB`). -/
structure AliasOut (S : LinkSpec) : Prop where
  pipe : ∀ (j : Nat) (hj : j < S.aliases.length) (hj' : j < S.aliasFns.length) (i : Nat)
    (hi : i < S.funcs.length), S.names[i]! = S.aliases[j].2 →
    AliasPipeOut S.aliases[j].1 S.aliases[j].2 S.aliasFns[j].func S.funcs[i].func
  blr : ∀ q ∈ S.aliases, ∀ e ∈ tabOf S.input.resultsT,
    (e.1.externs.any fun x => x.2.name == q.1) = true → e.1.name ≠ q.1 →
    blrGotB e.2.vcp q.1 = true

/-! ## The input conditions -/

theorem aliasIn_of {S : LinkSpec} (h : S.aliasInB = true) {j i : Nat}
    (hj : j < S.aliasFns.length) (hj2 : j < S.aliases.length) (hi : i < S.funcs.length)
    (he : S.names[i]! = S.aliases[j].2) :
    S.aliasFns[j].k = S.funcs[i].k ∧ S.aliasFns[j].ra = S.funcs[i].ra ∧
      S.aliasFns[j].j = S.funcs[i].j := by
  have := List.all_eq_true.1 (List.all_eq_true.1 h j (List.mem_range.2 hj)) i (List.mem_range.2 hi)
  rw [getElem!_pos S.aliases j hj2, getElem!_pos S.funcs i hi, getElem!_pos S.aliasFns j hj,
    he] at this
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1.symm, this.1.2.symm, this.2.symm⟩

theorem lookup_filterMap_none {x : String} {A : List (String × Nat)} :
    ∀ {l : List String}, x ∉ l →
      (l.filterMap fun n => (A.lookup n).map (n, ·)).lookup x = none
  | [], _ => rfl
  | y :: l, h => by
    have hne : x ≠ y := fun e => h (e ▸ List.mem_cons_self)
    have ih := lookup_filterMap_none (A := A) fun hm => h (List.mem_cons_of_mem _ hm)
    rw [List.filterMap_cons]
    cases A.lookup y with
    | none => exact ih
    | some v =>
      simp only [Option.map_some, List.lookup_cons]
      rw [show (x == y) = false from beq_false_of_ne hne]
      exact ih

theorem syms_alias {S : LinkSpec} (h : S.aliasSymsB = true) {q : String × String}
    (hq : q ∈ S.aliases) : S.input.syms.lookup q.1 = none := by
  have hn : q.1 ∉ S.symNames := by
    have := List.all_eq_true.1 h q hq
    simpa using this
  rw [input_syms]
  exact lookup_filterMap_none hn

/-! ## The alias's entry -/

/-- **An alias and its function in the compiled table**: the `j`-th alias (entry
`funcs.length + j`) and the `i`-th placed function, at `i`'s slot, with code alike. -/
theorem alias_pair {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) (hai : S.aliasInB = true)
    (ho : AliasOut S) {j : Nat} (hj : j < S.aliases.length) :
    ∃ i < S.funcs.length, S.names[i]! = S.aliases[j].2 ∧ ∃ e ef,
      (tabOf S.input.resultsT)[S.funcs.length + j]? = some e ∧
      (tabOf S.input.resultsT)[i]? = some ef ∧
      e.1.name = S.aliases[j].1 ∧ ef.1.name = S.aliases[j].2 ∧
      ef.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      ef.2.fb.words.size = S.sizes[i]! ∧ e.2.base = ef.2.base ∧
      AliasArt S.aliases[j].1 S.aliases[j].2 e.2 ef.2 := by
  have hP := placeOk_of hp
  have hj' : j < S.aliasFns.length := by
    have := congrArg List.length hP.aliasFns
    simp only [List.length_map] at this
    omega
  obtain ⟨i, hi, hni⟩ := alias_index hP hj
  obtain ⟨fa, a, hfa, ha, hta⟩ := tab_entry hr (i := S.funcs.length + j) (by omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hj', Option.some.injEq] at hfa
  subst hfa
  obtain ⟨fi, b, hfi, hb, htb⟩ := tab_entry hr (i := i) (by omega)
  rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, Option.some.injEq] at hfi
  subst hfi
  obtain ⟨ef, htf, hbf, hszf, hnf, -⟩ := tab_placed hp hr hn hs i hi
  rw [htb, Option.some.injEq] at htf
  subst htf
  have hname : S.aliasFns[j].func.name = S.aliases[j].1 := by
    have := congrArg (·[j]?) hP.aliasFns
    simpa [List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hj] using this
  obtain ⟨hk, hra, hjj⟩ := aliasIn_of hai hj' hj hi hni
  have hbase : S.input.baseOf S.aliasFns[j].func.name = S.input.baseOf S.funcs[i].func.name := by
    rw [hname, baseOf_alias hP hj hi hni, ← names_getElem! hn hi, baseOf_name hP hi]
  rw [hbase, hk, hra, hjj] at ha
  refine ⟨i, hi, hni, _, _, hta, htb, hname, hnf.trans hni, hbf, hszf, ?_,
    ho.pipe j hj hj' i hi hni _ _ _ _ _ ha hb⟩
  rw [(pipeT_layout ha).2, (pipeT_layout hb).2]

/-- The entry of the compiled table with the name `s` is the one `find?` finds. -/
theorem find_tab {S : LinkSpec} (hP : PlaceOk S) (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    {x : Nat} {e : Clif.Function × Art} (he : (tabOf S.input.resultsT)[x]? = some e) {s : String}
    (hs : e.1.name = s) : (tabOf S.input.resultsT).find? (·.1.name == s) = some e := by
  subst hs
  exact find?_key (f := fun e : Clif.Function × Art => e.1.name) (tab_names S hP hn)
    (List.mem_of_getElem? he)

/-! ## Relocations alike resolve alike -/

theorem find?_alike {a n : String} {o : Nat} : ∀ {l l' : List Reloc},
    Forall₂ (RelocAlike a n) l l' →
    (l.find? (·.offset == o) = none ∧ l'.find? (·.offset == o) = none) ∨
    ∃ r r', l.find? (·.offset == o) = some r ∧ l'.find? (·.offset == o) = some r' ∧
      RelocAlike a n r r'
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | r :: l, r' :: l', .cons h t => by
    have hoff : r.offset = r'.offset := by
      rcases h with rfl | h
      · rfl
      · exact h.1
    rw [List.find?_cons, List.find?_cons, hoff]
    cases r'.offset == o
    · exact find?_alike t
    · exact .inr ⟨r, r', rfl, rfl, h⟩

/-- The partner a low-part relocation's resolved form reads (four bytes before) is no `call26`
(`relocOkB`: it is the page part). -/
theorem partner_not_call {I : LinkInput} {tp : Nat → Option Nat} {ef : Art}
    (hv : relocsOkB I tp ef = true) {r : Reloc} (hr : r ∈ ef.fb.relocs) {x : Reloc}
    (hx : relocAt? ef (r.offset - 4) = some x)
    (ht : r.type = .ld64GotLo12Nc ∨ r.type = .addAbsLo12Nc ∨ r.type = .tlsDescLd64Lo12) :
    x.type ≠ .call26 := by
  simp only [relocsOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
  obtain ⟨hnd, hall⟩ := hv
  have hok := hall r hr
  have hxm : x ∈ ef.fb.relocs := List.mem_of_find?_eq_some hx
  have hxo : x.offset = r.offset - 4 := by
    have := List.find?_some hx
    simpa using this
  have key : ∀ y ∈ ef.fb.relocs, y.offset = r.offset - 4 → y.type ≠ .call26 → x.type ≠ .call26 :=
    fun y hy hyo hyt => by rw [eq_of_nodup_offset hnd hxm hy (hxo.trans hyo.symm)]; exact hyt
  unfold relocOkB at hok
  rcases ht with ht | ht | ht <;> rw [ht] at hok <;>
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq, hasAt] at hok
  · obtain ⟨-, y, hy, hyo, hyt⟩ := hok
    exact key y hy (by omega) (by rcases hyt with h | h <;> rw [h] <;> decide)
  · obtain ⟨-, y, hy, hyo, hyt⟩ := hok
    exact key y hy (by omega) (by rcases hyt with h | h <;> rw [h] <;> decide)
  · obtain ⟨-, ⟨y, hy, hyo, hyt⟩, -⟩ := hok
    exact key y hy hyo (by rw [hyt]; decide)

/-- **An alias's resolved words are its function's**: alike relocations resolve alike when the
alias's two names have one load address. -/
theorem resolveWord_alias {I : LinkInput} {tp : Nat → Option Nat} {a n : String} {ea ef : Art}
    (hA : AliasArt a n ea ef) (hb : ea.base = ef.base) (hab : I.baseOf a = I.baseOf n)
    (hv : relocsOkB I tp ef = true) (k : Nat) :
    resolveWord I tp ea k = resolveWord I tp ef k := by
  have hw : ∀ k, wordOf ea k = wordOf ef k := fun k => by simp [wordOf, hA.words]
  have hP : ∀ o, wAt ea o = wAt ef o := fun o => by simp [wAt, hb]
  have hbase : ∀ s s', (s = a ∨ s = n) → (s' = a ∨ s' = n) → I.baseOf s = I.baseOf s' := by
    rintro s s' (rfl | rfl) (rfl | rfl) <;> simp [hab]
  -- the partner four bytes before: alike, and the same relocation when the word's own is low
  have hpart : ∀ r ∈ ef.fb.relocs, r.offset = 4 * k →
      (r.type = .ld64GotLo12Nc ∨ r.type = .addAbsLo12Nc ∨ r.type = .tlsDescLd64Lo12) →
      relocAt? ea (4 * k - 4) = relocAt? ef (4 * k - 4) := by
    intro r hr hro ht
    rcases find?_alike (o := 4 * k - 4) hA.relocs with ⟨h1, h2⟩ | ⟨x, x', h1, h2, hx⟩
    · simp only [relocAt?, h1, h2]
    · simp only [relocAt?, h1, h2]
      rcases hx with rfl | ⟨-, -, hx', -, -⟩
      · rfl
      · exact absurd hx' (partner_not_call hv hr (x := x') (by rw [hro]; exact h2) ht)
  unfold resolveWord
  simp only [hw, hP]
  rcases find?_alike (o := 4 * k) hA.relocs with ⟨h1, h2⟩ | ⟨r, r', h1, h2, hr⟩
  · simp only [relocAt?] at *
    rw [h1, h2]
  · have hrm : r' ∈ ef.fb.relocs := List.mem_of_find?_eq_some h2
    have hro : r'.offset = 4 * k := by
      have := List.find?_some h2
      simpa using this
    have e1 : relocAt? ea (4 * k) = some r := h1
    have e2 : relocAt? ef (4 * k) = some r' := h2
    rw [e1, e2]
    rcases hr with rfl | ⟨-, ht, ht', hs, hs'⟩
    · dsimp only
      cases ht : r.type with
      | ld64GotLo12Nc => rw [hpart r hrm hro (.inl ht)]
      | addAbsLo12Nc => rw [hpart r hrm hro (.inr (.inl ht))]
      | tlsDescLd64Lo12 => rw [hpart r hrm hro (.inr (.inr ht))]
      | _ => rfl
    · simp only [ht, ht', hbase _ _ hs hs']

/-! ## Lines alike -/

theorem lineAlike_self (P : Clif.Program) (l : Line) : lineAlikeB P l l = true := by
  cases l <;> simp [lineAlikeB, insnAlikeB]

theorem lineAlike_of {P : Clif.Program} {a n : String} (ha : (P.func? a).isSome = true)
    (hn : (P.func? n).isSome = true) {l l' : Line} (h : LineAlike a n l l') :
    lineAlikeB P l l' = true ∧ lineAlikeB P l' l = true := by
  rcases h with rfl | ⟨s, s', t, rfl, rfl, hs, hs'⟩
  · exact ⟨lineAlike_self P l, lineAlike_self P l⟩
  · have hf : ∀ x, (x = a ∨ x = n) → (P.func? x).isSome = true := by
      rintro x (rfl | rfl) <;> assumption
    simp [lineAlikeB, insnAlikeB, hf s hs, hf s' hs']

theorem linesAlike_of {P : Clif.Program} {a n : String} (ha : (P.func? a).isSome = true)
    (hn : (P.func? n).isSome = true) : ∀ {L L' : List Line}, Forall₂ (LineAlike a n) L L' →
    linesAlikeB P L L' = true ∧ linesAlikeB P L' L = true
  | _, _, .nil => ⟨rfl, rfl⟩
  | _, _, .cons h t => by
    have h1 := lineAlike_of ha hn h
    have h2 := linesAlike_of ha hn t
    simp only [linesAlikeB, h1.1, h1.2, h2.1, h2.2, Bool.and_self, and_self]

theorem map_shape_alike {a n : String} : ∀ {L L' : List Line}, Forall₂ (LineAlike a n) L L' →
    L.map (fun l => (callLine l, l.size)) = L'.map (fun l => (callLine l, l.size))
  | _, _, .nil => rfl
  | _, _, .cons hl t => by
    rw [List.map_cons, List.map_cons, map_shape_alike t]
    rcases hl with rfl | ⟨s, s', tr, rfl, rfl, -, -⟩
    · rfl
    · rfl

theorem callShape_alike {a n : String} {ea ef : Art} (hA : AliasArt a n ea ef) :
    callShape ea = callShape ef :=
  map_shape_alike hA.lines

theorem func?_isSome {T : List (Clif.Function × Art)} {e : Clif.Function × Art} (he : e ∈ T) :
    ((progT T).func? e.1.name).isSome = true := by
  simp only [Clif.Program.func?, progT, List.find?_map, Option.isSome_map]
  exact List.find?_isSome.2 ⟨e, he, by simp⟩

/-! ## The checks -/

/-- Every alias pair as a fact usable inside `I.aliases.all`. -/
theorem aliases_all {S : LinkSpec} {p : String × String → Bool}
    (h : ∀ j (hj : j < S.aliases.length), p S.aliases[j] = true) : S.aliases.all p = true :=
  List.all_eq_true.2 fun q hq => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    exact h j hj

/-- **`aliasShapeB` holds** with `AliasOut`. -/
theorem aliasShape_alias {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) (hai : S.aliasInB = true)
    (ho : AliasOut S) : aliasShapeB S.input (tabOf S.input.resultsT) = true := by
  have hP := placeOk_of hp
  unfold aliasShapeB
  rw [input_aliases]
  refine aliases_all fun j hj => ?_
  obtain ⟨i, hi, -, e, ef, he, hef, hen, hefn, -, -, -, hA⟩ :=
    alias_pair hp hr hn hs hai ho hj
  simp only [find_tab hP hn he hen, find_tab hP hn hef hefn, hA.words, callShape_alike hA,
    beq_self_eq_true, Bool.and_self]

/-- **`aliasOkB` holds** with `AliasOut` and the relocations' checks. -/
theorem aliasOk_alias {S : LinkSpec} {tp : Nat → Option Nat} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) (hai : S.aliasInB = true)
    (ho : AliasOut S) (hv : (tabOf S.input.resultsT).all (fun e => relocsOkB S.input tp e.2) = true) :
    aliasOkB S.input tp (tabOf S.input.resultsT) = true := by
  have hP := placeOk_of hp
  unfold aliasOkB
  rw [input_aliases]
  refine aliases_all fun j hj => ?_
  obtain ⟨i, hi, hni, e, ef, he, hef, hen, hefn, -, -, hb, hA⟩ :=
    alias_pair hp hr hn hs hai ho hj
  have hab : S.input.baseOf S.aliases[j].1 = S.input.baseOf S.aliases[j].2 := by
    rw [baseOf_alias hP hj hi hni, ← hni, baseOf_name hP hi]
  have hvf := List.all_eq_true.1 hv ef (List.mem_of_getElem? hef)
  simp only [find_tab hP hn he hen, find_tab hP hn hef hefn, hA.words, beq_self_eq_true,
    Bool.true_and, List.all_eq_true, List.mem_range]
  intro k _
  rw [resolveWord_alias hA hb hab hvf k]
  exact beq_self_eq_true _

/-- **No `blr` enters an alias** (`noBlrB`): with `aliasSymsB` and `AliasOut.blr`. -/
theorem noBlr_alias {S : LinkSpec} (hsy : S.aliasSymsB = true) (ho : AliasOut S)
    {q : String × String} (hq : q ∈ S.aliases) :
    noBlrB S.input (tabOf S.input.resultsT) q.1 = true := by
  unfold noBlrB
  rw [syms_alias hsy hq]
  simp only [Option.isNone_none, Bool.true_and, List.all_eq_true]
  intro e he
  by_cases hd : (e.1.externs.any fun x => x.2.name == q.1) = true
  · by_cases hne : e.1.name = q.1
    · simp [hne]
    · simp [ho.blr q hq e he hd hne]
  · simp [hd]

/-- **The code map with aliases**: every entry sits at a placed function's slot (an alias at its
function's); two slots are disjoint; one slot's two entries are a function and its alias, with
lines alike. -/
theorem codeMap_alias {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) (hai : S.aliasInB = true)
    (hsy : S.aliasSymsB = true) (ho : AliasOut S) :
    codeMapB S.input (tabOf S.input.resultsT) = true := by
  have hP := placeOk_of hp
  have hfit : ∀ i < S.funcs.length, S.R + (offs S.sizes 0)[i]! + 4 * S.sizes[i]! < 2 ^ 64 :=
    fun i hi => by
      have := off_end hP hi
      have := hP.fits
      omega
  have hlen : S.aliasFns.length = S.aliases.length := by
    have := congrArg List.length hP.aliasFns
    simpa using this
  -- every entry: its slot `i`, and whether it is the placed function or an alias of it
  have hslot : ∀ e ∈ tabOf S.input.resultsT, ∃ i < S.funcs.length,
      e.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      e.2.fb.words.size = S.sizes[i]! ∧
      (((tabOf S.input.resultsT)[i]? = some e ∧ e.1.name = S.names[i]!) ∨
      ∃ j, ∃ hj : j < S.aliases.length, S.names[i]! = S.aliases[j].2 ∧
        e.1.name = S.aliases[j].1 ∧ ∃ ef, (tabOf S.input.resultsT)[i]? = some ef ∧
        ef.1.name = S.aliases[j].2 ∧ AliasArt S.aliases[j].1 S.aliases[j].2 e.2 ef.2) := by
    intro e he
    obtain ⟨x, hx⟩ := List.mem_iff_getElem?.1 he
    have hxl := (List.getElem?_eq_some_iff.1 hx).1
    rw [tab_length] at hxl
    by_cases hxi : x < S.funcs.length
    · obtain ⟨e1, h1, hb, hsz, hnm, -⟩ := tab_placed hp hr hn hs x hxi
      rw [hx, Option.some.injEq] at h1
      subst h1
      exact ⟨x, hxi, hb, hsz, .inl ⟨hx, hnm⟩⟩
    · obtain ⟨j, rfl⟩ : ∃ j, x = S.funcs.length + j := ⟨x - S.funcs.length, by omega⟩
      have hj : j < S.aliases.length := by omega
      obtain ⟨i, hi, hni, e1, ef, h1, hef, hen, hefn, hbf, hszf, hb, hA⟩ :=
        alias_pair hp hr hn hs hai ho hj
      rw [hx, Option.some.injEq] at h1
      subst h1
      exact ⟨i, hi, hb.trans hbf, hA.words ▸ hszf, .inr ⟨j, hj, hni, hen, ef, hef, hefn, hA⟩⟩
  have htoNat : ∀ e : Clif.Function × Art, ∀ i < S.funcs.length,
      e.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) →
      e.2.base.toNat = S.R + (offs S.sizes 0)[i]! := fun e i hi hb => by
    rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hfit i hi; omega)]
  have hmem : ∀ {i} {ef : Clif.Function × Art}, (tabOf S.input.resultsT)[i]? = some ef →
      ef ∈ tabOf S.input.resultsT := List.mem_of_getElem?
  simp only [codeMapB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  intro e he
  obtain ⟨i, hi, hb, hsz, hk⟩ := hslot e he
  refine ⟨?_, fun e' he' => ?_⟩
  · rcases hk with ⟨-, hnm⟩ | ⟨j, hj, -, hen, -⟩
    · left
      simp only [LinkInput.symAddr, LinkInput.addrOf, hnm, input_addrs, addrs_name hP hi,
        Option.getD_some, hb, BitVec.ofInt_ofNat, BitVec.add_zero]
    · right
      rw [hen]
      exact noBlr_alias hsy ho (List.getElem_mem hj)
  · obtain ⟨i', hi', hb', hsz', hk'⟩ := hslot e' he'
    have t1 := htoNat e i hi hb
    have t2 := htoNat e' i' hi' hb'
    rcases Nat.lt_trichotomy i i' with h | rfl | h
    · have := off_sep hP h hi'
      exact .inl (.inr (.inl (by rw [t1, t2, hsz]; omega)))
    · have hbb : e.2.base = e'.2.base := hb.trans hb'.symm
      rcases hk with ⟨h1, -⟩ | ⟨j, hj, hni, hen, ef, hef, hefn, hA⟩ <;>
        rcases hk' with ⟨h1', -⟩ | ⟨j', hj', hni', hen', ef', hef', hefn', hA'⟩
      · rw [h1] at h1'
        cases Option.some.inj h1'
        exact .inl (.inl rfl)
      · -- `e` the function, `e'` its alias
        rw [h1] at hef'
        cases Option.some.inj hef'
        refine .inr ⟨hbb, (linesAlike_of ?_ ?_ hA'.lines).2⟩
        · rw [← hen']; exact func?_isSome he'
        · rw [← hefn']; exact func?_isSome he
      · -- `e` an alias, `e'` its function
        rw [h1'] at hef
        cases Option.some.inj hef
        refine .inr ⟨hbb, (linesAlike_of ?_ ?_ hA.lines).1⟩
        · rw [← hen]; exact func?_isSome he
        · rw [← hefn]; exact func?_isSome he'
      · -- two aliases of one function: the same alias
        have hq := alias_fn_inj hP (List.getElem_mem hj) (List.getElem_mem hj')
          (hni.symm.trans hni')
        exact .inl (.inl (by rw [hen, hen', hq]))
    · have := off_sep hP h hi
      exact .inl (.inr (.inr (by rw [t1, t2, hsz']; omega)))

/-! ## `leanLink` succeeds -/

/-- **`leanLink` succeeds with self-call aliases**: the alias-free causes of
`leanLink_total_of`, the input conditions `aliasInB`, `aliasSymsB`, and the (unproven) output
facts `AliasOut`. -/
theorem leanLink_total_alias {S : LinkSpec} {file0 : ByteArray}
    {phs : List Phdr} (hph : phdrs (fileRd file0) = some phs) (hin : InScopeP S.input0 = true)
    (hp : S.placeOkB = true) (hai : S.aliasInB = true) (hsy : S.aliasSymsB = true)
    (ho : AliasOut S)
    (hn : S.names = S.funcs.map (·.func.name)) (hs : S.sizes = S.sizesOf)
    (hshape : ∀ e ∈ tabOf S.input.resultsT, relocShapesB e.2 = true)
    (hrange : ∀ e ∈ tabOf S.input.resultsT, ∀ r ∈ e.2.fb.relocs,
      relocRangeB S.input (tpOff phs) e.2 r = true)
    (hreg : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    (hout : outsideOkB S.input S.data (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) =
      true) :
    leanLink S file0 = .ok (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) := by
  have hr := results_of hin
  have hnm := names_of hn
  have hsz := sizes_of hs
  have hv : (tabOf S.input0.resultsT).all (fun e => relocsOkB S.input (tpOff phs) e.2) = true :=
    List.all_eq_true.2 fun e he => relocsOkB_of (hshape e he) (hrange e he)
  exact leanLink_total_checks hph hp hr hnm hsz hv
    (aliasOk_alias hp hr hnm hsz hai ho hv) (aliasShape_alias hp hr hnm hsz hai ho)
    (codeMap_alias hp hr hnm hsz hai hsy ho) hreg hout

end Link

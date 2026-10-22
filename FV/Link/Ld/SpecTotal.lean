import FV.Link.Ld.LinkTotal
import FV.Link.Ld.Spec

/-! # The link spec at `lean-ld`'s plan (A1f, #409)

`Plan.specOkB` (`FV/Link/Ld/Spec.lean`) relates a link spec to `lean-ld`'s plan. Here the link
spec's addresses come from the plan's symbols (`LinkSpec.atSyms`): the region's base `R` and
every outside name's address are a value the plan gives a symbol of that name (the given address
when the plan has a symbol of that name and value — the executable's symbol table on `lean-ld`'s
own output —, else the plan's first symbol of the name; a name without one is left out, as
`Front.buildSpec` leaves it out). So the outside part of `symsPlanB` holds by construction
(`outside_inSyms`).

`specPreB` decides the rest on `lean-ld`'s placement of the inputs (`layPre`: its segments, TLS
template and symbols, and the placed input sections' bytes with their relocations resolved; no
relocation applied, no byte of the output written): the region in the `R E` segment's file bytes
(`regionInB`), the program part's link-map entries among the plan's symbols (the region object's
symbols at the Lean compiler's layout), the TLS offsets (`tlsBoundB`), the CLIF data objects in
the input sections (`dataPlanB`). **`specOkB_of_pre`**: with `layout`'s plan, `Plan.specOkB`.
-/

namespace Link.Ld

open E2E E2E.Elf E2E.BinCheck E2E.LinkCheck Link

/-! ## Finding a plan's symbols -/

/-- One step of `symHint`. -/
def hintStep (syms : Array OutSym) (m : Std.HashMap (String × Nat) Nat) (k : Nat) :
    Std.HashMap (String × Nat) Nat :=
  match syms[k]? with
  | some s => m.insertIfNew (s.name, s.value) k
  | none => m

theorem symHint_eq (syms : Array OutSym) : symHint syms = (List.range syms.size).foldl (hintStep syms) {} := rfl

/-- `symHint`'s entries are the plan's symbols; every symbol's name and value is a key. -/
theorem hint_foldl (syms : Array OutSym) : ∀ (l : List Nat) (m : Std.HashMap (String × Nat) Nat),
    (∀ key k, m[key]? = some k → ∃ s : OutSym, syms[k]? = some s ∧ (s.name, s.value) = key) →
    (∀ key k, (l.foldl (hintStep syms) m)[key]? = some k → ∃ s : OutSym, syms[k]? = some s ∧ (s.name, s.value) = key) ∧
    (∀ key, key ∈ m → key ∈ l.foldl (hintStep syms) m) ∧
    (∀ k ∈ l, ∀ s, syms[k]? = some s → (s.name, s.value) ∈ l.foldl (hintStep syms) m)
  | [], m, h => ⟨h, fun _ hk => hk, fun _ hk => by cases hk⟩
  | k :: l, m, h => by
    simp only [List.foldl_cons]
    have hstep : ∀ key k', (hintStep syms m k)[key]? = some k' →
        ∃ s : OutSym, syms[k']? = some s ∧ (s.name, s.value) = key := by
      intro key k' hk'
      unfold hintStep at hk'
      split at hk'
      · rename_i s hs
        rw [Std.HashMap.getElem?_insertIfNew] at hk'
        split at hk'
        · rename_i hc
          simp only [Option.some.injEq] at hk'
          subst hk'
          exact ⟨s, hs, by simpa using hc.1⟩
        · exact h key k' hk'
      · exact h key k' hk'
    obtain ⟨h1, h2, h3⟩ := hint_foldl syms l _ hstep
    have hm : ∀ key, key ∈ m → key ∈ hintStep syms m k := by
      intro key hk
      unfold hintStep
      split
      · exact Std.HashMap.mem_insertIfNew.2 (.inr hk)
      · exact hk
    refine ⟨h1, fun key hk => h2 key (hm key hk), fun k' hk' s hs => ?_⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · apply h2
      unfold hintStep
      rw [hs]
      exact Std.HashMap.mem_insertIfNew_self
    · exact h3 k' hk' s hs

theorem symHint_sound {syms : Array OutSym} {key : String × Nat} {k : Nat} (h : (symHint syms)[key]? = some k) :
    ∃ s : OutSym, syms[k]? = some s ∧ (s.name, s.value) = key := by
  rw [symHint_eq] at h
  exact (hint_foldl syms _ {} (fun _ _ h => by simp at h)).1 _ _ h

theorem symHint_complete {syms : Array OutSym} {k : Nat} {s : OutSym} (hs : syms[k]? = some s) :
    (s.name, s.value) ∈ symHint syms := by
  rw [symHint_eq]
  have hk : k < syms.size := (Array.getElem?_eq_some_iff.1 hs).1
  exact (hint_foldl syms _ {} (fun _ _ h => by simp at h)).2.2 k (List.mem_range.2 hk) s hs

/-- **A link-map entry is one of the plan's symbols** (`symsPlanB`'s check of one entry). -/
def inSymsB (pl : Plan) (p : String × Nat) : Bool :=
  match (symHint pl.syms)[(symName p.1, p.2)]?.bind (pl.syms[·]?) with
  | some s => s.name == symName p.1 && s.value == p.2
  | none => false

theorem symsPlanB_eq (I : LinkInput) (pl : Plan) :
    symsPlanB I pl = I.addrs.all fun p => (I.aliases.lookup p.1).isSome || inSymsB pl p := rfl

theorem inSymsB_of_hint {pl : Plan} {p : String × Nat} (h : (symName p.1, p.2) ∈ symHint pl.syms) :
    inSymsB pl p = true := by
  obtain ⟨k, hk⟩ : ∃ k, (symHint pl.syms)[(symName p.1, p.2)]? = some k :=
    Option.isSome_iff_exists.1 (Std.HashMap.isSome_getElem?_iff_mem.2 h)
  obtain ⟨s, hs, he⟩ := symHint_sound hk
  unfold inSymsB
  simp only [hk, Option.bind_some, hs]
  simp only [Prod.mk.injEq] at he
  simp [he.1, he.2]

/-- The value of the first symbol of each name. -/
def firstVals (syms : Array OutSym) : Std.HashMap String Nat :=
  syms.foldl (fun m s => m.insertIfNew s.name s.value) {}

theorem firstVals_go : ∀ (l : List OutSym) (m : Std.HashMap String Nat) (P : OutSym → Prop),
    (∀ n v, m[n]? = some v → ∃ s : OutSym, P s ∧ s.name = n ∧ s.value = v) →
    ∀ n v, (l.foldl (fun m s => m.insertIfNew s.name s.value) m)[n]? = some v →
      ∃ s : OutSym, (P s ∨ s ∈ l) ∧ s.name = n ∧ s.value = v
  | [], m, P, h => fun n v hv => by
    obtain ⟨s, hs, h1, h2⟩ := h n v hv
    exact ⟨s, .inl hs, h1, h2⟩
  | s :: l, m, P, h => by
    simp only [List.foldl_cons]
    intro n v hv
    have := firstVals_go l (m.insertIfNew s.name s.value) (fun t => P t ∨ t = s) (fun n' v' hv' => by
      rw [Std.HashMap.getElem?_insertIfNew] at hv'
      split at hv'
      · rename_i hc
        simp only [Option.some.injEq] at hv'
        subst hv'
        exact ⟨s, .inr rfl, by simpa using hc.1, rfl⟩
      · obtain ⟨t, ht, h1, h2⟩ := h n' v' hv'
        exact ⟨t, .inl ht, h1, h2⟩) n v hv
    obtain ⟨t, ht, h1, h2⟩ := this
    refine ⟨t, ?_, h1, h2⟩
    rcases ht with (ht | rfl) | ht
    · exact .inl ht
    · exact .inr (List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ ht)

theorem firstVals_sound {syms : Array OutSym} {n : String} {v : Nat} (h : (firstVals syms)[n]? = some v) :
    ∃ s ∈ syms.toList, s.name = n ∧ s.value = v := by
  unfold firstVals at h
  rw [← Array.foldl_toList] at h
  obtain ⟨s, hs, h1, h2⟩ := firstVals_go syms.toList {} (fun _ => False) (fun _ _ h => by simp at h) n v h
  rcases hs with hs | hs
  · exact hs.elim
  · exact ⟨s, hs, h1, h2⟩

/-! ## The link spec at the plan's symbols -/

/-- **An address from the plan's symbols** for the link-map name `n` with hint `a`: `a` when the
plan has a symbol `symName n` of value `a`, else the first symbol named `symName n`'s value. -/
def pinAddr (syms : Array OutSym) (n : String) (a : Nat) : Option Nat :=
  if (symHint syms).contains (symName n, a) then some a else (firstVals syms)[symName n]?

/-- The outside part's addresses from the plan's symbols (a name without one is left out). -/
def pinOutside (syms : Array OutSym) (l : List (String × Nat)) : List (String × Nat) :=
  l.filterMap fun p => (pinAddr syms p.1 p.2).map (p.1, ·)

/-- **The link spec at `lean-ld`'s plan's symbols** `syms`: the region's base the first
function's address there (`S.R` as the hint; `S.R` without one), the outside part's addresses
from them. -/
def _root_.Link.LinkSpec.atSyms (S : LinkSpec) (syms : Array OutSym) : LinkSpec :=
  { S with R := ((S.funcs.head?.map (·.func.name)).bind fun n => pinAddr syms n S.R).getD S.R,
           outside := pinOutside syms S.outside }

theorem pinAddr_inSyms {pl : Plan} {n : String} {a v : Nat} (h : pinAddr pl.syms n a = some v) :
    inSymsB pl (n, v) = true := by
  unfold pinAddr at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    exact inSymsB_of_hint (Std.HashMap.contains_iff_mem.1 hc)
  · obtain ⟨s, hs, h1, h2⟩ := firstVals_sound h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hs
    rw [Array.getElem?_toList] at hk
    have := symHint_complete hk
    rw [h1, h2] at this
    exact inSymsB_of_hint this

/-- **The outside part of `symsPlanB` holds by construction.** -/
theorem outside_inSyms {pl : Plan} (l : List (String × Nat)) : ∀ p ∈ pinOutside pl.syms l, inSymsB pl p = true := by
  intro p hp
  unfold pinOutside at hp
  obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 hp
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hq
  exact pinAddr_inSyms hv

/-! ## The spec's conditions on the placement -/

/-- **The link spec's conditions on `lean-ld`'s placement** (the plan of `layPre`'s entry,
pieces and symbols, as `layout` builds it): the region in the `R E` segment's file bytes, the
program part's link-map entries among the plan's symbols, the TLS offsets, the CLIF data objects
in the placed input sections. -/
def specPreB (P : LinkSpec) (o : Opts) (st : St) (g : GcOut) : Bool :=
  let L := layPre o st g
  match L.entry o st g, L.pieces o st g with
  | .ok e, .ok ps =>
    let pl := L.plan o e ps (L.syms o st g).1
    pl.regionInB P.R P.size && P.progAddrs.all (inSymsB pl) && tlsBoundB P pl &&
      dataPlanB P.input0 P.data pl (offsetOf pl.phdrs P.R) P.size
  | _, _ => false

/-- **`Plan.specOkB` of `layout`'s plan** from `specPreB`, when the outside part's entries are
the plan's symbols (`outside_inSyms`). -/
theorem specOkB_of_pre {P : LinkSpec} {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (hl : layout o st g = .ok (pl, m)) (hP : specPreB P o st g = true)
    (hout : ∀ p ∈ P.outside, inSymsB pl p = true) : pl.specOkB P = true := by
  obtain ⟨e, ps, he, hps, rfl⟩ := layout_parts hl
  unfold specPreB at hP
  simp only [he, hps, Bool.and_eq_true] at hP
  obtain ⟨⟨⟨hreg, hprog⟩, htls⟩, hdat⟩ := hP
  unfold Plan.specOkB
  simp only [hreg, htls, hdat, Bool.and_true, Bool.true_and, symsPlanB_eq, List.all_eq_true]
  intro p hp
  have ha : (P.input0.aliases.lookup p.1) = none := rfl
  simp only [ha, Option.isSome_none, Bool.false_or]
  have hp' : p ∈ P.progAddrs ++ P.outside := hp
  rcases List.mem_append.1 hp' with hp' | hp'
  · exact List.all_eq_true.1 hprog p hp'
  · exact hout p hp'

theorem atSyms_outside (S : LinkSpec) (syms : Array OutSym) (sz : List Nat) :
    ((S.atSyms syms).withSizes sz).outside = pinOutside syms S.outside := rfl

end Link.Ld

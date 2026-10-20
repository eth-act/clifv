import FV.Front.Bundle
import FV.Link.LayoutFacts

/-!
# The Lean-built `LinkSpec` is the units' program (T7d, docs/contracts/frontend.md)

* **`Front.parseUnit_spec`**: a parsed unit's functions are its dumps' decodings (one each,
  named as the bundle says: `decodeFile_spec`; cg_clif's functions renamed by the unit's
  declarations: `parseUnit_raw`), its data the objects of its `; data:` lines that its functions
  reach (**`data_complete`**: every object reachable from the functions' names through
  relocations is kept; `data_sound`: only the unit's objects are; no line that does not parse is
  reachable).
* **`Front.scopingB_sound`**: the linked names are a scoping (`ScopingOk`).
* **`Front.link_alpha`**: the program (and data) of the units under any two scopings are
  alpha-equivalent: one is the other renamed by a bijection of names (`Clif.Ren`), which maps
  every name of the first to the corresponding one of the second. With `Clif.runLoop_ren`
  (`FV/Front/RenameRun.lean`) the runs of the two programs correspond.
* **`Front.buildSpec_spec`**: the `LinkSpec` built from a bundle has the source program
  `link us (finOf us)` (the parsed functions, renamed to the linked names: `srcProg_eq`), the data
  `linkData us (finOf us)`, and every program function whose address the program's CLIF or a
  reachable data object takes among the CLIF image's symbols (`symNames_complete`).
-/

namespace Front

open Clif E2E.LinkCheck Link

/-! ## Generic facts -/

theorem foldl_insert_contains (l : List String) (s : Std.HashSet String) (x : String) :
    (l.foldl (·.insert ·) s).contains x = true ↔ x ∈ l ∨ s.contains x = true := by
  induction l generalizing s with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    simp only [List.mem_cons, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem foldl_insert_empty (l : List String) (x : String) :
    (l.foldl (·.insert ·) ({} : Std.HashSet String)).contains x = true ↔ x ∈ l := by
  rw [foldl_insert_contains]
  simp

/-- A successful `mapM` pairs every input with its output. -/
theorem mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      ∃ ps : List (α × β), ps.map (·.1) = l ∧ ps.map (·.2) = r ∧ ∀ p ∈ ps, f p.1 = .ok p.2
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], rfl, h, by simp⟩
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => simp [ha, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [ha, hl, bind, Except.bind] at h
      | ok r' =>
        simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨ps, h1, h2, h3⟩ := mapM_ok hl
        refine ⟨(a, b) :: ps, by simp [h1], by simp [h2, h], ?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with hp | hp
        · subst hp; exact ha
        · exact h3 p hp

theorem mapM_ok_map {α β γ ε : Type} {f : α → Except ε β} {g : β → γ} {k : α → γ}
    (hg : ∀ a b, f a = .ok b → g b = k a) {l : List α} {r : List β} (h : l.mapM f = .ok r) :
    r.map g = l.map k := by
  obtain ⟨ps, h1, h2, h3⟩ := mapM_ok h
  subst h1 h2
  simp only [List.map_map]
  exact List.map_congr_left fun p hp => hg p.1 p.2 (h3 p hp)

theorem mem_dedupGo (x : String) : ∀ (l : List String) (s : Std.HashSet String),
    x ∈ dedupGo l s ↔ x ∈ l ∧ s.contains x = false
  | [], s => by simp [dedupGo]
  | y :: l, s => by
    unfold dedupGo
    by_cases hy : s.contains y = true
    · simp only [hy, ↓reduceIte]
      rw [mem_dedupGo x l s]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; rw [hy] at h2; cases h2
        · exact ⟨h1, h2⟩
    · simp only [hy, Bool.false_eq_true, ↓reduceIte]
      rw [List.mem_cons, mem_dedupGo x l (s.insert y), Std.HashSet.contains_insert]
      simp only [List.mem_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      constructor
      · rintro (h | ⟨h1, h2, h3⟩)
        · subst h; exact ⟨Or.inl rfl, by simpa using hy⟩
        · exact ⟨Or.inr h1, h3⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · by_cases hxy : x = y
          · exact Or.inl hxy
          · exact Or.inr ⟨h1, fun h => hxy h.symm, h2⟩

theorem mem_dedupFirst {x : String} {l : List String} : x ∈ dedupFirst l ↔ x ∈ l := by
  rw [dedupFirst, mem_dedupGo]
  simp

theorem mem_sortDedup {x : String} {l : List String} : x ∈ sortDedup l ↔ x ∈ l := by
  rw [sortDedup, List.mem_eraseDups, List.mem_mergeSort]

/-! ## The data closure -/

/-- **The names reachable from `roots`** through the relocations of the objects `ds`. -/
inductive Reach (ds : List DataObject) (roots : List String) : String → Prop
  | root {n : String} : n ∈ roots → Reach ds roots n
  | ref {o : DataObject} {n : String} : o ∈ ds → Reach ds roots o.name → n ∈ o.refs →
      Reach ds roots n

/-- A closed set holds every reachable name. -/
theorem closedB_reach {ds : List DataObject} {roots : List String} {s : Std.HashSet String}
    (h : closedB ds roots s = true) {n : String} (hr : Reach ds roots n) : s.contains n = true := by
  simp only [closedB, Bool.and_eq_true, List.all_eq_true] at h
  induction hr with
  | root hn => exact h.1 _ hn
  | ref ho _ hn ih =>
    have := h.2 _ ho
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at this
    rcases this with h' | h'
    · rw [ih] at h'; cases h'
    · exact h' _ hn

theorem mem_okData {o : DataObject} {ls : List String} :
    o ∈ okData (dataParsed ls) ↔ ∃ l ∈ ls, Clif.dataDirective l = some (.ok o) := by
  simp only [okData, dataParsed, List.mem_filterMap]
  constructor
  · rintro ⟨p, ⟨l, hl, hp⟩, ho⟩
    refine ⟨l, hl, ?_⟩
    cases hd : Clif.dataDirective l with
    | none => simp [hd] at hp
    | some r =>
      simp only [hd, Option.map_some, Option.some.injEq] at hp
      subst hp
      cases r with
      | ok o' => simp at ho; rw [ho]
      | error e => simp at ho
  · rintro ⟨l, hl, hd⟩
    exact ⟨(dataLineName l, .ok o), ⟨l, hl, by simp [hd]⟩, rfl⟩

theorem badLine_none {s : Std.HashSet String} {ps : List (String × Except String DataObject)}
    (h : badLine s ps = none) {n : String} {e : String} (hp : (n, .error e) ∈ ps) :
    s.contains n = false := by
  simp only [badLine, List.findSome?_eq_none_iff] at h
  have := h _ hp
  simp only at this
  by_cases hc : s.contains n = true
  · simp only [hc, ↓reduceIte] at this; cases this
  · simpa using hc

/-- What a decoded function file is: its dump's function in module identities renamed by the
unit's declarations, named as the bundle says, with the dump's header and the regalloc output. -/
theorem decodeFile_spec {ρ : Std.HashMap String String} {fd : FnFile × Dump}
    {r : Clif.Function × List String × String} (h : decodeFile ρ fd = .ok r) :
    r.1 = fd.2.raw.rename (lookupRen ρ) ∧ r.1.name = fd.1.name ∧ r.2.1 = fd.2.header ∧
      r.2.2 = fd.1.ra := by
  unfold decodeFile at h
  split at h
  · cases h
  · rename_i g hg
    split at h
    · rename_i hn
      cases h
      exact ⟨decodeFn_spec hg, hn, rfl, rfl⟩
    · cases h

/-- **A parsed unit.** -/
theorem parseUnit_spec {u : Cgu} {pu : PCgu} (h : parseUnit u = .ok pu) :
    ∃ ds ρ fs s, u.funcs.mapM readFile = .ok ds ∧ unitTable ds = .ok ρ ∧
      (u.funcs.zip ds).mapM (decodeFile ρ) = .ok fs ∧ pu.funcs = fs ∧
      pu.raw = ds.map Dump.raw ∧ pu.ren = lookupRen ρ ∧ pu.tag = u.tag ∧
      pu.locals = u.locals ∧ pu.names = u.names ∧
      closedB (okData (dataParsed u.data)) (rootsOf fs) s = true ∧
      pu.data = (okData (dataParsed u.data)).filter (s.contains ·.name) ∧
      badLine s (dataParsed u.data) = none ∧
      (pu.data.flatMap (·.names)).all (fun n => lookupRen ρ n == n) = true := by
  unfold parseUnit at h
  split at h
  · cases h
  · rename_i ds hds
    split at h
    · cases h
    · rename_i ρ hρ
      split at h
      · cases h
      · rename_i fs hfs
        simp only at h
        split at h
        · cases h
        · rename_i hc
          split at h
          · cases h
          · rename_i hb
            split at h
            · rename_i hfix
              cases h
              exact ⟨ds, ρ, fs, _, hds, hρ, hfs, rfl, rfl, rfl, rfl, rfl, rfl,
                by simpa using hc, rfl, hb, hfix⟩
            · cases h

/-- **A parsed unit's functions are cg_clif's, renamed by the unit's declarations.** -/
theorem parseUnit_raw {u : Cgu} {pu : PCgu} (h : parseUnit u = .ok pu) :
    pu.funcs.map (·.1) = pu.raw.map (·.rename pu.ren) := by
  obtain ⟨ds, ρ, fs, -, hds, -, hfs, hf, hr, hren, -⟩ := parseUnit_spec h
  rw [hf, hr, hren, List.map_map]
  have hlen : ds.length ≤ u.funcs.length := by
    obtain ⟨ps, h1, h2, -⟩ := mapM_ok hds
    rw [← h1, ← h2, List.length_map, List.length_map]
    exact Nat.le_refl _
  rw [mapM_ok_map (k := fun fd => fd.2.raw.rename (lookupRen ρ))
    (fun fd r hr => (decodeFile_spec hr).1) hfs]
  have : (u.funcs.zip ds).map (fun fd => fd.2.raw.rename (lookupRen ρ)) =
      ((u.funcs.zip ds).map Prod.snd).map (fun d => d.raw.rename (lookupRen ρ)) := by
    rw [List.map_map]; rfl
  rw [this, List.map_snd_zip hlen]
  rfl

/-- A parsed unit's data names are no declared external names: its renaming fixes them. -/
theorem parseUnit_fix {u : Cgu} {pu : PCgu} (h : parseUnit u = .ok pu) :
    ∀ n ∈ pu.data.flatMap (·.names), pu.ren n = n := by
  obtain ⟨ds, ρ, fs, -, -, -, -, -, -, hren, -, -, -, -, -, -, hfix⟩ := parseUnit_spec h
  intro n hn
  rw [hren]
  simpa using List.all_eq_true.mp hfix n hn

/-- **The data closure loses nothing**: every object of the unit's `; data:` lines that is
reachable from its functions' names through relocations is in the parsed unit's data. -/
theorem data_complete {u : Cgu} {pu : PCgu} (h : parseUnit u = .ok pu) {o : DataObject}
    (ho : o ∈ okData (dataParsed u.data))
    (hr : Reach (okData (dataParsed u.data)) (rootsOf pu.funcs) o.name) : o ∈ pu.data := by
  obtain ⟨-, -, fs, s, -, -, -, hf, -, -, -, -, -, hc, hd, -⟩ := parseUnit_spec h
  rw [hd]
  rw [hf] at hr
  exact List.mem_filter.mpr ⟨ho, closedB_reach hc hr⟩

/-- **The data closure is the unit's**: its objects are objects of the unit's lines. -/
theorem data_sound {u : Cgu} {pu : PCgu} (h : parseUnit u = .ok pu) {o : DataObject}
    (ho : o ∈ pu.data) : ∃ l ∈ u.data, Clif.dataDirective l = some (.ok o) := by
  obtain ⟨-, -, fs, s, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := parseUnit_spec h
  rw [hd] at ho
  exact mem_okData.mp (List.mem_filter.mp ho).1

/-- **No reachable data line fails to parse.** -/
theorem data_parses {u : Cgu} {pu : PCgu} (h : parseUnit u = .ok pu) {l e : String}
    (hl : l ∈ u.data) (he : Clif.dataDirective l = some (.error e)) :
    ¬ Reach (okData (dataParsed u.data)) (rootsOf pu.funcs) (dataLineName l) := by
  obtain ⟨-, -, fs, s, -, -, -, hf, -, -, -, -, -, hc, -, hb, -⟩ := parseUnit_spec h
  intro hr
  rw [hf] at hr
  have h1 := closedB_reach hc hr
  have h2 := badLine_none hb (n := dataLineName l) (e := e)
    (List.mem_filterMap.mpr ⟨l, hl, by simp [he]⟩)
  rw [h1] at h2; cases h2

/-! ## The scoping -/

theorem finOf_eq {us : List PCgu} {i : Nat} {u : PCgu} (h : us[i]? = some u) (n : String) :
    finOf us i n = u.fin n := by
  simp [finOf, h]

theorem mem_zipIdx {α : Type} {us : List α} {u : α} {i : Nat} : (u, i) ∈ us.zipIdx ↔ us[i]? = some u :=
  List.mem_zipIdx_iff_getElem?

theorem mem_localIds {us : List PCgu} {i : Nat} {n : String} :
    (i, n) ∈ localIds us ↔ ∃ u, us[i]? = some u ∧ n ∈ u.idents ∧ n ∈ u.localNames := by
  simp only [localIds, List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨u, i'⟩, hu, n', ⟨hn, hl⟩, rfl, rfl⟩
    exact ⟨u, mem_zipIdx.mp hu, hn, hl⟩
  · rintro ⟨u, hu, hn, hl⟩
    exact ⟨(u, i), mem_zipIdx.mpr hu, n, ⟨hn, hl⟩, rfl, rfl⟩

theorem mem_globalNames {us : List PCgu} {m : String} {j : Nat} {v : PCgu} (hv : us[j]? = some v)
    (hm : m ∈ v.idents) (hg : m ∉ v.localNames) : m ∈ globalNames us := by
  simp only [globalNames, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  exact ⟨v, List.mem_of_getElem? hv, hm, hg⟩

/-- Distinct images under a map without duplicates. -/
theorem inj_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: l, h, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (by rw [he]; exact List.mem_map_of_mem hb') h.1
    · subst hb'; exact absurd (by rw [← he]; exact List.mem_map_of_mem ha') h.1
    · exact inj_of_nodup_map h.2 ha' hb' he

/-- **The linked names are a scoping of the units** when `scopingB` holds. -/
theorem scopingB_sound {us : List PCgu} (h : scopingB us = true) : ScopingOk us (finOf us) := by
  simp only [scopingB, Bool.and_eq_true, List.all_eq_true, List.mem_filter, decide_eq_true_eq,
    beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hA, hB⟩, hC⟩ := h
  have hnd := nodupB_sound hB
  -- a global name keeps its name
  have hglob : ∀ {i u n}, us[i]? = some u → n ∈ u.idents → n ∉ u.localNames → finOf us i n = n :=
    fun {_ _ n} hu hn hl => by rw [finOf_eq hu]; exact hA _ (List.mem_of_getElem? hu) n ⟨hn, hl⟩
  -- a local symbol's name is no global name
  have hloc : ∀ {i u n}, us[i]? = some u → n ∈ u.idents → n ∈ u.localNames →
      finOf us i n ∉ globalNames us := fun {_ _ _} hu hn hl hg => by
    have := hC (_, _) (mem_localIds.mpr ⟨_, hu, hn, hl⟩)
    rw [(foldl_insert_empty _ _).mpr hg] at this
    cases this
  intro i j u v n m hu hv hn hm
  by_cases hln : n ∈ u.localNames <;> by_cases hlm : m ∈ v.localNames
  · -- both local
    have hi := mem_localIds.mpr ⟨_, hu, hn, hln⟩
    have hj := mem_localIds.mpr ⟨_, hv, hm, hlm⟩
    constructor
    · intro he
      have := inj_of_nodup_map hnd hi hj he
      simp only [Prod.mk.injEq] at this
      exact ⟨this.2, Or.inl this.1⟩
    · rintro ⟨rfl, hij | ⟨hn', -⟩⟩
      · subst hij; rfl
      · exact absurd hln hn'
  · -- local, global
    rw [hglob hv hm hlm]
    constructor
    · intro he; exact absurd (he ▸ mem_globalNames hv hm hlm) (hloc hu hn hln)
    · rintro ⟨rfl, hij | ⟨hn', -⟩⟩
      · subst hij; rw [hu] at hv; cases hv; exact absurd hln hlm
      · exact absurd hln hn'
  · -- global, local
    rw [hglob hu hn hln]
    constructor
    · intro he; exact absurd (he ▸ mem_globalNames hu hn hln) (hloc hv hm hlm)
    · rintro ⟨rfl, hij | ⟨-, hm'⟩⟩
      · subst hij; rw [hu] at hv; cases hv; exact absurd hlm hln
      · exact absurd hlm hm'
  · -- both global
    rw [hglob hu hn hln, hglob hv hm hlm]
    constructor
    · rintro rfl; exact ⟨rfl, Or.inr ⟨hln, hlm⟩⟩
    · exact fun h => h.1

/-! ## Alpha-equivalence of scopings -/

theorem GlobalValue.rename_rename (g h : String → String) (v : GlobalValue) :
    (v.rename g).rename h = v.rename (fun x => h (g x)) := by
  cases v <;> rfl

theorem GlobalValue.rename_congr {g g' : String → String} {v : GlobalValue}
    (hv : ∀ x, v.name? = some x → g x = g' x) : v.rename g = v.rename g' := by
  cases v <;> simp_all [GlobalValue.rename, GlobalValue.name?]

theorem Function.rename_rename (g h : String → String) (f : Clif.Function) :
    (f.rename g).rename h = f.rename (fun x => h (g x)) := by
  simp only [Clif.Function.rename, List.map_map, Function.comp_def, GlobalValue.rename_rename]
  rfl

theorem Function.rename_congr {g g' : String → String} {f : Clif.Function}
    (hf : ∀ x ∈ f.names, g x = g' x) : f.rename g = f.rename g' := by
  simp only [Clif.Function.names, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_filterMap] at hf
  simp only [Clif.Function.rename, ExtFunc.rename, RunCommand.rename]
  congr 1
  · exact hf _ (Or.inl rfl)
  · exact List.map_congr_left fun p hp => by
      rw [GlobalValue.rename_congr fun x hx => hf x (Or.inr (Or.inl (Or.inr ⟨p, hp, hx⟩)))]
  · exact List.map_congr_left fun p hp => by
      rw [hf _ (Or.inr (Or.inl (Or.inl ⟨p, hp, rfl⟩)))]
  · exact List.map_congr_left fun r hr => by
      rw [hf _ (Or.inr (Or.inr ⟨r, hr, rfl⟩))]

theorem DataObject.rename_rename (g h : String → String) (o : DataObject) :
    (o.rename g).rename h = o.rename (fun x => h (g x)) := by
  simp only [DataObject.rename, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by cases i <;> rfl

theorem DataObject.rename_congr {g g' : String → String} {o : DataObject}
    (ho : ∀ x ∈ o.names, g x = g' x) : o.rename g = o.rename g' := by
  simp only [DataObject.names, DataObject.refs, List.mem_cons, List.mem_filterMap] at ho
  simp only [DataObject.rename, DataObject.mk.injEq]
  refine ⟨ho _ (Or.inl rfl), trivial, trivial, List.map_congr_left fun i hi => ?_⟩
  cases i with
  | byte b => rfl
  | addr n off => simp only [DataItem.rename]; rw [ho n (Or.inr ⟨_, hi, rfl⟩)]

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, flatMap_congr_mem fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The (unit index, name) pairs of the units. -/
def allIds (us : List PCgu) : List (Nat × String) :=
  us.zipIdx.flatMap fun (u, i) => u.idents.map (i, ·)

theorem mem_allIds {us : List PCgu} {i : Nat} {n : String} :
    (i, n) ∈ allIds us ↔ ∃ u, us[i]? = some u ∧ n ∈ u.idents := by
  simp only [allIds, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨u, i'⟩, hu, n', hn, rfl, rfl⟩
    exact ⟨u, mem_zipIdx.mp hu, hn⟩
  · rintro ⟨u, hu, hn⟩
    exact ⟨(u, i), mem_zipIdx.mpr hu, n, hn, rfl, rfl⟩

/-- **Any two scopings give alpha-equivalent programs**: a bijection of names maps every name of
the units under `sc₁` to the same name under `sc₂`, and the program and data under `sc₂` are those
under `sc₁` renamed by it. -/
theorem link_alpha {us : List PCgu} {sc₁ sc₂ : Nat → String → String} (h₁ : ScopingOk us sc₁)
    (h₂ : ScopingOk us sc₂) :
    ∃ σ : Ren, (∀ i u n, us[i]? = some u → n ∈ u.idents → σ.fwd (sc₁ i n) = sc₂ i n) ∧
      link us sc₂ = (link us sc₁).rename σ.fwd ∧
      linkData us sc₂ = (linkData us sc₁).map (·.rename σ.fwd) := by
  let ps := (allIds us).map fun p => (sc₁ p.1 p.2, sc₂ p.1 p.2)
  have hc : Ren.Consistent ps := by
    intro a b a' b' ha hb
    simp only [ps, List.mem_map, Prod.mk.injEq] at ha hb
    obtain ⟨⟨i, n⟩, hin, rfl, rfl⟩ := ha
    obtain ⟨⟨j, m⟩, hjm, rfl, rfl⟩ := hb
    obtain ⟨u, hu, hn⟩ := mem_allIds.mp hin
    obtain ⟨v, hv, hm⟩ := mem_allIds.mp hjm
    rw [h₁ i j u v n m hu hv hn hm, h₂ i j u v n m hu hv hn hm]
  have hσ : ∀ i u n, us[i]? = some u → n ∈ u.idents → (Ren.ofPairs ps).fwd (sc₁ i n) = sc₂ i n :=
    fun i u n hu hn => Ren.ofPairs_fwd_of_consistent ps hc _ _
      (List.mem_map.mpr ⟨(i, n), mem_allIds.mpr ⟨u, hu, hn⟩, rfl⟩)
  refine ⟨Ren.ofPairs ps, hσ, ?_, ?_⟩
  · simp only [link, Program.rename, List.map_nil, List.map_flatMap, List.map_map]
    congr 1
    refine flatMap_congr_mem fun ⟨u, i⟩ hu => List.map_congr_left fun f hf => ?_
    have hu' := mem_zipIdx.mp hu
    simp only [Function.comp_apply, Function.rename_rename]
    exact (Function.rename_congr fun x hx => hσ i u x hu'
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨f, hf, hx⟩))).symm
  · simp only [linkData, List.map_flatMap, List.map_map]
    refine flatMap_congr_mem fun ⟨u, i⟩ hu => List.map_congr_left fun o ho => ?_
    have hu' := mem_zipIdx.mp hu
    simp only [Function.comp_apply, DataObject.rename_rename]
    exact (DataObject.rename_congr fun x hx => hσ i u x hu'
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, hx⟩))).symm

/-! ## The `LinkSpec` -/

theorem mkInput_src {hdr : List String} {g : Clif.Function} {ra : String} {fi : FnInput}
    (h : mkInput hdr g ra = .ok fi) : fi.src = g := by
  unfold mkInput at h
  dsimp only at h
  split at h
  · rename_i he; cases h; exact he
  · cases h

/-- What a successful `assemble` is made of. -/
theorem assemble_spec {b : Bundle} {A : Assembled} (h : assemble b = .ok A) :
    b.skipped = [] ∧ ∃ us fis, b.units.mapM parseUnit = .ok us ∧ scopingB us = true ∧
      (renamedOf us).mapM (fun x => mkInput x.1 x.2.1 x.2.2) = .ok fis ∧ A = assembled us fis := by
  unfold assemble at h
  split at h
  · cases h
  · rename_i hs
    refine ⟨hs, ?_⟩
    split at h
    · cases h
    · rename_i us hus
      split at h
      · cases h
      · rename_i hsc
        split at h
        · cases h
        · rename_i fis hfis
          cases h
          exact ⟨us, fis, hus, by simpa using hsc, hfis, rfl⟩

/-- What a successful `buildSpec` is made of. -/
theorem buildSpec_assemble {b : Bundle} {S : LinkSpec} (h : buildSpec b = .ok S) :
    ∃ A, assemble b = .ok A ∧ S.funcs = A.funcs ∧ S.names = A.names ∧ S.data = A.data ∧
      S.symNames = A.symNames := by
  unfold buildSpec at h
  split at h
  · cases h
  · rename_i A hA
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨A, hA, rfl, rfl, rfl, rfl⟩

theorem renamedOf_funcs (us : List PCgu) :
    (renamedOf us).map (·.2.1) = (link us (finOf us)).funcs := by
  simp only [renamedOf, link, List.map_flatMap, List.map_map]
  rfl

/-- **The `LinkSpec` of a bundle is the units' program under the linked names**: the units
parse (`parseUnit`: their data closures, `data_complete`), the linked names are a scoping
(`ScopingOk`), the functions' source (`FnInput.src`, what the compiler's theorems call the
source program) are the units' functions renamed to the linked names, in order, the data are
the units' data closures renamed, and every program function whose address the program's CLIF
or a data object takes is a symbol of the CLIF image. -/
theorem buildSpec_spec {b : Bundle} {S : LinkSpec} (h : buildSpec b = .ok S) :
    ∃ us, b.units.mapM parseUnit = .ok us ∧ ScopingOk us (finOf us) ∧
      S.funcs.map (·.src) = (link us (finOf us)).funcs ∧
      S.names = (link us (finOf us)).funcs.map (·.name) ∧
      S.data = linkData us (finOf us) ∧
      ∀ n ∈ S.names, ((∃ f ∈ (link us (finOf us)).funcs, n ∈ addrNamesOf f) ∨
        (∃ o ∈ S.data, n ∈ o.refs)) → n ∈ S.symNames := by
  obtain ⟨A, hA, hf, hn, hd, hs⟩ := buildSpec_assemble h
  obtain ⟨-, us, fis, hus, hsc, hfis, rfl⟩ := assemble_spec hA
  refine ⟨us, hus, scopingB_sound hsc, ?_, hn, hd, ?_⟩
  · rw [hf, ← renamedOf_funcs]
    exact mapM_ok_map (fun x fi hx => mkInput_src hx) hfis
  · intro n hnm hadr
    rw [hs]
    simp only [assembled] at hn hd ⊢
    rw [mem_dedupFirst, List.mem_append]
    rcases hadr with ⟨f, hf, hx⟩ | ⟨o, ho, hx⟩
    · exact Or.inl (List.mem_flatMap.mpr ⟨f, hf, hx⟩)
    · refine Or.inr ?_
      simp only [dataFnsOf, mem_sortDedup, List.mem_filter, List.mem_flatMap]
      rw [hd] at ho
      rw [hn] at hnm
      exact ⟨⟨o, ho, hx⟩, (foldl_insert_empty _ _).mpr hnm⟩

/-- The source program of a `LinkSpec`'s inputs is its functions' sources. -/
theorem srcProg_input0 (S : LinkSpec) : S.input0.srcProg = { funcs := S.funcs.map (·.src) } := rfl

/-- **The source program of the Lean-built `LinkSpec`** (of its compiler input
`S.input0`, and of every input with its functions: `S.input`, `S.inputCleanup`) is the units'
program under the linked names. -/
theorem buildSpec_srcProg {b : Bundle} {S : LinkSpec} (h : buildSpec b = .ok S) :
    ∃ us, b.units.mapM parseUnit = .ok us ∧ ScopingOk us (finOf us) ∧
      S.input0.srcProg = link us (finOf us) := by
  obtain ⟨us, hus, hsc, hsrc, -⟩ := buildSpec_spec h
  refine ⟨us, hus, hsc, ?_⟩
  rw [srcProg_input0, hsrc]
  rfl

/-! ## Deciding a scoping -/

/-- The local names of unit `i`. -/
def localsAt (us : List PCgu) (i : Nat) : List String := (us[i]?.map (·.localNames)).getD []

/-- **`sc` is a scoping of the units** (decided pairwise over their names; quadratic, for fixed
inputs: `scopingDecB_sound`). -/
def scopingDecB (us : List PCgu) (sc : Nat → String → String) : Bool :=
  (allIds us).all fun p => (allIds us).all fun q =>
    decide ((sc p.1 p.2 = sc q.1 q.2) ↔
      (p.2 = q.2 ∧ (p.1 = q.1 ∨ (p.2 ∉ localsAt us p.1 ∧ q.2 ∉ localsAt us q.1))))

theorem scopingDecB_sound {us : List PCgu} {sc : Nat → String → String}
    (h : scopingDecB us sc = true) : ScopingOk us sc := by
  intro i j u v n m hu hv hn hm
  have := List.all_eq_true.mp (List.all_eq_true.mp h _ (mem_allIds.mpr ⟨u, hu, hn⟩)) _
    (mem_allIds.mpr ⟨v, hv, hm⟩)
  simp only [localsAt, hu, hv, Option.map_some, Option.getD_some, decide_eq_true_eq] at this
  exact this

end Front

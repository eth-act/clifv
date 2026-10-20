import FV.Front.BundleProof

/-!
# The decoded units' program is cg_clif's program (T7c, docs/contracts/frontend.md)

cg_clif names code and data by **module identities** (`uNS:IDX`: a `FuncId` or `DataId` of the
codegen unit's module) and libcalls; its module declares a symbol for each, and the object binds
the identity to that symbol (`Linkage::Local`: a symbol local to the unit's object). The dump's
function in module identities is `Dump.raw`, a parsed unit's are `PCgu.raw`; `rawLink us sc` is
the units' program as cg_clif wrote it under a **naming** `sc` of those names.

* `RawScopingOk us sc`: `sc` names two names of the units alike exactly when cg_clif declared them
  as one symbol: the same symbol (`PCgu.ren`, the unit's declarations), in the same unit or
  global in both. This is the meaning of the identities in cranelift-module; it is defined
  without the decoding.
* **`rawLink_eq_link`**: for every such naming `sc` (of units that parse), the decoded units'
  program under the scoping `rawPull us sc` is cg_clif's program under `sc`:
  `link us (rawPull us sc) = rawLink us sc`, and `rawPull us sc` is a scoping. So every theorem
  about `link us sc'` for an arbitrary scoping `sc'` — the executable theorems `bundle_correct_*`
  — is a theorem about cg_clif's program under any naming that respects its declarations
  (`FV/Front/Exe.lean`, `bundle_correct_raw`).
* `raw_alpha`: such a naming's program is alpha-equivalent to the linked one (for `hσ`);
  `rawScoping_of`: the declarations followed by a scoping are such a naming (non-vacuity: e.g. the
  linked names, `finOf`), and cg_clif's program under it is the decoded one under the scoping
  (`rawLink_decl`).
-/

namespace Front

open Clif

/-! ## Renaming and names -/

theorem GlobalValue.name?_rename (g : String → String) (v : GlobalValue) :
    (v.rename g).name? = v.name?.map g := by
  cases v <;> rfl

/-- The names of a renamed function are its names renamed. -/
theorem Function.names_rename (g : String → String) (f : Clif.Function) :
    (f.rename g).names = f.names.map g := by
  simp only [Clif.Function.names, Clif.Function.rename, List.map_cons, List.map_append,
    List.map_map, List.map_filterMap, List.filterMap_map, Function.comp_def,
    GlobalValue.name?_rename, ExtFunc.rename, RunCommand.rename]

/-! ## Units -/

/-- What a parsed unit is (`parseUnit_raw`, `parseUnit_fix`): its functions cg_clif's renamed by
its declarations, its data names fixed by them. -/
structure UnitOk (u : PCgu) : Prop where
  raw : u.funcs.map (·.1) = u.raw.map (·.rename u.ren)
  fix : ∀ n ∈ u.data.flatMap (·.names), u.ren n = n

theorem parseUnit_ok {u : Cgu} {pu : PCgu} (h : parseUnit u = .ok pu) : UnitOk pu :=
  ⟨parseUnit_raw h, parseUnit_fix h⟩

/-- The units of a bundle that parse are `UnitOk`. -/
theorem units_ok {cs : List Cgu} {us : List PCgu} (h : cs.mapM parseUnit = .ok us) :
    ∀ u ∈ us, UnitOk u := by
  obtain ⟨ps, -, h2, h3⟩ := mapM_ok h
  intro u hu
  rw [← h2] at hu
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
  exact parseUnit_ok (h3 p hp)

/-- **The names of a unit as cg_clif wrote it**: its functions' (module identities, libcalls) and
its data closure's. -/
def PCgu.rawIdents (u : PCgu) : List String :=
  u.raw.flatMap (·.names) ++ u.data.flatMap (·.names)

/-- The decoded names of a unit are its raw names renamed. -/
theorem UnitOk.idents_of {u : PCgu} (hu : UnitOk u) {n : String} (hn : n ∈ u.idents) :
    ∃ a ∈ u.rawIdents, u.ren a = n := by
  simp only [PCgu.idents, List.mem_append] at hn
  rcases hn with hn | hn
  · have : n ∈ (u.funcs.map (·.1)).flatMap (·.names) := by
      simpa [List.flatMap_map] using hn
    rw [hu.raw] at this
    simp only [List.flatMap_map, Function.names_rename, List.mem_flatMap, List.mem_map] at this
    obtain ⟨f, hf, a, ha, rfl⟩ := this
    exact ⟨a, List.mem_append_left _ (List.mem_flatMap.mpr ⟨f, hf, ha⟩), rfl⟩
  · exact ⟨n, List.mem_append_right _ hn, hu.fix n hn⟩

/-- A raw name renamed is a decoded name. -/
theorem UnitOk.ren_mem {u : PCgu} (hu : UnitOk u) {a : String} (ha : a ∈ u.rawIdents) :
    u.ren a ∈ u.idents := by
  simp only [PCgu.rawIdents, List.mem_append] at ha
  rcases ha with ha | ha
  · obtain ⟨f, hf, ha⟩ := List.mem_flatMap.mp ha
    have : u.ren a ∈ (u.raw.map (·.rename u.ren)).flatMap (·.names) := by
      simp only [List.flatMap_map, Function.names_rename, List.mem_flatMap, List.mem_map]
      exact ⟨f, hf, a, ha, rfl⟩
    rw [← hu.raw] at this
    simp only [PCgu.idents, List.mem_append]
    exact Or.inl (by simpa [List.flatMap_map] using this)
  · rw [hu.fix a ha]
    exact List.mem_append_right _ ha

/-- A raw name of `u` that `u.ren` takes to `n` (`n` itself if none). -/
def PCgu.pre (u : PCgu) (n : String) : String :=
  (u.rawIdents.find? (fun a => u.ren a == n)).getD n

theorem UnitOk.pre_spec {u : PCgu} (hu : UnitOk u) {n : String} (hn : n ∈ u.idents) :
    u.pre n ∈ u.rawIdents ∧ u.ren (u.pre n) = n := by
  obtain ⟨a, ha, han⟩ := hu.idents_of hn
  unfold PCgu.pre
  cases hf : u.rawIdents.find? (fun a => u.ren a == n) with
  | none =>
    have := List.find?_eq_none.mp hf a ha
    simp [han] at this
  | some b =>
    have hb := List.find?_some hf
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using hb⟩

/-! ## Namings of cg_clif's program -/

/-- **A naming of cg_clif's program**: two names of the units (as cg_clif wrote them) are named
alike exactly when they denote one symbol — the same declared symbol (`PCgu.ren`), in the same
unit or global (not a local symbol of its unit's object) in both. -/
def RawScopingOk (us : List PCgu) (sc : Nat → String → String) : Prop :=
  ∀ i j u v a b, us[i]? = some u → us[j]? = some v → a ∈ u.rawIdents → b ∈ v.rawIdents →
    (sc i a = sc j b ↔ u.ren a = v.ren b ∧
      (i = j ∨ (u.ren a ∉ u.localNames ∧ v.ren b ∉ v.localNames)))

/-- The scoping of the decoded units that a naming of cg_clif's program induces: a decoded name
is named as a raw name it decodes from. -/
def rawPull (us : List PCgu) (sc : Nat → String → String) (i : Nat) (n : String) : String :=
  match us[i]? with
  | some u => sc i (u.pre n)
  | none => sc i n

theorem rawPull_eq {us : List PCgu} {sc : Nat → String → String} {i : Nat} {u : PCgu}
    (hu : us[i]? = some u) (n : String) : rawPull us sc i n = sc i (u.pre n) := by
  simp [rawPull, hu]

/-- **The decoded units' program is cg_clif's program**: for a naming `sc` of cg_clif's program,
`rawPull us sc` is a scoping of the decoded units, and the decoded units' program under it is
cg_clif's program under `sc`. -/
theorem rawLink_eq_link {us : List PCgu} (hok : ∀ u ∈ us, UnitOk u)
    {sc : Nat → String → String} (h : RawScopingOk us sc) :
    ScopingOk us (rawPull us sc) ∧ link us (rawPull us sc) = rawLink us sc := by
  constructor
  · intro i j u v n m hu hv hn hm
    have hu' := hok u (List.mem_of_getElem? hu)
    have hv' := hok v (List.mem_of_getElem? hv)
    obtain ⟨ha, hna⟩ := hu'.pre_spec hn
    obtain ⟨hb, hmb⟩ := hv'.pre_spec hm
    rw [rawPull_eq hu, rawPull_eq hv, h i j u v _ _ hu hv ha hb, hna, hmb]
  · simp only [link, rawLink, Clif.Program.mk.injEq]
    refine ⟨trivial, trivial, flatMap_congr_mem fun ⟨u, i⟩ hui => ?_⟩
    have hu := mem_zipIdx.mp hui
    have hu' := hok u (List.mem_of_getElem? hu)
    have : u.funcs.map (fun f => f.1.rename (rawPull us sc i)) =
        (u.funcs.map (·.1)).map (·.rename (rawPull us sc i)) := by
      rw [List.map_map]; rfl
    rw [this, hu'.raw, List.map_map]
    refine List.map_congr_left fun f hf => ?_
    simp only [Function.comp_apply, Function.rename_rename]
    refine Function.rename_congr fun x hx => ?_
    have hx' : x ∈ u.rawIdents := List.mem_append_left _ (List.mem_flatMap.mpr ⟨f, hf, hx⟩)
    obtain ⟨hp, hpx⟩ := hu'.pre_spec (hu'.ren_mem hx')
    rw [rawPull_eq hu]
    exact (h i i u u _ _ hu hu hp hx').mpr ⟨hpx, Or.inl rfl⟩

/-- **The declarations followed by a scoping name cg_clif's program** (non-vacuity of
`RawScopingOk`): for a scoping `sc` of the decoded units, `fun i a => sc i (ren_i a)`. -/
theorem rawScoping_of {us : List PCgu} (hok : ∀ u ∈ us, UnitOk u) {sc : Nat → String → String}
    (h : ScopingOk us sc) :
    RawScopingOk us (fun i a => match us[i]? with | some u => sc i (u.ren a) | none => sc i a) := by
  intro i j u v a b hu hv ha hb
  simp only [hu, hv]
  exact h i j u v _ _ hu hv ((hok u (List.mem_of_getElem? hu)).ren_mem ha)
    ((hok v (List.mem_of_getElem? hv)).ren_mem hb)

/-- **cg_clif's program under a naming is alpha-equivalent to the linked one** (`link_alpha`). -/
theorem raw_alpha {us : List PCgu} (hok : ∀ u ∈ us, UnitOk u) (hfin : ScopingOk us (finOf us))
    {sc : Nat → String → String} (h : RawScopingOk us sc) :
    ∃ σ : Ren, link us (finOf us) = (rawLink us sc).rename σ.fwd := by
  obtain ⟨hs, he⟩ := rawLink_eq_link hok h
  obtain ⟨σ, -, hl, -⟩ := link_alpha hs hfin
  exact ⟨σ, by rw [hl, he]⟩

/-- **cg_clif's program with every module identity named by its declared symbol** (then by `sc`)
is the decoded units' program under `sc` (`PCgu.raw` renamed by `PCgu.ren`: `parseUnit_raw`). -/
theorem rawLink_decl {us : List PCgu} (hok : ∀ u ∈ us, UnitOk u) (sc : Nat → String → String) :
    rawLink us (fun i a => match us[i]? with | some u => sc i (u.ren a) | none => sc i a) =
      link us sc := by
  simp only [link, rawLink, Clif.Program.mk.injEq]
  refine ⟨trivial, trivial, flatMap_congr_mem fun ⟨u, i⟩ hui => ?_⟩
  have hu := mem_zipIdx.mp hui
  have hu' := hok u (List.mem_of_getElem? hu)
  simp only [hu]
  have : u.funcs.map (fun f => f.1.rename (sc i)) = (u.funcs.map (·.1)).map (·.rename (sc i)) := by
    rw [List.map_map]; rfl
  rw [this, hu'.raw, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_apply, Function.rename_rename]

end Front

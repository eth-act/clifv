import FV.E2E.LinkCheckFast

/-! # The link checks' scans over the program, indexed (#1062)

`linkChksWith` tests every `blr` site against every function of the program (`blrOk`'s
`P.funcs.all`: the functions the site may enter, `may`), `indFastB` every function of the program
against `g`'s indirect calls, and `raCallFastB` every call's return address against every
function of the table (`E.all`): per call site a scan of the program, 30-45% of `lean-link`'s and
`link-check`'s time on 20k-31k-function executables (#1076).

`LinkIdx.of P E` groups the program's functions by name and by parameter types, and the table's
code ranges by 4 KiB page: `may h` needs `g` to declare `h`'s name or one of `g`'s indirect-call
signatures to have `h`'s parameter types (`LinkSys.IndSigMatch.ty`), so the functions of
`LinkIdx.cands` are the only ones the scans can fail on (`all_sub_eq`); a return address `r` is
inside the code of a function only if that function fits the address space and `r`'s page is
one of its pages (or it does not fit, `unfit`). `linkChksWithI C (LinkIdx.of P C.ents) P g r =
linkChksWith C P g r` (`linkChksWithI_of`). No statement changes.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof

/-! ## Grouping a list by keys -/

/-- `x` added to the group of each of its keys `keys x`. -/
def groupInto {α K : Type} [BEq K] [Hashable K] (keys : α → List K)
    (m : Std.HashMap K (List α)) (x : α) : Std.HashMap K (List α) :=
  (keys x).foldl (fun m k => m.insert k (x :: m.getD k [])) m

/-- The elements of `l` by key: `y` is in the group of `k` iff `y ∈ l` and `k ∈ keys y`
(`mem_groupMulti`). -/
def groupMulti {α K : Type} [BEq K] [Hashable K] (keys : α → List K) (l : List α) :
    Std.HashMap K (List α) :=
  l.foldl (groupInto keys) {}

section
variable {α K : Type} [BEq K] [Hashable K] [LawfulBEq K]

theorem mem_groupInto_foldl (x y : α) (k : K) : ∀ (ks : List K) (m : Std.HashMap K (List α)),
    y ∈ (ks.foldl (fun m k' => m.insert k' (x :: m.getD k' [])) m).getD k [] ↔
      y ∈ m.getD k [] ∨ (y = x ∧ k ∈ ks)
  | [], m => by simp
  | k' :: ks, m => by
    rw [List.foldl_cons, mem_groupInto_foldl x y k ks, Std.HashMap.getD_insert]
    by_cases h : k' = k
    · subst h
      by_cases hy : y = x
      · subst hy; simp
      · simp [hy]
    · by_cases hy : y = x
      · simp [h, Ne.symm h, hy]
      · simp [h, hy]

theorem mem_groupMulti_foldl (keys : α → List K) (y : α) (k : K) :
    ∀ (l : List α) (m : Std.HashMap K (List α)),
      y ∈ (l.foldl (groupInto keys) m).getD k [] ↔ y ∈ m.getD k [] ∨ (y ∈ l ∧ k ∈ keys y)
  | [], m => by simp
  | x :: l, m => by
    rw [List.foldl_cons, mem_groupMulti_foldl keys y k l, groupInto, mem_groupInto_foldl]
    by_cases hy : y = x
    · subst hy
      constructor
      · rintro ((h | ⟨-, h⟩) | ⟨-, h⟩)
        · exact .inl h
        · exact .inr ⟨List.mem_cons.2 (.inl rfl), h⟩
        · exact .inr ⟨List.mem_cons.2 (.inl rfl), h⟩
      · rintro (h | ⟨-, h⟩)
        · exact .inl (.inl h)
        · exact .inl (.inr ⟨rfl, h⟩)
    · simp [hy]

theorem mem_groupMulti (keys : α → List K) (l : List α) (y : α) (k : K) :
    y ∈ (groupMulti keys l).getD k [] ↔ y ∈ l ∧ k ∈ keys y := by
  simp [groupMulti, mem_groupMulti_foldl]

end

/-- A scan over `l` of a test that fails only on elements of `c ⊆ l` is the scan over `c`. -/
theorem all_sub_eq {α : Type} {l c : List α} {p : α → Bool}
    (hc : ∀ x ∈ l, p x = false → x ∈ c) (hs : ∀ x ∈ c, x ∈ l) : l.all p = c.all p := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  constructor
  · intro h x hx
    exact h x (hs x hx)
  · intro h x hx
    cases hp : p x with
    | false =>
      have := h x (hc x hx hp)
      rw [hp] at this
      exact this
    | true => rfl

/-! ## The index -/

/-- The 4 KiB pages of a function's code range that fits the address space (none otherwise). -/
def RaEnt.pages (x : RaEnt) : List Nat :=
  if x.fits then List.range' (x.lo / 4096) ((x.hi - 1) / 4096 + 1 - x.lo / 4096) else []

/-- **The program's functions and the table's code ranges, indexed** (`LinkIdx.of`). -/
structure LinkIdx where
  /-- the program's functions by name -/
  byName : Std.HashMap String (List Clif.Function)
  /-- the program's functions by parameter types (`Clif.AbiParam.tys`) -/
  bySig : Std.HashMap (List Clif.Ty) (List Clif.Function)
  /-- the table's entries whose code range does not fit the address space -/
  unfit : List RaEnt
  /-- the table's other entries by the pages of their code range (`RaEnt.pages`) -/
  pages : Std.HashMap Nat (List RaEnt)

/-- The index of the program `P` and the table's code ranges `E`. -/
def LinkIdx.of (P : Clif.Program) (E : List RaEnt) : LinkIdx where
  byName := groupMulti (fun h => [h.name]) P.funcs
  bySig := groupMulti (fun h => [Clif.AbiParam.tys h.sig.params]) P.funcs
  unfit := E.filter (!·.fits)
  pages := groupMulti RaEnt.pages E

/-- The functions `g`'s `blr` sites and indirect calls (with signatures `sigs`) can enter: the
ones `g` declares and the ones with the parameter types of one of `sigs` (`mem_cands`). -/
def LinkIdx.cands (X : LinkIdx) (g : Clif.Function) (sigs : List Clif.Signature) :
    List Clif.Function :=
  g.externs.flatMap (fun e => X.byName.getD e.2.name []) ++
    sigs.flatMap (fun s => X.bySig.getD (Clif.AbiParam.tys s.params) [])

/-- The table's entries whose code range may contain the address `r`. -/
def LinkIdx.near (X : LinkIdx) (r : Nat) : List RaEnt :=
  X.unfit ++ X.pages.getD (r / 4096) []

theorem mem_cands {P : Clif.Program} {E : List RaEnt} {g : Clif.Function}
    {sigs : List Clif.Signature} {h : Clif.Function} (hh : h ∈ P.funcs)
    (hc : (declSet g).contains h.name = true ∨ ∃ s ∈ sigs, LinkSys.IndTyMatch s h) :
    h ∈ (LinkIdx.of P E).cands g sigs := by
  unfold LinkIdx.cands
  rcases hc with hd | ⟨s, hs, hm⟩
  · have hd' : declB g h.name = true := by rw [← declSet_contains]; exact hd
    simp only [declB, List.any_eq_true, beq_iff_eq] at hd'
    obtain ⟨e, he, hen⟩ := hd'
    refine List.mem_append_left _ (List.mem_flatMap.2 ⟨e, he, ?_⟩)
    simp only [LinkIdx.of, mem_groupMulti, List.mem_singleton]
    exact ⟨hh, hen⟩
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨s, hs, ?_⟩)
    simp only [LinkIdx.of, mem_groupMulti, List.mem_singleton]
    exact ⟨hh, hm.symm⟩

theorem cands_sub {P : Clif.Program} {E : List RaEnt} {g : Clif.Function}
    {sigs : List Clif.Signature} {h : Clif.Function} (hx : h ∈ (LinkIdx.of P E).cands g sigs) :
    h ∈ P.funcs := by
  simp only [LinkIdx.cands, LinkIdx.of, List.mem_append, List.mem_flatMap, mem_groupMulti] at hx
  rcases hx with ⟨_, _, h1, _⟩ | ⟨_, _, h1, _⟩ <;> exact h1

theorem indTo_cands {P : Clif.Program} (E : List RaEnt) (S : String → Option Nat) (ind : Bool)
    (g : Clif.Function) (sigs : List Clif.Signature) {h : Clif.Function} (hh : h ∈ P.funcs)
    (hm : indToWithB S ind (fun n => (declSet g).contains n) sigs g h = true) :
    h ∈ (LinkIdx.of P E).cands g sigs := by
  apply mem_cands hh
  simp only [indToWithB, indMatchWithB, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at hm
  rcases hm with ⟨-, ⟨hd, -⟩ | ⟨s, hs, hsm, -⟩⟩
  · exact .inl hd
  · exact .inr ⟨s, hs, hsm.ty⟩

theorem indSig_cands {P : Clif.Program} (E : List RaEnt) (g : Clif.Function)
    (sigs : List Clif.Signature) {h : Clif.Function} (hh : h ∈ P.funcs)
    (hm : indSigWithB (fun n => (declSet g).contains n) sigs h = true) :
    h ∈ (LinkIdx.of P E).cands g sigs := by
  apply mem_cands hh
  simp only [indSigWithB, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at hm
  rcases hm with ⟨s, hs, hsm⟩ | ⟨hd, -⟩
  · exact .inr ⟨s, hs, hsm.ty⟩
  · exact .inl hd

theorem near_all_eq (P : Clif.Program) (E : List RaEnt) (gn : String) (pc : BitVec 64) (r : Nat) :
    ((LinkIdx.of P E).near r).all (fun x => x.okAt gn pc r) = E.all (fun x => x.okAt gn pc r) := by
  refine (all_sub_eq (fun x hx hp => ?_) (fun x hx => ?_)).symm
  · simp only [LinkIdx.near, LinkIdx.of, List.mem_append, List.mem_filter, mem_groupMulti]
    cases hf : x.fits
    · exact .inl ⟨hx, by simp⟩
    · refine .inr ⟨hx, ?_⟩
      simp only [RaEnt.okAt, hf, Bool.true_and, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        Nat.not_lt, Nat.not_le] at hp
      obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hp
      simp only [RaEnt.pages, hf, ↓reduceIte, List.mem_range'_1]
      omega
  · simp only [LinkIdx.near, LinkIdx.of, List.mem_append, List.mem_filter, mem_groupMulti] at hx
    rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact h1

/-! ## The checks with the index -/

/-- **`raCallFastB` with the table's code ranges by page** (`raCallIdxB_eq`): a call's return
address is tested against the functions whose code may contain it (`LinkIdx.near`). -/
def raCallIdxB (X : LinkIdx) (g : Clif.Function) (a : Art) : Bool :=
  let offs := (offsList a.fa.lines.toList 0).toArray
  let gn := g.name
  (List.range a.fa.lines.size).all fun j =>
    match a.fa.lines[j]? with
    | some l => !callLine l ||
        let pc := a.base + BitVec.ofNat 64 (offs[j]?.getD 0)
        let r := (pc + 4).toNat
        (X.near r).all fun x => x.okAt gn pc r
    | none => true

theorem raCallIdxB_eq (P : Clif.Program) (E : List RaEnt) (g : Clif.Function) (a : Art) :
    raCallIdxB (LinkIdx.of P E) g a = raCallFastB E g a := by
  simp only [raCallIdxB, raCallFastB, near_all_eq]
  rfl

theorem blrOk_restrict {P P' : Clif.Program} {may : Clif.Function → Bool}
    (hc : ∀ h ∈ P.funcs, may h = true → h ∈ P'.funcs) (hs : ∀ h ∈ P'.funcs, h ∈ P.funcs)
    (got : Nat → Option String) (info : CallInfo) :
    blrOk P' may got info = blrOk P may got info := by
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only [blrOk]
        rw [all_sub_eq (l := P.funcs) (c := P'.funcs) ?_ hs]
        intro x hx hp
        apply hc x hx
        cases hm : may x
        · simp [hm] at hp
        · rfl
    | _ => rfl

theorem siteWithOk_restrict (F : String → Option Clif.Function) {P P' : Clif.Program}
    (g : Clif.Function) {may : Clif.Function → Bool}
    (hc : ∀ h ∈ P.funcs, may h = true → h ∈ P'.funcs) (hs : ∀ h ∈ P'.funcs, h ∈ P.funcs)
    (vc : VCode) : siteWithOk F P' g may vc = siteWithOk F P g may vc := by
  funext info
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r => exact blrOk_restrict hc hs _ _

theorem indWithB_restrict {P P' : Clif.Program} (S : String → Option Nat) (ind : Bool)
    (D : String → Bool) (sigs : List Clif.Signature)
    (hc : ∀ h ∈ P.funcs, indSigWithB D sigs h = true → h ∈ P'.funcs)
    (hs : ∀ h ∈ P'.funcs, h ∈ P.funcs) :
    indWithB P' S ind D sigs = indWithB P S ind D sigs := by
  unfold indWithB
  rw [all_sub_eq (l := P.funcs) (c := P'.funcs) ?_ hs]
  intro x hx hp
  apply hc x hx
  cases hm : indSigWithB D sigs x
  · simp [hm] at hp
  · rfl

/-- The program `P` restricted to the functions `g` (with indirect-call signatures `sigs`) may
enter through an address. -/
def LinkIdx.progFor (X : LinkIdx) (P : Clif.Program) (g : Clif.Function)
    (sigs : List Clif.Signature) : Clif.Program :=
  { P with funcs := X.cands g sigs }

theorem siteWithOk_progFor (F : String → Option Clif.Function) (P : Clif.Program) (E : List RaEnt)
    (S : String → Option Nat) (ind : Bool) (g : Clif.Function) (sigs : List Clif.Signature)
    (vc : VCode) :
    siteWithOk F ((LinkIdx.of P E).progFor P g sigs) g
        (indToWithB S ind (fun n => (declSet g).contains n) sigs g) vc =
      siteWithOk F P g (indToWithB S ind (fun n => (declSet g).contains n) sigs g) vc :=
  siteWithOk_restrict F g (fun _ hh hm => indTo_cands E S ind g sigs hh hm)
    (fun _ hh => cands_sub hh) vc

theorem indWithB_progFor (P : Clif.Program) (E : List RaEnt) (S : String → Option Nat)
    (ind : Bool) (g : Clif.Function) (sigs : List Clif.Signature) :
    indWithB ((LinkIdx.of P E).progFor P g sigs) S ind (fun n => (declSet g).contains n) sigs =
      indWithB P S ind (fun n => (declSet g).contains n) sigs :=
  indWithB_restrict S ind _ sigs (fun _ hh hm => indSig_cands E g sigs hh hm)
    (fun _ hh => cands_sub hh)

/-- **`linkChksWith` with the index `X`** (`linkChksWithI_of`: at `X = LinkIdx.of P C.ents`,
`linkChksWith`). -/
def linkChksWithI (C : LinkCtx) (X : LinkIdx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  let Pg := X.progFor P g sigs
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOk C.F Pg g may a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indWithB Pg C.S (indFreeB g) (fun n => Ds.contains n) sigs)]

theorem linkChksWithI_of (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) :
    linkChksWithI C (LinkIdx.of P C.ents) P g r = linkChksWith C P g r := by
  simp only [linkChksWithI, linkChksWith, siteWithOk_progFor, indWithB_progFor, raCallIdxB_eq,
    indFastB]

end E2E.LinkCheck

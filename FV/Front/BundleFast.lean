import FV.Front.BundleProof
import FV.E2E.LinkScopeFast

/-! # The bundle assembled with hash maps and in parallel (#1077: ruint, 232,604 functions)

`Front.assemble` looks names up in lists: `PCgu.fin` scans the unit's merge names and local
symbols (`List.lookup`) for every name a function uses, in `scopingB`, `renamedOf` and `link`;
`localIds` and `sortDedup` remove duplicates with `List.eraseDups` (a scan of the kept elements
per element). On ruint's test executable one unit holds 191,432 functions, 415,252 merge names,
686,881 local symbols and the units 2,361,116 names in use: `lean-link` was still in `scopingB`
after an hour. The replacements below compute the same values with hash maps (`assocMap`) and
hash sets, decode and print the functions in parallel tasks (`Link.parMap`), and rename every
function once (`link us (finOf us)`'s functions are `renamedOf us`'s: `renamedOf_funcs`).

Every replacement is a new definition proved equal to the original and swapped in with
`@[csimp]` (the kernel and every theorem see the original definitions). `assemble` and
`buildSpec` are compiled in `FV/Front/Bundle.lean`, before these lemmas: their copies here
(`assembleF`, `buildSpecF`) are compiled with them, and the executables that import this file
(`lean-link`, `link-check`) run those. No statement changes.
-/

namespace Front

open Clif E2E.LinkCheck Link

/-! ## Duplicates removed with a hash set -/

/-- `List.eraseDupsBy.loop (· == ·)` with the kept elements also in the hash set `s`. -/
def eraseDupsGo {α : Type} [BEq α] [Hashable α] : List α → Std.HashSet α → List α → List α
  | [], _, bs => bs.reverse
  | a :: as, s, bs =>
    if s.contains a then eraseDupsGo as s bs else eraseDupsGo as (s.insert a) (a :: bs)

/-- `l.eraseDups` in linear time (`eraseDupsH_eq`). -/
def eraseDupsH {α : Type} [BEq α] [Hashable α] (l : List α) : List α := eraseDupsGo l {} []

theorem eraseDupsGo_eq {α : Type} [BEq α] [Hashable α] [LawfulBEq α] :
    ∀ (as : List α) (s : Std.HashSet α) (bs : List α),
      (∀ x, s.contains x = bs.any (fun b => x == b)) →
      eraseDupsGo as s bs = List.eraseDupsBy.loop (· == ·) as bs
  | [], _, _, _ => by simp [eraseDupsGo, List.eraseDupsBy.loop]
  | a :: as, s, bs, h => by
    rw [eraseDupsGo, List.eraseDupsBy.loop, h a]
    cases hb : bs.any (fun b => a == b)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply eraseDupsGo_eq
      intro x
      rw [Std.HashSet.contains_insert, h x, List.any_cons]
      by_cases hx : x = a
      · subst hx; simp
      · have h1 : (a == x) = false := by simpa using Ne.symm hx
        have h2 : (x == a) = false := by simpa using hx
        simp [h1, h2]
    · simp only [↓reduceIte]
      exact eraseDupsGo_eq as s bs h

theorem eraseDupsH_eq {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (l : List α) :
    eraseDupsH l = l.eraseDups :=
  eraseDupsGo_eq l {} [] (by simp)

/-- `sortDedup` with `eraseDupsH`. -/
def sortDedupF (l : List String) : List String :=
  eraseDupsH (l.mergeSort fun a b => decide (a ≤ b))

@[csimp] theorem sortDedup_eq_F : @sortDedup = @sortDedupF := by
  funext l
  simp only [sortDedup, sortDedupF, eraseDupsH_eq]

/-- `localIds` with `eraseDupsH`. -/
def localIdsF (us : List PCgu) : List (Nat × String) :=
  eraseDupsH (us.zipIdx.flatMap fun (u, i) => u.localIdents.map (i, ·))

@[csimp] theorem localIds_eq_F : @localIds = @localIdsF := by
  funext us
  simp only [localIds, localIdsF, eraseDupsH_eq]

/-- `dataFnsOf`, compiled here (with `sortDedupF`). -/
def dataFnsOfF (names : List String) (D : List DataObject) : List String :=
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  sortDedup ((D.flatMap (·.refs)).filter nameSet.contains)

@[csimp] theorem dataFnsOf_eq_F : @dataFnsOf = @dataFnsOfF := rfl

/-! ## The linked names with hash maps -/

/-- A unit's naming tables: its merge names and its local symbols as hash maps, its tag. -/
structure FinTab where
  names : Std.HashMap String String
  locals : Std.HashMap String String
  tag : String

/-- The naming tables of `u`. -/
def PCgu.finTab (u : PCgu) : FinTab :=
  { names := assocMap u.names, locals := assocMap u.locals, tag := u.tag }

/-- `PCgu.fin` through the tables (`PCgu.finTab_fin`). -/
def FinTab.fin (t : FinTab) (n : String) : String :=
  match t.names[n]? with
  | some f => f
  | none => match t.locals[n]? with
    | some o => o ++ "@" ++ t.tag
    | none => n

theorem PCgu.finTab_fin (u : PCgu) (n : String) : u.finTab.fin n = u.fin n := by
  simp only [FinTab.fin, PCgu.finTab, PCgu.fin, assocMap_get]
  all_goals rfl

/-- `finOf` through the units' tables (`finOfT_eq`). -/
def finOfT (ts : Array FinTab) (i : Nat) (n : String) : String :=
  match ts[i]? with
  | some t => t.fin n
  | none => n

theorem finOfT_eq (us : List PCgu) : finOfT (us.map PCgu.finTab).toArray = finOf us := by
  funext i n
  simp only [finOfT, finOf, List.getElem?_toArray, List.getElem?_map]
  cases us[i]? <;> simp [PCgu.finTab_fin]

theorem all_zip_map {α β : Type} (l : List α) (f : α → β) (p : α × β → Bool) :
    (l.zip (l.map f)).all p = l.all fun a => p (a, f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zip_cons_cons, List.all_cons, ih]

/-- `scopingB` with the units' naming tables. -/
def scopingBF (us : List PCgu) : Bool :=
  let ts := us.map PCgu.finTab
  (us.zip ts).all (fun p => p.1.globalIdents.all fun n => p.2.fin n == n) &&
  let sc := finOfT ts.toArray
  let ls := localIds us
  nodupB (ls.map fun p => sc p.1 p.2) &&
  let g : Std.HashSet String := (globalNames us).foldl (·.insert ·) {}
  ls.all fun p => !g.contains (sc p.1 p.2)

@[csimp] theorem scopingB_eq_F : @scopingB = @scopingBF := by
  funext us
  simp only [scopingB, scopingBF, finOfT_eq, all_zip_map, PCgu.finTab_fin]

/-! ## Parsing and printing in parallel -/

theorem mapM_eq_par {α β : Type} (f : α → Except String β) (l : List α) :
    l.mapM f = (parMap f l).mapM id := by
  rw [parMap_eq]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, List.map_cons, ih, id]

/-- `parseUnit` with the dumps read and decoded in parallel tasks. -/
def parseUnitF (u : Cgu) : Except String PCgu :=
  match (parMap readFile u.funcs).mapM id with
  | .error e => .error e
  | .ok ds =>
  match unitTable ds with
  | .error e => .error s!"unit {u.tag}: {e}"
  | .ok ρ =>
  match (parMap (decodeFile ρ) (u.funcs.zip ds)).mapM id with
  | .error e => .error e
  | .ok fs =>
    let ps := dataParsed u.data
    let ds' := okData ps
    let s := reachSet ds' (rootsOf fs)
    if !closedB ds' (rootsOf fs) s then .error s!"unit {u.tag}: data closure not closed" else
    match badLine s ps with
    | some (n, e) => .error s!"unit {u.tag}: data object %{n}: {e}"
    | none =>
      let data := ds'.filter (s.contains ·.name)
      if (data.flatMap (·.names)).all (fun n => lookupRen ρ n == n) then
        .ok { tag := u.tag, funcs := fs, raw := ds.map Dump.raw, ren := lookupRen ρ, data,
              locals := u.locals, names := u.names }
      else .error s!"unit {u.tag}: a data object is named like a declared external name"

@[csimp] theorem parseUnit_eq_F : @parseUnit = @parseUnitF := by
  funext u
  simp only [parseUnit, parseUnitF, ← mapM_eq_par]
  all_goals rfl

/-! ## The assembled program part -/

/-- `renamedOf` under the naming `sc` (`renamedOf us = renamedOfW (finOf us) us`). -/
def renamedOfW (sc : Nat → String → String) (us : List PCgu) :
    List (List String × Clif.Function × String) :=
  us.zipIdx.flatMap fun (u, i) => u.funcs.map fun f => (f.2.1, f.1.rename (sc i), f.2.2)

/-- `assembled` from the program's functions `Pf` and data `D` (`assembled us fis =
assembledW us (link us (finOf us)).funcs (linkData us (finOf us)) fis`). -/
def assembledW (us : List PCgu) (Pf : List Clif.Function) (D : List DataObject)
    (fis : List FnInput) : Assembled :=
  let names := Pf.map (·.name)
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  { units := us, funcs := fis, names, data := D
    refs := sortDedup ((Pf.flatMap (·.names) ++ D.flatMap (·.names)).filter
      (!nameSet.contains ·))
    symNames := dedupFirst (Pf.flatMap addrNamesOf ++ dataFnsOf names D) }

/-- `assemble`: the linked names through the units' tables, every function renamed once (its
`FnInput` and the program's function), the inputs printed and checked in parallel tasks. -/
def assembleF (b : Bundle) : Except String Assembled :=
  match b.skipped with
  | (n, why) :: _ =>
    .error s!"link-proof skipped {b.skipped.length} function(s) of the region: {n}: {why}"
  | [] =>
    match b.units.mapM parseUnit with
    | .error e => .error e
    | .ok us =>
      if !scopingB us then .error "the linked names are not a scoping of the units" else
      let sc := finOfT (us.map PCgu.finTab).toArray
      let rn := renamedOfW sc us
      match (parMap (fun x => mkInput x.1 x.2.1 x.2.2) rn).mapM id with
      | .error e => .error e
      | .ok fis => .ok (assembledW us (rn.map (·.2.1)) (linkData us sc) fis)

@[csimp] theorem assemble_eq_F : @assemble = @assembleF := by
  funext b
  have hr : ∀ us, renamedOfW (finOf us) us = renamedOf us := fun _ => rfl
  have ha : ∀ us fis, assembledW us ((renamedOf us).map (·.2.1)) (linkData us (finOf us)) fis =
      assembled us fis := by
    intro us fis
    rw [renamedOf_funcs]
    rfl
  simp only [assemble, assembleF, finOfT_eq, hr, ← mapM_eq_par, ha]
  all_goals rfl

/-- `buildSpec`, compiled here (with `assembleF`). -/
def buildSpecF (b : Bundle) : Except String LinkSpec :=
  match assemble b with
  | .error e => .error e
  | .ok A =>
    match sizesFor b.sizes A.names with
    | .error e => .error e
    | .ok sizes =>
      match A.names.head?.bind (fun n => b.markers.lookup n) with
      | none => .error "no function, or the first has no Lean code address"
      | some R =>
        let t := symTable b
        let al := firstMap b.aligns
        .ok { funcs := A.funcs, names := A.names, sizes,
              outside := A.refs.filterMap fun n => (addrOf t n).map (n, ·),
              data := A.data, symNames := A.symNames, R,
              aligns := A.names.map fun n => al.getD n 4 }

@[csimp] theorem buildSpec_eq_F : @buildSpec = @buildSpecF := rfl

end Front

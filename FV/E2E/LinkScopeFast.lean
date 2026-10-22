import FV.E2E.LinkScopeInputDefs

/-! # The program-level input conditions, evaluated with hash maps (T3d)

`progScopeB`/`progScopeInB` (`FV/E2E/LinkScopeDefs.lean`, `LinkScopeInputDefs.lean`) look up a
name in the program (`Clif.Program.func?`, a scan of its functions) at every declaration and call
site, and in the CLIF image's symbols `S` (`List.lookup` in `Link.inScopePar`) for every pair of a
function with indirect calls and a function of the program (`indB`, `indSiteB`): quadratic, an hour
of `lean-link` on a 28k-function program (std through `cargo fv --build-std`).

`progScopeWithB F`, `progScopeInWithB F` are those conditions with the program's functions looked
up through `F` (`= progScopeB` at `F = P.func?`, by definition); `funcMap P` (a hash map built
once) answers `P.func?` (`funcMap_get`) and `assocMap l` answers `l.lookup` (`assocMap_get`), so
the hash-map versions `progScopeFastB`, `progScopeInFastB` are equal to the conditions
(`progScopeFastB_eq`, `progScopeInFastB_eq`); `Link.inScopePar`, `Link.inScopeInPar` evaluate
them. They also compute a function's own facts (`indFreeB g`, `declB g`, `indSigs g`) once per
function instead of once per (function, function) pair (`indFastB`, `indToFastB`). No statement
changes.
-/

namespace E2E.LinkCheck

open Backend

/-- `l` as a hash map; the first entry of a key wins (`List.lookup`'s answer: `assocMap_get`). -/
def assocMap {α : Type} (l : List (String × α)) : Std.HashMap String α :=
  l.foldr (fun p m => m.insert p.1 p.2) {}

theorem assocMap_get {α : Type} (l : List (String × α)) (n : String) :
    (assocMap l)[n]? = l.lookup n := by
  induction l with
  | nil => simp [assocMap]
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [assocMap, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getElem?_insert, ih, List.lookup_cons]
    by_cases h : k = n
    · subst h; simp
    · have h' : (n == k) = false := by simpa using Ne.symm h
      simp [h, h']

/-- The functions of `P` by name, as a hash map; the first function of a name wins
(`Clif.Program.func?`'s answer: `funcMap_get`). -/
def funcMap (P : Clif.Program) : Std.HashMap String Clif.Function :=
  P.funcs.foldr (fun f m => m.insert f.name f) {}

theorem foldr_insert_name_get (fs : List Clif.Function) (n : String) :
    (fs.foldr (fun f m => m.insert f.name f) ({} : Std.HashMap String Clif.Function))[n]? =
      fs.find? (·.name == n) := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, ih, List.find?_cons]
    by_cases h : f.name = n
    · simp [h]
    · have h' : (f.name == n) = false := by simpa using h
      simp [h, h']

theorem funcMap_get (P : Clif.Program) (n : String) : (funcMap P)[n]? = P.func? n :=
  foldr_insert_name_get P.funcs n

theorem foldl_insert_name_contains (l : List (Clif.FnRef × Clif.ExtFunc)) (s : Std.HashSet String)
    (n : String) :
    (l.foldl (fun s e => s.insert e.2.name) s).contains n = (s.contains n || l.any (·.2.name == n)) := by
  induction l generalizing s with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, List.any_cons]
    cases s.contains n <;> cases (e.2.name == n) <;> simp

/-- The names `g` declares, as a hash set (`declB g`: `declSet_contains`). -/
def declSet (g : Clif.Function) : Std.HashSet String :=
  g.externs.foldl (fun s e => s.insert e.2.name) {}

theorem declSet_contains (g : Clif.Function) : (fun n => (declSet g).contains n) = declB g := by
  funext n
  simp [declSet, foldl_insert_name_contains, declB]

/-! ### `g`'s facts computed once

`mayB S g`, `indSigB g`, `indRetsB g`, `indToB S g` and `indB P S g` evaluate `indFreeB g`,
`declB g` (a scan of `g`'s externs) and `indSigs g` (a scan of `g`'s body) again for every
function `h` of the program. The `…WithB` forms take them as arguments (`ind`, `D`, `sigs`) and
are those definitions at `indFreeB g`, `declB g`, `indSigs g` (`rfl`); the `…FastB` forms compute
them once, `D` as a hash set. -/

/-- `mayB S g` with `indFreeB g`, `declB g` given. -/
def mayWithB (S : String → Option Nat) (ind : Bool) (D : String → Bool) (n : String) : Bool :=
  D n || (!ind && (S n).isSome)

/-- `indSigB g` with `declB g`, `indSigs g` given. -/
def indSigWithB (D : String → Bool) (sigs : List Clif.Signature) (h : Clif.Function) : Bool :=
  sigs.any (fun s => decide (LinkSys.IndSigMatch s h)) ||
    (D h.name && sigs.any (fun s => decide (LinkSys.IndTyMatch s h)))

/-- `indRetsB g` with `indSigs g` given. -/
def indRetsWithB (sigs : List Clif.Signature) (h : Clif.Function) : Bool :=
  sigs.all fun s => !decide (LinkSys.IndTyMatch s h) ||
    h.sig.returns.length != s.returns.length || (sigRets h.sig).length == (sigRets s).length

/-- `indMatchB g` with `indSigs g` given. -/
def indMatchWithB (sigs : List Clif.Signature) (h : Clif.Function) : Bool :=
  sigs.any fun s => decide (LinkSys.IndSigMatch s h) && h.sig.returns.length == s.returns.length

/-- `indToB S g` with `indFreeB g`, `declB g`, `indSigs g` given. -/
def indToWithB (S : String → Option Nat) (ind : Bool) (D : String → Bool)
    (sigs : List Clif.Signature) (g h : Clif.Function) : Bool :=
  mayWithB S ind D h.name && ((D h.name && gotDeclB g h.name) || indMatchWithB sigs h)

/-- `indB P S g` with `indFreeB g`, `declB g`, `indSigs g` given. -/
def indWithB (P : Clif.Program) (S : String → Option Nat) (ind : Bool) (D : String → Bool)
    (sigs : List Clif.Signature) : Bool :=
  ind || P.funcs.all (fun h => !mayWithB S ind D h.name || !indSigWithB D sigs h ||
      ((match sigParamBytes h.sig with | .ok b => decide (b.length ≤ 8) | .error _ => false) &&
        indRetsWithB sigs h))

theorem indToWithB_eq (S : String → Option Nat) (g : Clif.Function) :
    indToWithB S (indFreeB g) (declB g) (indSigs g) g = indToB S g := rfl

theorem indWithB_eq (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) :
    indWithB P S (indFreeB g) (declB g) (indSigs g) = indB P S g := rfl

/-- **`indToB S g` with `g`'s facts computed once** (`indToFastB_eq`). -/
def indToFastB (S : String → Option Nat) (g : Clif.Function) : Clif.Function → Bool :=
  let D := declSet g
  indToWithB S (indFreeB g) (fun n => D.contains n) (indSigs g) g

theorem indToFastB_eq (S : String → Option Nat) (g : Clif.Function) :
    indToFastB S g = indToB S g := by
  simp only [indToFastB, declSet_contains, indToWithB_eq]

/-- **`indB P S g` with `g`'s facts computed once** (`indFastB_eq`). -/
def indFastB (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : Bool :=
  let D := declSet g
  indWithB P S (indFreeB g) (fun n => D.contains n) (indSigs g)

theorem indFastB_eq (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) :
    indFastB P S g = indB P S g := by
  simp only [indFastB, declSet_contains, indWithB_eq]

/-- `indSiteB P S g` with the test `indToB S g` given (`indSiteB = indSiteWithB P (indToB S g)`). -/
def indSiteWithB (P : Clif.Program) (to : Clif.Function → Bool) (s : Clif.Signature)
    (args : List Nat) : Bool :=
  P.funcs.all fun h => !to h ||
    decide ((regLocs h.sig).length ≠ (callRegs s args).length) ||
    decide (regLocs h.sig = callRegs s args)

/-- `declSigB` with the program's functions looked up through `F`. -/
def declSigWithB (F : String → Option Clif.Function) (g : Clif.Function) : Bool :=
  g.externs.all fun e => match F e.2.name with
    | some h => decide (e.2.sig = h.sig)
    | none => true

/-- `dirSiteB` with the program's functions looked up through `F`. -/
def dirSiteWithB (F : String → Option Clif.Function) (e : Clif.ExtFunc) (args : List Nat) : Bool :=
  match F e.name with
  | some h => decide (callRegs e.sig args = regLocs h.sig)
  | none => true

/-- `callScopeB` with the program's functions looked up through `F` at the direct calls and the
test `to` (`indToB S g`) at the indirect ones. -/
def callScopeWithB (F : String → Option Clif.Function) (P : Clif.Program)
    (to : Clif.Function → Bool) (g : Clif.Function) : Bool :=
  g.blocks.all fun B =>
    B.body.all (fun st => match st.inst with
      | .call fn args => match g.extern? fn with
        | some e => dirSiteWithB F e args
        | none => true
      | .callIndirect sg _ args => match g.sigDecls.lookup sg with
        | some s => indSiteWithB P to s args
        | none => true
      | _ => true) &&
    match B.term with
    | .tryCall fn args _ => match g.extern? fn with
      | some e => dirSiteWithB F e args
      | none => true
    | .tryCallIndirect _ args et => match g.sigDecls.lookup et.sig with
      | some s => indSiteWithB P to s args
      | none => true
    | _ => true

/-- `outScopeB` with the program's functions looked up through `F`. -/
def outScopeWithB (F : String → Option Clif.Function) (g : Clif.Function) : Bool :=
  g.externs.all fun e => !(F e.2.name).isSome || outFitsB e.2.sig (callStack g)

theorem callScopeWithB_eq (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) :
    callScopeWithB P.func? P (indToB S g) g = callScopeB P S g := rfl

/-- The per-function part of `progScopeB` with the program's functions looked up through `F` and
`g`'s facts computed once (`indFastB`, `indToFastB`). -/
def progFnWithB (F : String → Option Clif.Function) (P : Clif.Program) (S : String → Option Nat)
    (g : Clif.Function) : Bool :=
  let to := indToFastB S g
  declSigWithB F g && indFastB P S g && callScopeWithB F P to g && outScopeWithB F g

theorem progFnWithB_func? (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) :
    progFnWithB P.func? P S g =
      (declSigB P g && indB P S g && callScopeB P S g && outScopeB P g) := by
  simp only [progFnWithB, indFastB_eq, indToFastB_eq, callScopeWithB_eq]
  rfl

/-- `progScopeB` with the program's functions looked up through `F`. -/
def progScopeWithB (F : String → Option Clif.Function) (P : Clif.Program)
    (S : String → Option Nat) : Bool :=
  decide (P.funcs.map (·.name)).Nodup && P.funcs.all (progFnWithB F P S) && addrSlotsInB P S

/-- `progScopeInB` with the program's functions looked up through `F`. -/
def progScopeInWithB (F : String → Option Clif.Function) (P : Clif.Program)
    (S : String → Option Nat) : Bool :=
  decide (P.funcs.map (·.name)).Nodup && P.funcs.all (progFnWithB F P S) && addrSlotsInputB P S

theorem progScopeWithB_func? (P : Clif.Program) (S : String → Option Nat) :
    progScopeWithB P.func? P S = progScopeB P S := by
  rw [progScopeWithB, funext (progFnWithB_func? P S)]
  rfl

theorem progScopeInWithB_func? (P : Clif.Program) (S : String → Option Nat) :
    progScopeInWithB P.func? P S = progScopeInB P S := by
  rw [progScopeInWithB, funext (progFnWithB_func? P S)]
  rfl

/-- **`progScopeB` with the program's functions in a hash map** (`progScopeFastB_eq`). -/
def progScopeFastB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  let m := funcMap P
  progScopeWithB (fun n => m[n]?) P S

/-- **`progScopeInB` with the program's functions in a hash map** (`progScopeInFastB_eq`). -/
def progScopeInFastB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  let m := funcMap P
  progScopeInWithB (fun n => m[n]?) P S

theorem funcMap_fun (P : Clif.Program) : (fun n => (funcMap P)[n]?) = P.func? :=
  funext (funcMap_get P)

theorem progScopeFastB_eq (P : Clif.Program) (S : String → Option Nat) :
    progScopeFastB P S = progScopeB P S := by
  simp only [progScopeFastB, funcMap_fun, progScopeWithB_func?]

theorem progScopeInFastB_eq (P : Clif.Program) (S : String → Option Nat) :
    progScopeInFastB P S = progScopeInB P S := by
  simp only [progScopeInFastB, funcMap_fun, progScopeInWithB_func?]

/-- The CLIF image's symbols of `l` looked up in a hash map: `l.lookup` (`assocMap_get`). -/
theorem assocMap_fun {α : Type} (l : List (String × α)) :
    (fun n => (assocMap l)[n]?) = (fun n => l.lookup n) :=
  funext (assocMap_get l)

end E2E.LinkCheck

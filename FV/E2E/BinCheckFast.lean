import FV.E2E.CodeMap
import FV.E2E.StackBound
import FV.E2E.LinkCheckFast

/-! # The code map and the stack budgets with hash maps (T3d)

`codeMapB` (`FV/E2E/CodeMap.lean`) looks every function's address up in the link map
(`List.lookup`) and compares every pair of functions of the table; `budMap`
(`FV/E2E/StackBound.lean`) builds the call graph by testing every pair of functions with `g`'s
externs scanned and the CLIF image's symbols looked up (`List.lookup`) per pair, and finds each
function's image by a scan of the results (`artOf`). On a 28k-function program (std through
`cargo fv --build-std`) that is hours of `link-check`.

`codeMapFastB` (`codeMapFastB_eq`) and `budMapFast` (`budMapFast_eq`) are the same functions with
the lookups in hash maps and each function's facts computed once. `link-check` evaluates these.
No statement changes.
-/

namespace E2E

open Backend LinkCheck

namespace LinkCheck

/-- `noBlrB I T` with the CLIF image's symbols looked up through `S`. -/
def noBlrWithB (S : String → Option Nat) (T : List (Clif.Function × Art)) (n : String) : Bool :=
  (S n).isNone && T.all fun e => !(e.1.externs.any fun x => x.2.name == n) || blrGotB e.2.vcp n

/-- `codeMapB`'s test of the pair (`x`, `y`) of functions of the table, the range test first. -/
def RaEnt.codeOk (pt : Clif.Program) (x y : RaEnt) : Bool :=
  decide (x.hi ≤ y.lo ∨ y.hi ≤ x.lo) || x.name == y.name ||
    (x.art.base == y.art.base && linesAlikeB pt x.art.fa.lines.toList y.art.fa.lines.toList)

theorem or_swap12 (a b c : Bool) : (a || b || c) = (b || a || c) := by
  cases a <;> cases b <;> rfl

/-- **`codeMapB` with the link map and the symbols in hash maps** (`A`, `S`) and the code ranges
computed once (`codeMapFastB_eq`). -/
def codeMapFastB (A S : String → Option Nat) (T : List (Clif.Function × Art)) : Bool :=
  let E := T.map RaEnt.of
  let pt := progT T
  T.all fun e =>
    (BitVec.ofNat 64 ((A e.1.name).getD 0) + BitVec.ofInt 64 0 == e.2.base ||
      noBlrWithB S T e.1.name) &&
    let x := RaEnt.of e
    E.all fun y => x.codeOk pt y

theorem codeMapFastB_eq (I : LinkInput) (T : List (Clif.Function × Art)) :
    codeMapFastB (fun n => (assocMap I.addrs)[n]?) (fun n => (assocMap I.syms)[n]?) T =
      codeMapB I T := by
  simp only [codeMapFastB, codeMapB, assocMap_fun, List.all_map, Function.comp_def]
  congr 1
  funext e
  congr 1
  congr 1
  funext e'
  exact or_swap12 _ _ _

/-- The compiled image of each function of the results by name, the first one of a name
(`artOf`: `artMap_artOf`). -/
def artMap (R : Res) : Std.HashMap String Art := assocMap (R.map fun e => (e.1.name, getOk e.2))

theorem artMap_artOf (R : Res) (g : Clif.Function) :
    ((artMap R)[g.name]?).getD default = artOf R g := by
  rw [artMap, assocMap_get, artOf]
  induction R with
  | nil => rfl
  | cons e R ih =>
    simp only [List.map_cons, List.lookup_cons, List.find?_cons]
    by_cases h : e.1.name = g.name
    · have h1 : (g.name == e.1.name) = true := by simp [h]
      have h2 : (e.1.name == g.name) = true := by simp [h]
      simp [h1, h2]
    · have h1 : (g.name == e.1.name) = false := by simpa using Ne.symm h
      have h2 : (e.1.name == g.name) = false := by simpa using h
      simp only [h1, h2]
      exact ih

end LinkCheck

namespace StackBound

/-- `edgeW S g` with `declB g` given (`D`). -/
def edgeWithW (S : String → Option Nat) (D : String → Bool) (ind : Bool)
    (sigs : List Clif.Signature) (h : Clif.Function) : Bool :=
  D h.name || (ind && (S h.name).isSome && sigs.any fun s => decide (LinkSys.IndSigMatch s h))

/-- `budSucc` with the symbols looked up through `S` and `declB g` a hash set. -/
def budSuccFast (S : String → Option Nat) (fs : Array Clif.Function) : Array (List Nat) :=
  fs.map fun g =>
    let D := declSet g
    let ind := !indFreeB g
    let sigs := indSigs g
    (List.range fs.size).filter fun j => edgeWithW S (fun n => D.contains n) ind sigs fs[j]!

theorem budSuccFast_eq (I : LinkInput) (fs : Array Clif.Function) :
    budSuccFast (fun n => (assocMap I.syms)[n]?) fs = budSucc I fs := by
  simp only [budSuccFast, assocMap_fun, declSet_contains]
  rfl

/-- `budFd` with the images in a hash map. -/
def budFdFast (M : Std.HashMap String Art) (fs : Array Clif.Function) : Array Nat :=
  fs.map fun g => frameDrop ((M[g.name]?).getD default).af

theorem budFdFast_eq (R : Res) (fs : Array Clif.Function) :
    budFdFast (artMap R) fs = budFd R fs := by
  simp only [budFdFast, budFd, artMap_artOf]

/-- **`budMap` with hash maps** (`budMapFast_eq`). -/
def budMapFast (I : LinkInput) (R : Res) : Std.HashMap String Nat :=
  let fs := (progOf R).funcs.toArray
  let b := budIter (budFdFast (artMap R) fs) (budSuccFast (fun n => (assocMap I.syms)[n]?) fs)
    (fs.size + 1) (fs.map fun _ => none)
  (List.range fs.size).foldl (fun m j => match b[j]! with
    | some v => m.insert fs[j]!.name v
    | none => m) {}

theorem budMapFast_eq (I : LinkInput) (R : Res) : budMapFast I R = budMap I R := by
  simp only [budMapFast, budFdFast_eq, budSuccFast_eq]
  rfl

end StackBound

end E2E

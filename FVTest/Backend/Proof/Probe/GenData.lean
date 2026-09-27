import FV.Backend
open Backend Isle Isle.Aarch64

/-! Generates `FV/Backend/Proof/IselData.lean` (run: `lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean`):
terms the probe's rules reach, each by `native_decide` on a single small equality. -/

partial def patTerms : Pattern → List Nat
  | .term _ t args => t :: args.flatMap patTerms
  | .bind _ _ p => patTerms p
  | .and _ ps => ps.flatMap patTerms
  | _ => []

partial def exprTerms : Expr → List Nat
  | .term _ t args => t :: args.flatMap exprTerms
  | .let _ bs body => bs.flatMap (fun (_, _, e) => exprTerms e) ++ exprTerms body
  | _ => []

def ruleTerms (r : Rule) : List Nat :=
  r.args.flatMap patTerms ++ r.iflets.flatMap (fun il => patTerms il.lhs ++ exprTerms il.rhs) ++
    exprTerms r.rhs

partial def closeTerms (seen : List Nat) (rules : List String) : List Nat → List Nat × List String
  | [] => (seen, rules)
  | t :: ts =>
    if seen.contains t then closeTerms seen rules ts else
    match program.term? t with
    | some tm =>
      if tm.hasInternalCtor && t != 686 then
        let rs := program.rulesOf t
        closeTerms (t :: seen) (rules ++ rs.map (·.name)) (ts ++ rs.flatMap ruleTerms)
      else closeTerms (t :: seen) rules ts
    | none => closeTerms seen rules ts

partial def patNodes : Pattern → List (Nat × Nat) × List Nat × List (Nat × Int)
  | .term ty t args => let r := args.map patNodes
      (((ty, t) :: r.flatMap (·.1)), r.flatMap (·.2.1), r.flatMap (·.2.2))
  | .bind _ _ p => patNodes p
  | .and _ ps => let r := ps.map patNodes; (r.flatMap (·.1), r.flatMap (·.2.1), r.flatMap (·.2.2))
  | .constPrim ty _ => ([], [ty], [])
  | .constInt ty i => ([], [], [(ty, i)])
  | _ => ([], [], [])

partial def exprNodes : Expr → List (Nat × Nat) × List Nat × List (Nat × Int)
  | .term ty t args => let r := args.map exprNodes
      (((ty, t) :: r.flatMap (·.1)), r.flatMap (·.2.1), r.flatMap (·.2.2))
  | .let _ bs body =>
    let es : List Expr := bs.map (fun (b : VarId × TypeId × Expr) => b.2.2) ++ [body]
    let r := es.map exprNodes
    (r.flatMap (·.1), r.flatMap (·.2.1), r.flatMap (·.2.2))
  | .constPrim ty _ => ([], [ty], [])
  | .constInt ty i => ([], [], [(ty, i)])
  | _ => ([], [], [])

def ruleNodes (r : Rule) : List (Nat × Nat) × List Nat × List (Nat × Int) :=
  let l : List (List (Nat × Nat) × List Nat × List (Nat × Int)) :=
    r.args.map patNodes ++ r.iflets.flatMap (fun il => [patNodes il.lhs, exprNodes il.rhs]) ++
    [exprNodes r.rhs]
  (l.flatMap (·.1), l.flatMap (·.2.1), l.flatMap (·.2.2))

def q (s : String) : String := s.quote

def bstr (b : Bool) : String := if b then "true" else "false"

def kindStr : TermKind → String
  | .enumVariant k => s!"(.enumVariant {k})"
  | .struct => ".struct"
  | .decl f c e =>
    let c := match c with
      | none => "none" | some .internal => "(some .internal)"
      | some (.external n) => s!"(some (.external {q n}))"
    let e := match e with
      | none => "none" | some (.internal _) => "(some (.internal default))"
      | some (.external n inf) => s!"(some (.external {q n} {bstr inf}))"
    s!"(.decl ⟨{bstr f.isPure}, {bstr f.isMulti}, {bstr f.isPartial}, {bstr f.isRec}⟩ {c} {e})"

def termStr (tm : Term) : String :=
  s!"⟨{tm.id}, {q tm.name}, {tm.args}, {tm.ret}, {kindStr tm.kind}, ⟨{q tm.pos.file}, {tm.pos.line}⟩⟩"

def header (roots : List String) (extra : List Nat) : String := s!"import FV.Backend
import FV.Backend.Proof.IselAttr

/-!
# ISLE data facts for the isel proofs (generated, do not edit)

Regenerate: `lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean > FV/Backend/Proof/IselData.lean`.

For every term reachable from the root rules {roots} (patterns, if-lets, right-hand sides,
and the rules of every internal constructor they call, transitively) plus terms {extra}:
`program.term? t = some term_t` and, for internal constructors, `program.rulesOf t = [...]`,
each by `native_decide` on one small equality; `term_t.kind` / `term_t.name` by `rfl`.

`Isle.Aarch64.program` is never reduced by the kernel (it is built by `Program.build`, a fold
over all 1165 rules and a sort per term; kernel reduction of it exhausted memory before).
-/

namespace Backend.Proof

open Isle Isle.Aarch64
"

def roots : List String := ["rule_lower_86", "rule_lower_90", "rule_lower_2215", "rule_lower_1638"]
def extra : List Nat := []

def main : IO Unit := do
  let rs := roots.filterMap program.ruleByName?
  let (terms, rules) := closeTerms [] [] (rs.flatMap ruleTerms ++ extra)
  let terms := terms.mergeSort (· ≤ ·)
  IO.println (header roots extra)
  IO.println s!"-- terms: {terms.length}, internal-constructor rules: {rules.length}\n"
  for t in terms do
    let some tm := program.term? t | continue
    if let some (.internal _) := (match tm.kind with | .decl _ _ e => e | _ => none) then
      IO.println s!"-- WARNING internal extractor {tm.name}"
    IO.println s!"/-- `{tm.name}` -/\ndef term_{t} : Isle.Term :=\n  {termStr tm}\ntheorem program_term_{t} : program.term? {t} = some term_{t} := by native_decide\n@[isel_data] theorem termOf_{t} : Interp.termOf program {t} = pure term_{t} := by\n  rw [Interp.termOf, program_term_{t}]\n@[isel_data] theorem term_{t}_kind : term_{t}.kind = {kindStr tm.kind} := rfl\n@[isel_data] theorem term_{t}_name : term_{t}.name = {q tm.name} := rfl\n"
    if tm.hasInternalCtor && t != 686 then
      let names := (program.rulesOf t).map (·.name)
      IO.println s!"@[isel_data] theorem program_rulesOf_{t} : program.rulesOf {t} = [{", ".intercalate names}] := by native_decide\n"

  -- enum variants, `$Type` constants, integer literals of all rules involved
  let allRules := rs ++ rules.filterMap program.ruleByName?
  let (vs, prims, ints) := (allRules.map ruleNodes).foldl
    (fun (a, b, c) (x, y, z) => (a ++ x, b ++ y, c ++ z)) ([], [], [])
  let dedup {α} [BEq α] (l : List α) : List α := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  IO.println "/-! ### Enum variant names, `$Type` constants, integer literals -/\n"
  for (ty, t) in dedup vs do
    let some tm := program.term? t | continue
    if let .enumVariant k := tm.kind then
      if let some n := (variantNames ty)[k]? then
        IO.println s!"@[isel_data] theorem variantNames_{ty}_{k} : (variantNames {ty})[{k}]? = some {q n} := by native_decide"
  for ty in dedup prims do
    IO.println s!"@[isel_data] theorem typeName_{ty} : program.typeName {ty} = {q (program.typeName ty)} := by native_decide"
  for (ty, i) in dedup ints do
    let nm := if i < 0 then s!"neg{-i}" else s!"{i}"
    IO.println s!"@[isel_data] theorem normInt_{ty}_{nm} : normInt {ty} ({i}) = {normInt ty i} := by native_decide"
  IO.println ""
  for (n, v) in [("tyMInst", tyMInst), ("tyALUOp", tyALUOp), ("tyALUOp3", tyALUOp3),
      ("tyOperandSize", tyOperandSize), ("tyCond", tyCond), ("tyExtendOp", tyExtendOp),
      ("tyAMode", tyAMode), ("tyCondBrKind", tyCondBrKind), ("tyMoveWideOp", tyMoveWideOp),
      ("tyBfmOp", tyBfmOp), ("tyBitOp", tyBitOp), ("tyScalarSize", tyScalarSize),
      ("tyIntCC", tyIntCC), ("tyOpcode", tyOpcode), ("tyInstData", tyInstData)] do
    IO.println s!"@[isel_data] theorem {n}_eq : {n} = {v} := by native_decide"
  IO.println ""
  IO.println "end Backend.Proof"

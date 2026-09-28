import FV.Isle.Opt.Simplify
import FV.Isle.Generated.Opt.Closure
import Std.Data.HashSet
open Isle Isle.Opt

/-! Generates `FV/Opt/Proof/RuleData.lean`
(run: `lake env lean --run FVTest/Opt/Proof/GenData.lean > FV/Opt/Proof/RuleData.lean`).

For the terms the closure root rules of `simplify`/`simplify_skeleton` reach (patterns,
if-lets, right-hand sides, and the rules of every internal constructor they call,
transitively; not the rules of the roots themselves), the `Data p` structure of facts
`termOf p t = .ok T.x` and `p.rulesOf t = [...]`, their `rfl` proofs for `program`, and `rfl`
lemmas for the term kinds. -/

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

def rootTerms : List Nat := [T.«simplify».id, T.«simplify_skeleton».id]

partial def closeTerms (seen : Std.HashSet Nat) (acc : Array Nat) : List Nat → Array Nat
  | [] => acc
  | t :: ts =>
    if seen.contains t then closeTerms seen acc ts else
    match program.term? t with
    | some tm =>
      let more := if tm.hasInternalCtor && !rootTerms.contains t then
        (program.rulesOf t).flatMap ruleTerms else []
      closeTerms (seen.insert t) (acc.push t) (ts ++ more)
    | none => closeTerms seen acc ts

partial def patInts : Pattern → List (Nat × Int)
  | .term _ _ args => args.flatMap patInts
  | .bind _ _ p => patInts p
  | .and _ ps => ps.flatMap patInts
  | .constInt ty i => [(ty, i)]
  | _ => []

partial def exprInts : Expr → List (Nat × Int)
  | .term _ _ args => args.flatMap exprInts
  | .let _ bs body => bs.flatMap (fun (_, _, e) => exprInts e) ++ exprInts body
  | .constInt ty i => [(ty, i)]
  | _ => []

def ruleInts (r : Rule) : List (Nat × Int) :=
  r.args.flatMap patInts ++ r.iflets.flatMap (fun il => patInts il.lhs ++ exprInts il.rhs) ++
    exprInts r.rhs

def q (s : String) : String := s.quote
def bstr (b : Bool) : String := if b then "true" else "false"
def tconst (tm : Term) : String := s!"T.«{tm.name}»"

def kindStr : TermKind → String
  | .enumVariant k => s!"(.enumVariant {k})"
  | .struct => ".struct"
  | .decl f c e =>
    let c := match c with
      | none => "none" | some .internal => "(some .internal)"
      | some (.external n) => s!"(some (.external {q n}))"
    let e := match e with
      | none => "none" | some (.internal _) => "(some (.internal _))"
      | some (.external n inf) => s!"(some (.external {q n} {bstr inf}))"
    s!"(.decl ⟨{bstr f.isPure}, {bstr f.isMulti}, {bstr f.isPartial}, {bstr f.isRec}⟩ {c} {e})"

def rootRules : List Rule :=
  Isle.Opt.Closure.rules.toList.filterMap fun c =>
    if c.isRoot then program.rule? c.rule else none

def main : IO Unit := do
  let roots := rootRules
  let terms := closeTerms {} #[] (roots.flatMap ruleTerms)
  let terms := terms.qsort (· < ·)
  let internal := terms.filter fun t =>
    (program.term? t).any (·.hasInternalCtor) && !rootTerms.contains t
  let nrules := (internal.toList.map fun t => (program.rulesOf t).length).sum
  IO.println s!"import FV.Isle.Opt.Simplify
import FV.Opt.Proof.RuleAttr

/-!
# ISLE data facts for the mid-end rule proofs (generated, do not edit)

Regenerate: `lake env lean --run FVTest/Opt/Proof/GenData.lean > FV/Opt/Proof/RuleData.lean`.

Roots: the {roots.length} closure root rules of `simplify`/`simplify_skeleton`
(`Isle.Opt.Closure`); {terms.size} terms reachable from them, of which the internal
constructors (other than the roots) have {nrules} rules.

`Data p` bundles `Interp.termOf p t = .ok T.x` and `p.rulesOf t = [...]`. Rule proofs are
stated for an abstract `p` with `Data p`, so the kernel never unfolds the program while
checking them; `data_program : Data program` proves every field by `rfl`.
-/

namespace Opt.Proof

open Isle Isle.Opt
"
  IO.println "/-! ### Term kinds (`rfl`) -/\n"
  let mut fields : Array String := #[]
  let mut facts : Array String := #[]
  let mut proofs : Array String := #[]
  for t in terms do
    let some tm := program.term? t | continue
    unless (match tm.kind with | .decl _ _ (some (.internal _)) => true | _ => false) do
      IO.println s!"@[opt_data] theorem term_{t}_kind : {tconst tm}.kind = {kindStr tm.kind} := rfl"
    fields := fields.push s!"  t{t} : Interp.termOf p {t} = .ok {tconst tm}"
    facts := facts.push s!"theorem program_term_{t} : Interp.termOf program {t} = .ok {tconst tm} := rfl"
    proofs := proofs.push s!"  t{t} := program_term_{t}"
    if tm.hasInternalCtor && !rootTerms.contains t then
      let names := ", ".intercalate ((program.rulesOf t).map (·.name))
      fields := fields.push s!"  r{t} : p.rulesOf {t} = [{names}]"
      facts := facts.push s!"theorem program_rulesOf_{t} : program.rulesOf {t} = [{names}] := rfl"
      proofs := proofs.push s!"  r{t} := program_rulesOf_{t}"
  IO.println "
/-- The facts about the exported program that the rule proofs use. -/
structure Data (p : Program) : Prop where"
  for f in fields do IO.println f
  IO.println "
/-! ### The fields as conditional simp lemmas (`simp [opt_data]` discharges `Data p` from the
context) -/
"
  for t in terms do
    let some tm := program.term? t | continue
    IO.println s!"@[opt_data] theorem Data.term_{t} \{p : Program} (hd : Data p) : Interp.termOf p {t} = .ok {tconst tm} := hd.t{t}"
    if tm.hasInternalCtor && !rootTerms.contains t then
      let names := ", ".intercalate ((program.rulesOf t).map (·.name))
      IO.println s!"@[opt_data] theorem Data.rules_{t} \{p : Program} (hd : Data p) : p.rulesOf {t} = [{names}] := hd.r{t}"
  IO.println "
/-! ### The facts for `program` (`rfl`) -/

set_option maxRecDepth 20000
"
  for f in facts do IO.println f
  IO.println "
theorem data_program : Data program where"
  for f in proofs do IO.println f
  IO.println "\n/-! ### Integer literals (`normInt`) -/\n"
  let allRules := roots ++ internal.toList.flatMap program.rulesOf
  let mut seenInts : Std.HashSet (Nat × Int) := {}
  for (ty, i) in allRules.flatMap ruleInts do
    if seenInts.contains (ty, i) then continue
    seenInts := seenInts.insert (ty, i)
    let nm := if i < 0 then s!"neg{-i}" else s!"{i}"
    IO.println s!"@[opt_data] theorem normInt_{ty}_{nm} : normInt {ty} ({i}) = {normInt ty i} := rfl"
  IO.println ""
  IO.println "end Opt.Proof"

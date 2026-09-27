import FV.Backend
open Backend Isle Isle.Aarch64

/-! Generates `FV/Backend/Proof/IselData.lean`
(run: `lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean > FV/Backend/Proof/IselData.lean`).

For the terms the root rules reach, the `Data p` structure of facts `termOf p t = pure T.x` and
`p.rulesOf t = [...]`, and `data_program : Data program` with every field by `rfl` (the
generated program is a structure literal over flat tables, `FV/Isle/Generated/*Table.lean`). -/

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

/-- Terms reachable from `ts` (following the rules of internal constructors other than the
root terms `lower`/`lower_branch`, whose rules are only followed for the chosen roots). -/
partial def closeTerms (seen : Std.HashSet Nat) (acc : Array Nat) : List Nat → Array Nat
  | [] => acc
  | t :: ts =>
    if seen.contains t then closeTerms seen acc ts else
    match program.term? t with
    | some tm =>
      let more := if tm.hasInternalCtor && t != TId.lower && t != TId.lower_branch then
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

/-- The generated Lean constant of term `tm` (`FV/Isle/Generated/Terms*.lean`). -/
def tconst (tm : Term) : String := s!"T.«{tm.name}»"

def kindStr : TermKind → String
  | .enumVariant k => s!"(.enumVariant {k})"
  | .struct => ".struct"
  | .decl f c e =>
    let c := match c with
      | none => "none" | some .internal => "(some .internal)"
      | some (.external n) => s!"(some (.external {q n}))"
    let e := match e with
      | none => "none" | some (.internal _) => "(some (.internal _))" -- not emitted (`main`)
      | some (.external n inf) => s!"(some (.external {q n} {bstr inf}))"
    s!"(.decl ⟨{bstr f.isPure}, {bstr f.isMulti}, {bstr f.isPartial}, {bstr f.isRec}⟩ {c} {e})"

/-- Root rules: `probe` (the probe's four rules) or `closure` (every closure root rule). -/
def rootRules (which : String) : List Rule :=
  if which == "probe" then
    ["rule_lower_86", "rule_lower_90", "rule_lower_2215", "rule_lower_1638"].filterMap
      program.ruleByName?
  else
    Closure.rules.toList.filterMap fun c => if c.isRoot then program.rule? c.rule else none

def header (which : String) (nroots nterms nrules : Nat) : String := s!"import FV.Backend
import FV.Backend.Proof.IselAttr

/-!
# ISLE data facts for the isel proofs (generated, do not edit)

Regenerate: `lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean {which} > FV/Backend/Proof/IselData.lean`.

Roots: {nroots} root rules ({which}); {nterms} terms reachable from them (patterns, if-lets,
right-hand sides, and the rules of every internal constructor they call, transitively), of
which the internal constructors have {nrules} rules. `lower`/`lower_branch` are included with
their full rule lists.

`Data p` bundles `Interp.termOf p t = pure T.x` and `p.rulesOf t = [...]` for these terms.
Rule proofs are stated for an abstract `p` with `Data p`, so the kernel never unfolds the
program while checking them; `data_program : Data program` proves every field by `rfl` (the
exported program is a structure literal over flat tables, `FV/Isle/Generated/*Table.lean`),
and `termByName? \"lower\"` by kernel `decide`.
-/

namespace Backend.Proof

open Isle Isle.Aarch64
"

def main (args : List String) : IO Unit := do
  let which := args.headD "probe"
  let roots := rootRules which
  let terms := closeTerms {} #[] (roots.flatMap ruleTerms ++ [TId.lower, TId.lower_branch])
  let terms := terms.qsort (· < ·)
  let internal := terms.filter fun t => (program.term? t).any (·.hasInternalCtor)
  let nrules := (internal.toList.map fun t => (program.rulesOf t).length).sum
  IO.println (header which roots.length terms.size nrules)
  IO.println "/-! ### Term fields (`rfl`) -/\n"
  let mut fields : Array String := #[]
  let mut proofs : Array String := #[]
  let mut facts : Array String := #[]
  for t in terms do
    let some tm := program.term? t | continue
    -- (internal extractors are macros, expanded away in the rules: no `kind` lemma needed)
    unless (match tm.kind with | .decl _ _ (some (.internal _)) => true | _ => false) do
      IO.println s!"@[isel_data] theorem term_{t}_kind : {tconst tm}.kind = {kindStr tm.kind} := rfl"
    IO.println s!"@[isel_data] theorem term_{t}_name : {tconst tm}.name = {q tm.name} := rfl"
    fields := fields.push s!"  t{t} : Interp.termOf p {t} = pure {tconst tm}"
    facts := facts.push s!"theorem program_term_{t} : Interp.termOf program {t} = pure {tconst tm} := rfl"
    proofs := proofs.push s!"  t{t} := program_term_{t}"
    if tm.hasInternalCtor then
      let names := ", ".intercalate ((program.rulesOf t).map (·.name))
      fields := fields.push s!"  r{t} : p.rulesOf {t} =\n    [{names}]"
      facts := facts.push s!"theorem program_rulesOf_{t} : program.rulesOf {t} =\n    [{names}] := rfl"
      proofs := proofs.push s!"  r{t} := program_rulesOf_{t}"
  fields := fields.push "  lower : p.termByName? \"lower\" = some T.lower"
  proofs := proofs.push "  lower := program_termByName_lower"
  IO.println "
/-- The facts about the exported program that the isel proofs use. Proofs are stated for an
arbitrary `p : Program` with `Data p`, never for `Isle.Aarch64.program` itself, so the kernel
cannot unfold the program data while checking them; `data_program` instantiates. -/
structure Data (p : Program) : Prop where"
  for f in fields do IO.println f
  IO.println "
/-! ### The facts for `program` (each `rfl`: indexing the flat tables, up to ~2500 deep in
`Meta.whnf`; one declaration each, so each has its own heartbeat budget) -/

set_option maxRecDepth 20000
"
  for f in facts do IO.println f
  IO.println "
theorem program_termByName_lower : program.termByName? \"lower\" = some T.lower := by
  decide +kernel

theorem data_program : Data program where"
  for f in proofs do IO.println f
  IO.println ""
  -- integer literals of all rules involved
  let allRules := roots ++ internal.toList.flatMap program.rulesOf
  let dedup {α} [BEq α] [Hashable α] (l : List α) : List α :=
    (l.foldl (fun (s, acc) x => if s.contains x then (s, acc) else (s.insert x, acc.push x))
      ((∅ : Std.HashSet α), #[])).2.toList
  IO.println "/-! ### Integer literals (`normInt`), type ids -/\n"
  for (ty, i) in dedup (allRules.flatMap ruleInts) do
    let nm := if i < 0 then s!"neg{-i}" else s!"{i}"
    IO.println s!"@[isel_data] theorem normInt_{ty}_{nm} : normInt {ty} ({i}) = {normInt ty i} := rfl"
  IO.println ""
  for (n, v) in [("tyMInst", tyMInst), ("tyALUOp", tyALUOp), ("tyALUOp3", tyALUOp3),
      ("tyOperandSize", tyOperandSize), ("tyCond", tyCond), ("tyExtendOp", tyExtendOp),
      ("tyAMode", tyAMode), ("tyCondBrKind", tyCondBrKind), ("tyMoveWideOp", tyMoveWideOp),
      ("tyBfmOp", tyBfmOp), ("tyBitOp", tyBitOp), ("tyScalarSize", tyScalarSize),
      ("tyIntCC", tyIntCC), ("tyOpcode", tyOpcode), ("tyInstData", tyInstData),
      ("tyImmExtend", tyImmExtend), ("tyRelocDistance", tyRelocDistance)] do
    IO.println s!"@[isel_data] theorem {n}_eq : {n} = {v} := rfl"
  IO.println ""
  IO.println "end Backend.Proof"

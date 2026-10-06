import FV.Backend.Proof.IselEmitFns

/-!
# Generator of the V6c emission summary table (`FV/Backend/Proof/IselEmitTab.lean`)

Untrusted: computes, by a fixpoint of V3's disjunctive abstract interpreter (`aRule`, `AW`) with
the emission transfer functions (`aextE`, `actorE`, precondition `apreE`, V3's oracle `aOracle`)
over the exported ISLE rules, a summary table for every internal term reachable from the closure
roots of `lower`, the terminator rules of `lower` and the rules of `lower_branch` (those ending in
a branch, `aRuleLast`, without their final `emit_side_effect`), and writes `IselEmitTab.lean`: the
table as Lean literals and the `native_decide` checks (`chkTab` and the root checks) the proofs
rely on. Prints the failing entries/roots/`emit`s if any.

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselEmitFns`):

    lake env lean --run FVTest/Backend/IselEmitGen.lean FV/Backend/Proof/IselEmitTab.lean
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.Cov

deriving instance Hashable for Backend.OperandSize
deriving instance Hashable for Backend.Proof.Cov.NK
deriving instance Hashable for Backend.Proof.Cov.AW

namespace Gen
open AW

def insAlt (b : AW) (as : List AW) (j : AW → AW → AW) : List AW :=
  match b with
  | .data t k fs =>
    if as.any (fun a => match a with | .data t' k' gs => t == t' && k == k' && fs.length == gs.length | _ => false)
    then as.map fun a => match a with
      | .data t' k' gs => if t == t' && k == k' && fs.length == gs.length then j a b else a
      | a => a
    else as ++ [b]
  | _ => as

partial def join : AW → AW → AW
  | .bot, b => b
  | a, .bot => a
  | .reg m, .reg n => .reg (m ||| n)
  | .ty a, .ty b => .ty (a ++ b.filter (!a.contains ·))
  | .num k b, .num k' b' => if k == k' then .num k (max b b') else .flat (if k == .callInfo || k' == .callInfo then 15 else 0) true
  | .data t k fs, .data t' k' gs =>
    if t == t' && k == k' && fs.length == gs.length then .data t k ((fs.zip gs).map fun (x, y) => join x y)
    else .alts [.data t k fs, .data t' k' gs]
  | .alts as, b@(.data ..) => .alts (insAlt b as join)
  | a@(.data ..), .alts bs => .alts (insAlt a bs join)
  | .alts as, .alts bs => .alts (bs.foldl (fun acc b => insAlt b acc join) as)
  | a, b => if a == b then a else
    let d := deep a; let e := deep b; .flat (d.1 ||| e.1) (d.2 && e.2)

abbrev Key := TermId × List AW

structure St where
  tab : Std.HashMap Key AW := {}
  old : Std.HashMap Key AW := {}
  changed : Bool := false
  bad : List (Nat × String) := []
  cur : Nat := 0

def demand (t : TermId) (as : List AW) : StateM St AW := do
  let s ← get
  match s.tab.get? (t, as) with
  | some out => pure out
  | none =>
    let o := (s.old.get? (t, as)).getD .bot
    set { s with tab := s.tab.insert (t, as) o, changed := true }
    pure o

variable (p : Program)

mutual
partial def iExpr : Isle.Expr → List AW → StateM St AW
  | .var _ x, env => pure (env.getD x .top)
  | .constBool _ b, _ => pure (.bool b)
  | .constInt _ n, _ => pure (aint n)
  | .constPrim tyv n, _ => pure (aprim tyv n)
  | .let _ bs body, env => do let env' ← iBinds bs env; iExpr body env'
  | .term tyv t args, env => do
    let as ← iArgs args env
    if as.any AW.isBot then pure .bot else
    match termOf p t with
    | .error _ => pure .top
    | .ok term =>
      match term.kind with
      | .enumVariant k => pure (.data tyv k as)
      | .struct => pure (.data tyv 0 as)
      | .decl _ (some (.external _)) _ =>
        if !apreE term.id as then
          modify fun s => { s with bad := (s.cur, s!"{term.name} {repr as}") :: s.bad }
        pure (actorE term.id as)
      | .decl _ (some .internal) _ =>
        match aOracle t as with
        | some a => pure a
        | none => demand t as
      | _ => pure .top
partial def iArgs : List Isle.Expr → List AW → StateM St (List AW)
  | [], _ => pure []
  | e :: es, env => do let a ← iExpr e env; let as ← iArgs es env; pure (a :: as)
partial def iBinds : List (VarId × TypeId × Isle.Expr) → List AW → StateM St (List AW)
  | [], env => pure env
  | (x, _, e) :: bs, env => do let a ← iExpr e env; iBinds bs (env.set x a)
end

partial def iIfLets : List IfLet → List AW → StateM St (List (List AW))
  | [], env => pure [env]
  | il :: ils, env => do
    let a ← iExpr p il.rhs env
    let mut out := []
    for e in aPat p aextE a il.lhs env do
      out := out ++ (← iIfLets ils e)
    pure out

def iRule (ins : List AW) (r : Rule) : StateM St AW := do
  modify fun s => { s with cur := r.id }
  let mut o := AW.bot
  for env0 in aPatArgs p aextE ins r.args (List.replicate r.vars.length .top) do
    for env1 in ← iIfLets p r.iflets env0 do
      o := join o (← iExpr p r.rhs env1)
  pure o

/-- The demands of `aLast`: everything but the final `emit_side_effect`. -/
partial def iLast : Nat → Isle.Expr → List AW → StateM St Unit
  | 0, _, _ => pure ()
  | n + 1, .term _ t args, env => do
    if t == TId.emit_side_effect then
      match args with
      | [e] => let _ ← iExpr p e env
      | _ => pure ()
    else
      let as ← iArgs p args env
      for r in p.rulesOf t do
        for env0 in aPatArgs p aextE as r.args (List.replicate r.vars.length .top) do
          for env1 in ← iIfLets p r.iflets env0 do
            iLast n r.rhs env1
  | n + 1, .let _ bs body, env => do
    let env' ← iBinds p bs env
    iLast n body env'
  | _ + 1, _, _ => pure ()

def lastFuel : Nat := 10

def iRuleLast (ins : List AW) (r : Rule) : StateM St Unit := do
  modify fun s => { s with cur := r.id }
  for env0 in aPatArgs p aextE ins r.args (List.replicate r.vars.length .top) do
    for env1 in ← iIfLets p r.iflets env0 do
      iLast p lastFuel r.rhs env1

/-- Roots: plain rules (`aRule`) and rules ending in a branch (`aRuleLast`). -/
structure Roots where
  plain : List (List AW × List Rule)
  last : List (List AW × List Rule)

def runRoots (roots : Roots) : StateM St Unit := do
  for (ins, rs) in roots.plain do
    for r in rs do
      let _ ← iRule p ins r
  for (ins, rs) in roots.last do
    for r in rs do
      iRuleLast p ins r

def round (roots : Roots) : StateM St Unit := do
  runRoots p roots
  let s ← get
  for ((t, ins), out) in s.tab.toList do
    let mut o := out
    for r in p.rulesOf t do
      o := join o (← iRule p ins r)
    let s ← get
    if o != out then set { s with tab := s.tab.insert (t, ins) o, changed := true }

def fix (roots : Roots) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let ((), s') := (round p roots).run { s with changed := false, bad := [] }
    if s'.changed then fix roots n s' else s'

def gcRound (roots : Roots) : StateM St Unit := do
  runRoots p roots
  let mut done : Std.HashSet Key := {}
  repeat
    let s ← get
    let todo := s.tab.toList.filter fun (x : Key × AW) => !done.contains x.1
    if todo.isEmpty then break
    for (k, _) in todo do
      done := done.insert k
      for r in p.rulesOf k.1 do
        let _ ← iRule p k.2 r

def fixGC (roots : Roots) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let s1 := fix p roots 100 s
    let ((), s2) := (gcRound p roots).run { tab := {}, old := s1.tab }
    let s3 := fix p roots 100 { tab := s2.tab }
    if s3.tab.size == s1.tab.size then s3 else fixGC roots n s3

/-- Syntactically, the expression ends in `emit_side_effect` (through `let`s and internal terms). -/
partial def endsLast : Nat → Isle.Expr → Bool
  | 0, _ => false
  | n + 1, .term _ t _ =>
    t == TId.emit_side_effect || (internalOne p t && (p.rulesOf t).all fun r => endsLast n r.rhs)
  | n + 1, .let _ _ body => endsLast n body
  | _, _ => false

end Gen

namespace Gen
open Backend.Proof.Cov

def ctyLit : CTy → String
  | .invalid => ".invalid" | .int n => s!"(.int {n})" | .float n => s!"(.float {n})"
  | .vec a b c => s!"(.vec {a} {b} {c})"

def szLit : OperandSize → String | .size32 => ".size32" | .size64 => ".size64"

def nkLit : NK → String
  | .int => "int" | .imm12 => "imm12" | .immShift => "immShift" | .uimm5 => "uimm5"
  | .uimm6 => "uimm6" | .shiftAmt => "shiftAmt" | .mwc => "mwc" | .callInfo => "callInfo"

partial def awLit : AW → String
  | .bot => ".bot" | .flat m c => s!"(.flat {m} {c})" | .reg m => s!"(.reg {m})"
  | .ty ts => s!"(.ty [{", ".intercalate (ts.map ctyLit)}])"
  | .bool b => s!"(.bool {b})" | .logic s => s!"(.logic {szLit s})" | .scale b => s!"(.scale {b})"
  | .simm9 => ".simm9"
  | .xv e => match e with | .inst => "(.xv .inst)" | .data => "(.xv .data)" | .value => "(.xv .value)"
  | .alts as => s!"(.alts [{", ".intercalate (as.map awLit)}])"
  | .data t k fs => s!"(.data {t} {k} [{", ".intercalate (fs.map awLit)}])"
  | .num k b => s!"(.num .{nkLit k} {b})"

def entryLit (e : TermId × List AW × AW) : String :=
  s!"({e.1}, [{", ".intercalate (e.2.1.map awLit)}], {awLit e.2.2})"

def stmtRules : List Rule := (program.rulesOf TId.lower).filter fun r =>
  closureRootIds.contains r.id && !emitHandIds.contains r.id
def termRules : List Rule := (program.rulesOf TId.lower).filter fun r => r.id == 964 || r.id == 1037
def lastRules : List Rule := (program.rulesOf TId.lower_branch).filter fun r => endsLast program lastFuel r.rhs
def plainBranchRules : List Rule :=
  (program.rulesOf TId.lower_branch).filter fun r => !endsLast program lastFuel r.rhs

def roots : Roots :=
  { plain := [([.xv .inst], stmtRules), ([.c0], termRules), ([.c0, .c0], plainBranchRules)]
    last := [([.c0, .c0], lastRules)] }

def mkTab (s : St) : Tab :=
  (s.tab.toList.toArray.qsort (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && toString (repr a.1.2) < toString (repr b.1.2)))).toList.map
    fun ((t, ins), o) => (t, ins, o)

end Gen

namespace Gen
open Backend.Proof.Cov

/-- Entries per chunk of the table (one definition and one `native_decide` per chunk). -/
def chunk : Nat := 60

def header : String := "import FV.Backend.Proof.IselEmitFns

/-!
# Emission conditions of the ISLE lowering (V6c): the summary table

GENERATED by `FVTest/Backend/IselEmitGen.lean` (untrusted; regenerate with
`lake env lean --run FVTest/Backend/IselEmitGen.lean FV/Backend/Proof/IselEmitTab.lean`).
Do not edit by hand.

`emitTab`: per entry an internal term, abstract inputs and an abstract output, closed under the
calls of the closure roots of `lower`, of its terminator rules and of the rules of
`lower_branch`. `emitTab_ok`: every rule of every entry checks (`chkTab` with `aextE`, `actorE`,
`apreE`, `aOracle`); `emitStmt_ok`/`emitTerm_ok`/`emitBranch_ok`: the roots check (`aRule`, or
`aRuleLast` for a branch rule ending in a branch). All are decided once over the exported rule
data.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Isle Isle.Aarch64

"

def render (tab : Tab) : String := Id.run do
  let n := (tab.length + chunk - 1) / chunk
  let mut out := header
  for k in [0:n] do
    let es := (tab.drop (k * chunk)).take chunk
    out := out ++ s!"/-- Chunk {k} of the table. -/\ndef emitTab{k} : Tab := [\n  " ++
      ",\n  ".intercalate (es.map entryLit) ++ "]\n\n"
  out := out ++ "/-- **The summary table.** -/\ndef emitTab : Tab :=\n  " ++
    " ++ ".intercalate ((List.range n).map (s!"emitTab{·}")) ++ "\n\n"
  out := out ++ "/-- `chkTab`'s test of one entry. -/\nabbrev emitEntryOk (e : TermId × List AW × AW) : Bool :=\n  (program.rulesOf e.1).all (aRule program emitTab aextE actorE apreE aOracle e.2.1 e.2.2)\n\n"
  for k in [0:n] do
    out := out ++ s!"theorem emitTab{k}_ok : (emitTab{k}).all emitEntryOk = true := by native_decide\n\n"
  out := out ++ "/-- **Every rule of every entry checks.** -/\ntheorem emitTab_ok : chkTab program emitTab aextE actorE apreE aOracle = true := by\n  unfold chkTab\n  show (emitTab).all emitEntryOk = true\n  simp only [emitTab, List.all_append, " ++
    ", ".intercalate ((List.range n).map (s!"emitTab{·}_ok")) ++ ", Bool.and_self]\n\n"
  out := out ++ "/-- The closure roots of `lower` other than the hand-checked ones check. -/
theorem emitStmt_ok : (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id ||
    emitHandIds.contains r.id || aRule program emitTab aextE actorE apreE aOracle [.xv .inst] AW.top r) = true := by native_decide

/-- The terminator rules of `lower` (964 `return`, 1037 `trap`) check. -/
theorem emitTerm_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    aRule program emitTab aextE actorE apreE aOracle [.c0] AW.top r) = true := by native_decide

/-- Every rule of `lower_branch` checks: without branches, or ending in one. -/
theorem emitBranch_ok : (program.rulesOf TId.lower_branch).all (fun r =>
    aRule program emitTab aextE actorE apreE aOracle [.c0, .c0] AW.top r ||
    aRuleLast program emitTab aextE actorE apreE aOracle 10 [.c0, .c0] r) = true := by native_decide

end Backend.Proof.Cov
"
  out

end Gen

open Gen in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: IselEmitGen <out.lean>"; return 1
  let s := fixGC program roots 10 {}
  let tab := mkTab s
  let ok := chkTab program tab aextE actorE apreE aOracle
  let failR (ins : List AW) (out : AW) (rs : List Rule) : List Nat :=
    (rs.filter fun r => !aRule program tab aextE actorE apreE aOracle ins out r).map (·.id)
  for e in tab do
    let bad := failR e.2.1 e.2.2 (program.rulesOf e.1)
    if !bad.isEmpty then IO.println s!"entry {e.1} {(", ".intercalate (e.2.1.map awLit)).take 300} fails rules {bad}"
  let stmt := failR [.xv .inst] AW.top stmtRules
  let term := failR [.c0] AW.top termRules
  let okBr (r : Rule) : Bool := aRule program tab aextE actorE apreE aOracle [.c0, .c0] AW.top r ||
    aRuleLast program tab aextE actorE apreE aOracle lastFuel [.c0, .c0] r
  let br := ((program.rulesOf TId.lower_branch).filter fun r => okBr r == false).map (·.id)
  IO.println s!"entries {tab.length} chkTab {ok} stmt {stmt} term {term} branch {br} last {lastRules.map (·.id)}"
  for (rid, msg) in s.bad.eraseDups do IO.println s!"bad rule {rid}: {msg.take 400}"
  IO.FS.writeFile path (render tab)
  return (if ok && stmt.isEmpty && term.isEmpty && br.isEmpty then 0 else 1)

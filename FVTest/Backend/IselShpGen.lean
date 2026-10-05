import FV.Backend.Proof.IselShpFns

/-!
# Generator of the V3 coverage summary table (`FV/Backend/Proof/IselShpTab.lean`)

Untrusted: computes, by a fixpoint of the disjunctive abstract interpreter (`aRule`, `AW`) over
the exported ISLE rules, a summary table for every internal term reachable from the closure roots
of `lower` and from `lower_branch`, and writes `IselShpTab.lean`: the table as Lean literals and
the `native_decide` checks (`chkTab` and the root checks) the proofs rely on.

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselShpFns`):

    lake env lean --run FVTest/Backend/IselShpGen.lean FV/Backend/Proof/IselShpTab.lean
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.Cov

deriving instance Hashable for Backend.OperandSize
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
  | .constInt .., _ => pure .c0
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
        if !apreS term.id as then
          modify fun s => { s with bad := (s.cur, s!"{term.name} {repr as}") :: s.bad }
        pure (actor term.id as)
      | .decl _ (some .internal) _ =>
        match aOracleS t as with
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
    for e in aPat p aext a il.lhs env do
      out := out ++ (← iIfLets ils e)
    pure out

def iRule (ins : List AW) (r : Rule) : StateM St AW := do
  modify fun s => { s with cur := r.id }
  let mut o := AW.bot
  for env0 in aPatArgs p aext ins r.args (List.replicate r.vars.length .top) do
    for env1 in ← iIfLets p r.iflets env0 do
      o := join o (← iExpr p r.rhs env1)
  pure o

def round (roots : List (List AW × List Rule)) : StateM St Unit := do
  for (ins, rs) in roots do
    for r in rs do
      let _ ← iRule p ins r
  let s ← get
  for ((t, ins), out) in s.tab.toList do
    let mut o := out
    for r in p.rulesOf t do
      o := join o (← iRule p ins r)
    let s ← get
    if o != out then set { s with tab := s.tab.insert (t, ins) o, changed := true }

def fix (roots : List (List AW × List Rule)) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let ((), s') := (round p roots).run { s with changed := false, bad := [] }
    if s'.changed then fix roots n s' else s'

def gcRound (roots : List (List AW × List Rule)) : StateM St Unit := do
  for (ins, rs) in roots do
    for r in rs do
      let _ ← iRule p ins r
  let mut done : Std.HashSet Key := {}
  repeat
    let s ← get
    let todo := s.tab.toList.filter fun (x : Key × AW) => !done.contains x.1
    if todo.isEmpty then break
    for (k, _) in todo do
      done := done.insert k
      for r in p.rulesOf k.1 do
        let _ ← iRule p k.2 r

def fixGC (roots : List (List AW × List Rule)) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let s1 := fix p roots 100 s
    let ((), s2) := (gcRound p roots).run { tab := {}, old := s1.tab }
    let s3 := fix p roots 100 { tab := s2.tab }
    if s3.tab.size == s1.tab.size then s3 else fixGC roots n s3

end Gen

namespace Gen
open Backend.Proof.Cov

def ctyLit : CTy → String
  | .invalid => ".invalid" | .int n => s!"(.int {n})" | .float n => s!"(.float {n})"
  | .vec a b c => s!"(.vec {a} {b} {c})"

def szLit : OperandSize → String | .size32 => ".size32" | .size64 => ".size64"

partial def awLit : AW → String
  | .bot => ".bot" | .flat m c => s!"(.flat {m} {c})" | .reg m => s!"(.reg {m})"
  | .ty ts => s!"(.ty [{", ".intercalate (ts.map ctyLit)}])"
  | .bool b => s!"(.bool {b})" | .logic s => s!"(.logic {szLit s})" | .scale b => s!"(.scale {b})"
  | .simm9 => ".simm9"
  | .xv e => match e with | .inst => "(.xv .inst)" | .data => "(.xv .data)" | .value => "(.xv .value)"
  | .alts as => s!"(.alts [{", ".intercalate (as.map awLit)}])"
  | .data t k fs => s!"(.data {t} {k} [{", ".intercalate (fs.map awLit)}])"

def entryLit (e : TermId × List AW × AW) : String :=
  s!"({e.1}, [{", ".intercalate (e.2.1.map awLit)}], {awLit e.2.2})"

def stmtRules : List Rule := (program.rulesOf TId.lower).filter fun r =>
  closureRootIds.contains r.id && !shpHandIds.contains r.id
def termRules : List Rule := (program.rulesOf TId.lower).filter fun r => r.id == 964 || r.id == 1037
def branchRules : List Rule := (program.rulesOf TId.lower_branch).filter fun r => !shpHandIds.contains r.id

def roots : List (List AW × List Rule) :=
  [([.xv .inst], stmtRules), ([.c0], termRules), ([.c0, .c0], branchRules)]

def mkTab : Tab :=
  let s := fixGC program roots 10 {}
  (s.tab.toList.toArray.qsort (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && toString (repr a.1.2) < toString (repr b.1.2)))).toList.map
    fun ((t, ins), o) => (t, ins, o)

end Gen

namespace Gen
open Backend.Proof.Cov

/-- Entries per chunk of the table (one definition and one `native_decide` per chunk). -/
def chunk : Nat := 88

def header : String := "import FV.Backend.Proof.IselShpFns

/-!
# Control shapes of the ISLE lowering (V4): the summary table

GENERATED by `FVTest/Backend/IselShpGen.lean` (untrusted; regenerate with
`lake env lean --run FVTest/Backend/IselShpGen.lean FV/Backend/Proof/IselShpTab.lean`).
Do not edit by hand.

`shpTab`: per entry an internal term, abstract inputs and an abstract output, closed under the
calls of the closure roots of `lower` and of `lower_branch` other than the hand-checked rules
`shpHandIds`. `shpTab_ok`: every rule of every entry checks (`chkTab` with `apreS`,
`aOracleS`); `shpStmt_ok`/`shpTerm_ok`/`shpBranch_ok`: the roots check (`aRule`). All are
decided once over the exported rule data.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Isle Isle.Aarch64

"

def render (tab : Tab) : String := Id.run do
  let n := (tab.length + chunk - 1) / chunk
  let mut out := header
  for k in [0:n] do
    let es := (tab.drop (k * chunk)).take chunk
    out := out ++ s!"/-- Chunk {k} of the table. -/\ndef shpTab{k} : Tab := [\n  " ++
      ",\n  ".intercalate (es.map entryLit) ++ "]\n\n"
  out := out ++ "/-- **The summary table.** -/\ndef shpTab : Tab :=\n  " ++
    " ++ ".intercalate ((List.range n).map (s!"shpTab{·}")) ++ "\n\n"
  out := out ++ "/-- `chkTab`'s test of one entry. -/\nabbrev shpEntryOk (e : TermId × List AW × AW) : Bool :=\n  (program.rulesOf e.1).all (aRule program shpTab aext actor apreS aOracleS e.2.1 e.2.2)\n\n"
  for k in [0:n] do
    out := out ++ s!"theorem shpTab{k}_ok : (shpTab{k}).all shpEntryOk = true := by native_decide\n\n"
  out := out ++ "/-- **Every rule of every entry checks.** -/\ntheorem shpTab_ok : chkTab program shpTab aext actor apreS aOracleS = true := by\n  unfold chkTab\n  show (shpTab).all shpEntryOk = true\n  simp only [shpTab, List.all_append, " ++
    ", ".intercalate ((List.range n).map (s!"shpTab{·}_ok")) ++ ", Bool.and_self]\n\n"
  out := out ++ "/-- The closure roots of `lower` other than the hand-checked ones check. -/
theorem shpStmt_ok : (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id ||
    shpHandIds.contains r.id || aRule program shpTab aext actor apreS aOracleS [.xv .inst] AW.top r) = true := by
  native_decide

/-- The terminator rules of `lower` (964 `return`, 1037 `trap`) check. -/
theorem shpTerm_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    aRule program shpTab aext actor apreS aOracleS [.c0] AW.top r) = true := by native_decide

/-- The rules of `lower_branch` other than the hand-checked ones check. -/
theorem shpBranch_ok : (program.rulesOf TId.lower_branch).all (fun r => shpHandIds.contains r.id ||
    aRule program shpTab aext actor apreS aOracleS [.c0, .c0] AW.top r) = true := by native_decide

end Backend.Proof.Cov
"
  out

end Gen

open Gen in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: IselShpGen <out.lean>"; return 1
  let s := fixGC program roots 10 {}
  let tab := mkTab
  let ok := chkTab program tab aext actor apreS aOracleS
  let failR (ins : List AW) (out : AW) (rs : List Rule) : List Nat :=
    (rs.filter fun r => !aRule program tab aext actor apreS aOracleS ins out r).map (·.id)
  for e in tab do
    let bad := failR e.2.1 e.2.2 (program.rulesOf e.1)
    if !bad.isEmpty then IO.println s!"entry {e.1} {(", ".intercalate (e.2.1.map awLit)).take 200} fails rules {bad}"
  let stmtTop := failR [.xv .inst] AW.top stmtRules
  let term := failR [.c0] AW.top termRules
  let br := failR [.c0, .c0] AW.top branchRules
  IO.println s!"entries {tab.length} chkTab {ok} stmtTop {stmtTop} term {term} branch {br}"
  for (rid, msg) in s.bad.eraseDups do IO.println s!"bad rule {rid}: {msg.take 300}"
  IO.FS.writeFile path (render tab)
  return (if ok && stmtTop.isEmpty && term.isEmpty && br.isEmpty then 0 else 1)

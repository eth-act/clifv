import FV.Backend.Proof.IselCovFns

/-!
# Generator of the V3 coverage summary table (`FV/Backend/Proof/IselCovTab.lean`)

Untrusted: computes, by a fixpoint of the disjunctive abstract interpreter (`aRule`, `AW`) over
the exported ISLE rules, a summary table for every internal term reachable from the closure roots
of `lower` and from `lower_branch`, and writes `IselCovTab.lean`: the table as Lean literals and
the `native_decide` checks (`chkTab` and the root checks) the proofs rely on.

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselCovFns`):

    lake env lean --run FVTest/Backend/IselCovGen.lean FV/Backend/Proof/IselCovTab.lean
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
        if !apre term.id as then
          modify fun s => { s with bad := (s.cur, s!"{term.name} {repr as}") :: s.bad }
        pure (actor term.id as)
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

def stmtRules : List Rule := (program.rulesOf TId.lower).filter fun r => closureRootIds.contains r.id
def termRules : List Rule := (program.rulesOf TId.lower).filter fun r => r.id == 964 || r.id == 1037
def branchRules : List Rule := program.rulesOf TId.lower_branch

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

def header : String := "import FV.Backend.Proof.IselCovFns

/-!
# Form coverage of the ISLE lowering (V3): the summary table

GENERATED by `FVTest/Backend/IselCovGen.lean` (untrusted; regenerate with
`lake env lean --run FVTest/Backend/IselCovGen.lean FV/Backend/Proof/IselCovTab.lean`).
Do not edit by hand.

`covTab`: per entry an internal term, abstract inputs and an abstract output, closed under the
calls of the closure roots of `lower` and of `lower_branch`. `covTab_ok`: every rule of every
entry checks (`chkTab`); `covStmt_ok`/`covStmtTop_ok`/`covTerm_ok`/`covBranch_ok`: the roots
check (`aRule`). All are decided once over the exported rule data.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Isle Isle.Aarch64

"

def render (tab : Tab) : String := Id.run do
  let n := (tab.length + chunk - 1) / chunk
  let mut out := header
  for k in [0:n] do
    let es := (tab.drop (k * chunk)).take chunk
    out := out ++ s!"/-- Chunk {k} of the table. -/\ndef covTab{k} : Tab := [\n  " ++
      ",\n  ".intercalate (es.map entryLit) ++ "]\n\n"
  out := out ++ "/-- **The summary table.** -/\ndef covTab : Tab :=\n  " ++
    " ++ ".intercalate ((List.range n).map (s!"covTab{·}")) ++ "\n\n"
  out := out ++ "/-- `chkTab`'s test of one entry. -/\nabbrev covEntryOk (e : TermId × List AW × AW) : Bool :=\n  (program.rulesOf e.1).all (aRule program covTab aext actor apre aOracle e.2.1 e.2.2)\n\n"
  for k in [0:n] do
    out := out ++ s!"theorem covTab{k}_ok : (covTab{k}).all covEntryOk = true := by native_decide\n\n"
  out := out ++ "/-- **Every rule of every entry checks.** -/\ntheorem covTab_ok : chkTab program covTab aext actor apre aOracle = true := by\n  unfold chkTab\n  show (covTab).all covEntryOk = true\n  simp only [covTab, List.all_append, " ++
    ", ".intercalate ((List.range n).map (s!"covTab{·}_ok")) ++ ", Bool.and_self]\n\n"
  out := out ++ "/-- The closure roots of `lower` other than `nop`'s rule 587 check with int-vreg results. -/
theorem covStmt_ok : (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id || r.id == 587 ||
    aRule program covTab aext actor apre aOracle [.xv .inst] (.flat 1 true) r) = true := by native_decide

/-- The closure roots of `lower` check with any result. -/
theorem covStmtTop_ok : (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id ||
    aRule program covTab aext actor apre aOracle [.xv .inst] AW.top r) = true := by native_decide

/-- The terminator rules of `lower` (964 `return`, 1037 `trap`) check. -/
theorem covTerm_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    aRule program covTab aext actor apre aOracle [.c0] AW.top r) = true := by native_decide

/-- Every rule of `lower_branch` checks. -/
theorem covBranch_ok : (program.rulesOf TId.lower_branch).all
    (aRule program covTab aext actor apre aOracle [.c0, .c0] AW.top) = true := by native_decide

end Backend.Proof.Cov
"
  out

end Gen

open Gen in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: IselCovGen <out.lean>"; return 1
  let tab := mkTab
  let ok := chkTab program tab aext actor apre aOracle
  let stmt := stmtRules.all fun r => aRule program tab aext actor apre aOracle [.xv .inst]
    (if r.id == 587 then AW.top else .flat 1 true) r
  let stmtTop := stmtRules.all (aRule program tab aext actor apre aOracle [.xv .inst] AW.top)
  let term := termRules.all (aRule program tab aext actor apre aOracle [.c0] AW.top)
  let br := branchRules.all (aRule program tab aext actor apre aOracle [.c0, .c0] AW.top)
  IO.println s!"entries {tab.length} chkTab {ok} stmt {stmt} stmtTop {stmtTop} term {term} branch {br}"
  IO.FS.writeFile path (render tab)
  return (if ok && stmt && stmtTop && term && br then 0 else 1)

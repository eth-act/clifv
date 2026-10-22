import FV.Backend.Proof.IselCovTFns

/-!
# Generator of the V3 coverage summary table (`FV/Backend/Proof/IselCovTab.lean`)

Untrusted: computes, by a fixpoint of the disjunctive abstract interpreter (`aRule`, `AT`) over
the exported ISLE rules, a summary table for every internal term reachable from the closure roots
of `lower` and from `lower_branch`, and writes `IselCovTab.lean`: the table as Lean literals and
the leaf-wise `decide +kernel` checks (`chkTab` and the root checks) the proofs rely on.

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselCovFns`):

    lake env lean --run FVTest/Backend/IselCovGen.lean FV/Backend/Proof/IselCovTab.lean

The checked-in table (704 entries, 8 chunks) was computed at V3 (#53), before V6c (#79) added the
`.num` leaves to `AT`; since then this generator gives 707 entries (`.num` summaries of terms 306,
414, 417 and 570; same output on `main` and with typed calls, S11e5a), and both tables pass
`chkTab`. The checked-in one is kept: `StockNoOpportunityTable` pins `covTab.length = 704`, and
`IselSzTab`/`StockSourceSinkTable` are built over its chunks. Regenerating it means regenerating
those too; only the root checks' text (`covStmt_ok`'s excluded rules) has followed the generator.
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.CovT
open Backend.Proof.Cov (NK)

deriving instance Hashable for Backend.OperandSize
deriving instance Hashable for Backend.Proof.CovT.AT

namespace Gen
open AT

def insAlt (b : AT) (as : List AT) (j : AT → AT → AT) : List AT :=
  match b with
  | .data t k fs =>
    if as.any (fun a => match a with | .data t' k' gs => t == t' && k == k' && fs.length == gs.length | _ => false)
    then as.map fun a => match a with
      | .data t' k' gs => if t == t' && k == k' && fs.length == gs.length then j a b else a
      | a => a
    else as ++ [b]
  | _ => as

partial def join : AT → AT → AT
  | .bot, b => b
  | a, .bot => a
  | .reg m, .reg n => .reg (m ||| n)
  | .ty a, .ty b => .ty (a ++ b.filter (!a.contains ·))
  | .num k b, .num k' b' => if k == k' then .num k (max b b') else .flat (if k == .callInfo || k' == .callInfo then 15 else 0) true
  | .val a, .val b => .val (a ++ b.filter (!a.contains ·))
  | .valsAll a, .valsAll b => .valsAll (a ++ b.filter (!a.contains ·))
  | .vals a, .vals b =>
    if a.length == b.length then .vals ((a.zip b).map fun (x, y) => x ++ y.filter (!x.contains ·))
    else .valsAll (a.flatten ++ b.flatten)
  | .vals a, .valsAll b => .valsAll (a.flatten ++ b)
  | .valsAll a, .vals b => .valsAll (a ++ b.flatten)
  | .inst a, .inst b => .inst (a ++ b.filter (!a.contains ·))
  | .data t k fs, .data t' k' gs =>
    if t == t' && k == k' && fs.length == gs.length then .data t k ((fs.zip gs).map fun (x, y) => join x y)
    else .alts [.data t k fs, .data t' k' gs]
  | .alts as, b@(.data ..) => .alts (insAlt b as join)
  | a@(.data ..), .alts bs => .alts (insAlt a bs join)
  | .alts as, .alts bs => .alts (bs.foldl (fun acc b => insAlt b acc join) as)
  | a, b => if a == b then a else
    let d := deep a; let e := deep b; .flat (d.1 ||| e.1) (d.2 && e.2)

abbrev Key := TermId × List AT

structure St where
  tab : Std.HashMap Key AT := {}
  old : Std.HashMap Key AT := {}
  changed : Bool := false
  bad : List (Nat × String) := []
  cur : Nat := 0
  from_ : Std.HashMap Key Nat := {}

def demand (t : TermId) (as : List AT) : StateM St AT := do
  let s ← get
  match s.tab.get? (t, as) with
  | some out => pure out
  | none =>
    let o := (s.old.get? (t, as)).getD .bot
    set { s with tab := s.tab.insert (t, as) o, changed := true, from_ := s.from_.insert (t, as) s.cur }
    pure o

variable (p : Program)

mutual
partial def iExpr : Isle.Expr → List AT → StateM St AT
  | .var _ x, env => pure (env.getD x .top)
  | .constBool _ b, _ => pure (.bool b)
  | .constInt _ n, _ => pure (aint n)
  | .constPrim tyv n, _ => pure (aprim tyv n)
  | .let _ bs body, env => do let env' ← iBinds bs env; iExpr body env'
  | .term tyv t args, env => do
    let as ← iArgs args env
    if as.any AT.isBot then pure .bot else
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
partial def iArgs : List Isle.Expr → List AT → StateM St (List AT)
  | [], _ => pure []
  | e :: es, env => do let a ← iExpr e env; let as ← iArgs es env; pure (a :: as)
partial def iBinds : List (VarId × TypeId × Isle.Expr) → List AT → StateM St (List AT)
  | [], env => pure env
  | (x, _, e) :: bs, env => do let a ← iExpr e env; iBinds bs (env.set x a)
end

partial def iIfLets : List IfLet → List AT → StateM St (List (List AT))
  | [], env => pure [env]
  | il :: ils, env => do
    let a ← iExpr p il.rhs env
    let mut out := []
    for e in aPat p aext a il.lhs env do
      out := out ++ (← iIfLets ils e)
    pure out

def iRule (ins : List AT) (r : Rule) : StateM St AT := do
  modify fun s => { s with cur := r.id }
  let mut o := AT.bot
  for env0 in aPatArgs p aext ins r.args (List.replicate r.vars.length .top) do
    for env1 in ← iIfLets p r.iflets env0 do
      o := join o (← iExpr p r.rhs env1)
  pure o

def round (roots : List (List AT × List Rule)) : StateM St Unit := do
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

def fix (roots : List (List AT × List Rule)) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let ((), s') := (round p roots).run { s with changed := false, bad := [] }
    if s'.changed then fix roots n s' else s'

def gcRound (roots : List (List AT × List Rule)) : StateM St Unit := do
  for (ins, rs) in roots do
    for r in rs do
      let _ ← iRule p ins r
  let mut done : Std.HashSet Key := {}
  repeat
    let s ← get
    let todo := s.tab.toList.filter fun (x : Key × AT) => !done.contains x.1
    if todo.isEmpty then break
    for (k, _) in todo do
      done := done.insert k
      for r in p.rulesOf k.1 do
        let _ ← iRule p k.2 r

def fixGC (roots : List (List AT × List Rule)) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let s1 := fix p roots 100 s
    let ((), s2) := (gcRound p roots).run { tab := {}, old := s1.tab }
    let s3 := fix p roots 100 { tab := s2.tab }
    if s3.tab.size == s1.tab.size then s3 else fixGC roots n s3

end Gen

namespace Gen
open Backend.Proof.CovT

def ctyLit : CTy → String
  | .invalid => ".invalid" | .int n => s!"(.int {n})" | .float n => s!"(.float {n})"
  | .vec a b c => s!"(.vec {a} {b} {c})"

def szLit : OperandSize → String | .size32 => ".size32" | .size64 => ".size64"

def nkLit : NK → String
  | .int => "int" | .imm12 => "imm12" | .immShift => "immShift" | .uimm5 => "uimm5"
  | .uimm6 => "uimm6" | .shiftAmt => "shiftAmt" | .mwc => "mwc" | .callInfo => "callInfo"

partial def awLit : AT → String
  | .bot => ".bot" | .flat m c => s!"(.flat {m} {c})" | .reg m => s!"(.reg {m})"
  | .ty ts => s!"(.ty [{", ".intercalate (ts.map ctyLit)}])"
  | .bool b => s!"(.bool {b})" | .logic s => s!"(.logic {szLit s})" | .scale b => s!"(.scale {b})"
  | .simm9 => ".simm9"
  | .val ts => s!"(.val [{", ".intercalate (ts.map ctyLit)}])"
  | .vals tss => s!"(.vals [{", ".intercalate (tss.map fun ts => s!"[{", ".intercalate (ts.map ctyLit)}]")}])"
  | .valsAll ts => s!"(.valsAll [{", ".intercalate (ts.map ctyLit)}])"
  | .inst fs => s!"(.inst {fs})"
  | .movi => ".movi" | .extv => ".extv"
  | .alts as => s!"(.alts [{", ".intercalate (as.map awLit)}])"
  | .data t k fs => s!"(.data {t} {k} [{", ".intercalate (fs.map awLit)}])"
  | .num k b => s!"(.num .{nkLit k} {b})"

def entryLit (e : TermId × List AT × AT) : String :=
  s!"({e.1}, [{", ".intercalate (e.2.1.map awLit)}], {awLit e.2.2})"

def stmtRules : List Rule := program.rulesOf TId.lower
def termRules : List Rule := (program.rulesOf TId.lower).filter fun r => r.id == 964 || r.id == 1037
def branchRules : List Rule := program.rulesOf TId.lower_branch

def roots : List (List AT × List Rule) :=
  ((List.range famTab.length).map fun i => ([.inst [i]], stmtRules)) ++
    ((List.range famTab.length).map fun i => ([.inst [i], .c0], branchRules))

def mkTab : Tab :=
  let s := fixGC program roots 10 {}
  (s.tab.toList.toArray.qsort (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && toString (repr a.1.2) < toString (repr b.1.2)))).toList.map
    fun ((t, ins), o) => (t, ins, o)

end Gen

namespace Gen
open Backend.Proof.CovT

/-- Entries per chunk of the table (one definition and one leaf-wise kernel proof per chunk). -/
def chunk : Nat := 88

def header : String := "import FV.Backend.Proof.IselCovTFns

/-!
# Form coverage over float-capable contexts (typed V3): the summary table

GENERATED by `FVTest/Backend/IselCovTGen.lean` (untrusted; regenerate with
`lake env lean --run FVTest/Backend/IselCovTGen.lean FV/Backend/Proof/IselCovTTab.lean`).
Do not edit by hand.

`covTabT`: per entry an internal term, abstract inputs and an abstract output, closed under the
calls of every rule of `lower` and `lower_branch` on every instruction family (`famTab`).
`covTabT_ok`: every rule of every entry checks (`chkTab`); `covStmtT_ok`: every rule of `lower`
checks on every family, with the family's result classes (`famOut`) except the `call` rules
1031-1033 (any result; their results by hand); `covTermT_ok`: the terminator rules of `lower` check;
`covBranchT_ok`: every rule of `lower_branch` checks on every family. All are decided leaf-wise (one leaf
per rule or table entry) by the kernel over the exported rule data.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Backend.Proof.CovT

open Backend Backend.Proof Isle Isle.Aarch64

/-- The result of a statement of family `i`: registers of the family's result classes. -/
def famOut (i : Nat) : AT :=
  let F := famTab.getD i default
  if F.all.isEmpty then AT.top else .flat (vcls F.all) true

/-- The output a rule of `lower` is checked against on family `i`. -/
def stmtOut (r : Rule) (i : Nat) : AT :=
  if r.id == 1031 || r.id == 1032 || r.id == 1033 then AT.top else famOut i

"

def render (tab : Tab) : String := Id.run do
  let n := (tab.length + chunk - 1) / chunk
  let mut out := header
  for k in [0:n] do
    let es := (tab.drop (k * chunk)).take chunk
    out := out ++ s!"/-- Chunk {k} of the table. -/\ndef covTabT{k} : Tab := [\n  " ++
      ",\n  ".intercalate (es.map entryLit) ++ "]\n\n"
  out := out ++ "/-- **The summary table.** -/\ndef covTabT : Tab :=\n  " ++
    " ++ ".intercalate ((List.range n).map (s!"covTabT{·}")) ++ "\n\n"
  out := out ++ "/-- `chkTab`'s test of one entry. -/\nabbrev covEntryOkT (e : TermId × List AT × AT) : Bool :=\n  (program.rulesOf e.1).all (aRule program covTabT aext actor apre aOracle e.2.1 e.2.2)\n\n"
  for k in [0:n] do
    out := out ++ s!"theorem covTabT{k}_ok : (covTabT{k}).all covEntryOkT = true := by\n  simp only [covTabT{k}, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]\n  repeat' apply And.intro\n  all_goals decide +kernel\n\n"
  out := out ++ "/-- **Every rule of every entry checks.** -/\ntheorem covTabT_ok : chkTab program covTabT aext actor apre aOracle = true := by\n  unfold chkTab\n  show (covTabT).all covEntryOkT = true\n  simp only [covTabT, List.all_append, " ++
    ", ".intercalate ((List.range n).map (s!"covTabT{·}_ok")) ++ ", Bool.and_self]\n\n"
  out := out ++ "/-- **Every rule of `lower` checks on every family** (`stmtOut`). -/
theorem covStmtT_ok : (program.rulesOf TId.lower).all (fun r => (List.range famTab.length).all fun i =>
    aRule program covTabT aext actor apre aOracle [.inst [i]] (stmtOut r i) r) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- The terminator rules of `lower` (964 `return`, 1037 `trap`) check. -/
theorem covTermT_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    aRule program covTabT aext actor apre aOracle [.c0] AT.top r) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- Every rule of `lower_branch` checks on every family. -/
theorem covBranchT_ok : (program.rulesOf TId.lower_branch).all (fun r =>
    (List.range famTab.length).all fun i =>
      aRule program covTabT aext actor apre aOracle [.inst [i], .c0] AT.top r) = true := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

end Backend.Proof.CovT
"
  out

end Gen

open Gen in
def famOut (i : Nat) : AT :=
  let F := famTab.getD i default
  if F.all.isEmpty then AT.top else .flat (vcls F.all) true

open Gen in
def stmtOut (r : Rule) (i : Nat) : AT :=
  if r.id == 1031 || r.id == 1032 || r.id == 1033 then AT.top else famOut i

open Gen in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: IselCovTGen <out.lean>"; return 1
  let tab := mkTab
  let ok := chkTab program tab aext actor apre aOracle
  IO.println s!"entries {tab.length} chkTab {ok}"
  let tmap : Std.HashMap Gen.Key AT := tab.foldl (fun m e => m.insert (e.1, e.2.1) e.2.2) {}
  let ((), sd) := (Gen.gcRound program roots).run { old := tmap }
  let froms := sd.from_
  for e in tab do
    for r in program.rulesOf e.1 do
      if !aRule program tab aext actor apre aOracle e.2.1 e.2.2 r then
        IO.println s!"  tab fail term {e.1} rule {r.id} ins {(e.2.1.map awLit)} out {awLit e.2.2} from rule {froms.get? (e.1, e.2.1)}"
        match aRuleEnvs program tab aext actor apre aOracle e.2.1 r with
        | none => IO.println "    envs: none (an if-let/arg check failed)"
        | some envs =>
          for env in envs do
            match aExpr program tab actor apre aOracle r.rhs env with
            | none => IO.println s!"    rhs none; env {(env.map awLit)}"
            | some a => IO.println s!"    rhs {awLit a}"
  let mut allOk := ok
  for i in List.range famTab.length do
    let topBad := stmtRules.filter fun r => !aRule program tab aext actor apre aOracle [.inst [i]] AT.top r
    let resBad := stmtRules.filter fun r => !aRule program tab aext actor apre aOracle [.inst [i]] (stmtOut r i) r
    if !topBad.isEmpty || !resBad.isEmpty then allOk := false
    IO.println s!"family {i}: top-fail {topBad.map (·.id)} res-fail {resBad.map (·.id)}"
  let termBad := termRules.filter fun r => !aRule program tab aext actor apre aOracle [.c0] AT.top r
  IO.println s!"term [.c0] fails {termBad.map (·.id)}"
  let term := termBad.isEmpty
  let mut br := true
  for i in List.range famTab.length do
    let bad := branchRules.filter fun r => !aRule program tab aext actor apre aOracle [.inst [i], .c0] AT.top r
    if !bad.isEmpty then
      br := false
      IO.println s!"branch family {i} fails {bad.map (·.id)}"
  IO.println s!"term {term} branch {br}"
  IO.FS.writeFile path (render tab)
  return (if allOk && term && br then 0 else 1)

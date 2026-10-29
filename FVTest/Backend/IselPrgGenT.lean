module

public import FV.Backend.Proof.IselPrgRootTF
public import FVTest.ModuleHeader

@[expose] public section

/-!
# Generator of the progress summary tables over the typed scope

`IselPrgGen.lean` for the typed scope (`IselPrgRootT`, `IselPrgExtT`): untrusted, computes by a
fixpoint of the abstract interpreter of `IselPrgCheck` (mirrored here with on-demand table
entries) a summary table for every internal term reachable from its roots, checks it with the
real `chkEntry` (reporting every failing entry with the reason) and writes it as Lean literals
with the leaf-wise `decide +kernel` checks the proofs rely on. Two tables:

* `prgTabT` (`FV/Backend/Proof/IselPrgTabT.lean`): the statement roots `stmtFormsT` and the
  terminator roots `termRootsT`, with the hand-checked rules `handRulesT`;
* `f64Tab` (`FV/Backend/Proof/IselPrgTabF64.lean`): the terms the hand-checked `f64const` rule
  calls (`f64Roots`), without hand-checked rules; the entry of `constant_f64` on a bit pattern of
  at least `2^32` (`f64Hi`) is computed for its callees and left out (its last rule needs the
  literal pool, which the hand proof excludes).

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselPrgRootT`):

    lake env lean --run FVTest/Backend/IselPrgGenT.lean FV/Backend/Proof/IselPrgTabT.lean FV/Backend/Proof/IselPrgTabF64.lean

Without output paths it only reports.
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.Prg

deriving instance BEq for Backend.Proof.Prg.PA
deriving instance Hashable for Backend.Proof.Prg.PA

namespace PrgGenT

/-! ## Join -/

partial def join : PA → PA → PA
  | .bot, b => b
  | a, .bot => a
  | .any, _ => .any
  | _, .any => .any
  | a, b =>
    if a == b then a else
    match a, b with
    | .int lo hi, .int lo' hi' => .int (do pure (min (← lo) (← lo'))) (do pure (max (← hi) (← hi')))
    | .bool c, .bool d => .bool (if c == d then c else none)
    | .ty ts, .ty us => .ty (ts ++ us.filter (!ts.contains ·))
    | .val ts, .val us => .val (ts ++ us.filter (!ts.contains ·))
    | .inst t d, .inst t' d' => .inst (join t t') (join d d')
    | .vals as, .vals bs => if as.length == bs.length then .vals ((as.zip bs).map fun (x, y) => join x y) else .valsMin (min as.length bs.length)
    | .vals as, .valsMin lo | .valsMin lo, .vals as => .valsMin (min lo as.length)
    | .valsMin lo, .valsMin lo' => .valsMin (min lo lo')
    | .regs n, .regs m => if n == m then .regs n else .any
    | .regsVec n, .regsVec m => .regsVec (if n == m then n else none)
    | .labels lo n, .labels lo' n' => .labels (min lo lo') (if n == n' then n else none)
    | .data t k fs, .data t' k' gs =>
      if t == t' && k == k' && fs.length == gs.length then .data t k ((fs.zip gs).map fun (x, y) => join x y)
      else .alts [a, b]
    | .op k n, .op k' n' => if k == k' then .op k (if n == n' then n else none) else .any
    | .alts as, .alts bs => .alts (bs.foldl (fun acc x => insAlt acc x) as)
    | .alts as, x => .alts (insAlt as x)
    | x, .alts bs => .alts (insAlt bs x)
    | _, _ => .any
where
  insAlt (as : List PA) (x : PA) : List PA :=
    if as.contains x then as else
    match x with
    | .data t k fs =>
      match as.findIdx? (fun a => match a with | .data t' k' gs => t == t' && k == k' && fs.length == gs.length | _ => false) with
      | some i => as.modify i (fun a => join a x)
      | none => as ++ [x]
    | _ => as ++ [x]

/-! ## The fixpoint -/

abbrev Key := TermId × List PA

structure Info where
  out : PA := .bot
  osome : Bool := true
  fu : Nat := 1
  deriving BEq, Inhabited

structure St where
  tab : Std.HashMap Key Info := {}
  order : Array Key := #[]
  changed : Bool := false
  cur : Key × Nat := ((0, []), 0)
  snap : PTab := []
  callers : Std.HashMap Key (Key × Nat) := {}
  hand : RuleId → Option (Nat × PA) := fun _ => none
  aext : TermId → PA → Option (List (List PA) × Bool) := aextT

def demand (t : TermId) (as : List PA) : StateM St Info := do
  let s ← get
  match s.tab.get? (t, as) with
  | some i => pure i
  | none =>
    set { s with tab := s.tab.insert (t, as) {}, order := s.order.push (t, as), changed := true,
                 callers := s.callers.insert (t, as) s.cur }
    pure {}


mutual
partial def gExpr : Isle.Expr → AEnv → StateM St (Option (PA × Bool × Nat))
  | .var _ x, env => pure (match env[x]? with | some (some a) => some (a, true, 1) | _ => none)
  | .constBool _ b, _ => pure (some (.bool (some b), true, 1))
  | .constInt ty i, _ => pure (some (aint ty i, true, 1))
  | .constPrim ty n, _ => pure (match primP ty n with | some (.ty t) => some (.ty [t], true, 1) | _ => none)
  | .let _ bs body, env => do
    match ← gBinds bs env with
    | none => pure none
    | some (env', m1, c1) =>
      match ← gExpr body env' with
      | none => pure none
      | some (a, m2, c2) => pure (some (a, m1 && m2, 1 + max c1 c2))
  | .term ty t args, env => do
    match ← gArgs args env with
    | none => pure none
    | some (as, m1, c1) =>
      match ← gApply ty t as with
      | none => pure none
      | some (a, m2, c2) => pure (some (a, m1 && m2, 1 + max c1 c2))
partial def gArgs : List Isle.Expr → AEnv → StateM St (Option (List PA × Bool × Nat))
  | [], _ => pure (some ([], true, 1))
  | e :: es, env => do
    match ← gExpr e env with
    | none => pure none
    | some (a, m1, c1) =>
      match ← gArgs es env with
      | none => pure none
      | some (as, m2, c2) => pure (some (a :: as, m1 && m2, 1 + max c1 c2))
partial def gBinds : List (VarId × TypeId × Isle.Expr) → AEnv → StateM St (Option (AEnv × Bool × Nat))
  | [], env => pure (some (env, true, 1))
  | (x, _, e) :: bs, env => do
    match ← gExpr e env with
    | none => pure none
    | some (a, m1, c1) =>
      if x < env.length then
        match ← gBinds bs (env.set x (some a)) with
        | none => pure none
        | some (env', m2, c2) => pure (some (env', m1 && m2, 1 + max c1 c2))
      else pure none
partial def gApply (ty : TypeId) (t : TermId) (as : List PA) : StateM St (Option (PA × Bool × Nat)) := do
  if as.any PA.isBot then return some (.bot, true, 1)
  match termOf program t with
  | .error _ => pure none
  | .ok term =>
    match term.kind with
    | .enumVariant k => pure (some (.data ty k as, true, 1))
    | .struct => pure (some (.data ty 0 as, true, 1))
    | .decl flags (some (.external _)) _ =>
      if flags.isMulti then pure none else
      pure <| match actorT term.id as with
        | none => none
        | some (a, mustOk) => if !flags.isPartial && !mustOk then none else some (a, mustOk, 1)
    | .decl flags (some .internal) _ =>
      if flags.isMulti then pure none else do
      let i ← demand t as
      pure (some (i.out, i.osome, i.fu))
    | _ => pure none
end

partial def gIfLets : List IfLet → AEnv → StateM St (Option (List AEnv × Bool × Nat))
  | [], env => pure (some ([env], true, 1))
  | il :: ils, env => do
    match ← gExpr il.rhs env with
    | none => pure none
    | some (a, m1, c1) =>
      match aPat program (← get).aext aidata a il.lhs env with
      | none => pure none
      | some (envs, m2) =>
        let mut rs := []
        for e in envs do
          match ← gIfLets ils e with
          | none => return none
          | some r => rs := rs ++ [r]
        pure (some (rs.flatMap (·.1), m1 && m2 && rs.all (·.2.1), 1 + max c1 (maxCost (rs.map (·.2.2)))))

def gRule (ins : List PA) (r : Rule) : StateM St (Option (List AEnv × Bool × Nat)) := do
  match aPatArgs program (← get).aext aidata ins r.args (List.replicate r.vars.length none) with
  | none => pure none
  | some (envs, m) =>
    let mut rs := []
    for e in envs do
      match ← gIfLets r.iflets e with
      | none => return none
      | some x => rs := rs ++ [x]
    pure (some (rs.flatMap (·.1), m && rs.all (·.2.1), maxCost (rs.map (·.2.2))))

/-- The current table as a `PTab` (in insertion order). -/
def curTab (s : St) : PTab :=
  s.order.toList.map fun k =>
    let i := s.tab.getD k {}
    (k.1, k.2, i.out, i.osome, i.fu)

/-- Evaluate one key: its new info and the problems found. -/
def evalKey (k : Key) : StateM St (Info × List String) := do
  let (t, ins) := k
  match termOf program t with
  | .error _ => pure ({}, ["unknown term"])
  | .ok term =>
    match term.kind with
    | .decl flags (some .internal) _ =>
      let rules := program.rulesOf t
      let mut cs : List (Nat × Nat) := []
      let mut out : PA := .bot
      let mut allMust := true
      let mut errs : List String := []
      let mut reached : List Rule := []
      for r in rules do
        modify fun s => { s with cur := (k, r.id) }
        reached := reached ++ [r]
        let mustR := mustRule program (← get).snap (← get).aext actorT aidata ins r
        match ← gRule ins r with
        | none => errs := errs ++ [s!"match of rule {r.id} ({r.name}) may throw"]; cs := cs ++ [(1, 1)]
        | some (envs, _, ilc) =>
          if let some (hc, ha) := (← get).hand r.id then
            if !envs.isEmpty then out := join out ha
            cs := cs ++ [(ilc, hc)]
            if mustR then break
            continue
          let mut rcs : List Nat := []
          for env in envs do
            match ← gExpr r.rhs env with
            | none => errs := errs ++ [s!"rhs of rule {r.id} ({r.name}) may throw"]
            | some (a, m, c) => out := join out a; allMust := allMust && m; rcs := c :: rcs
          cs := cs ++ [(ilc, maxCost rcs)]
        if mustR then break
      let fu := 1 + max (selCost cs) (maxCost (cs.map (·.2)))
      let s ← get
      let exh := exhaustive program s.snap s.aext actorT aidata reached ins
      if !flags.isPartial && !exh then errs := errs ++ ["not exhaustive"]
      pure ({ out, osome := allMust && (exh || !flags.isPartial), fu }, errs)
    | _ => pure ({}, ["not an internal constructor"])

def step : StateM St (List (Key × List String)) := do
  modify fun s => { s with changed := false, snap := curTab s }
  let mut errs : List (Key × List String) := []
  let mut i := 0
  while i < (← get).order.size do
    let k := (← get).order[i]!
    let old := (← get).tab.getD k {}
    let (new, es) ← evalKey k
    let merged : Info := { out := join old.out new.out, osome := old.osome && new.osome, fu := max old.fu new.fu }
    if !(merged == old) then
      modify fun s => { s with tab := s.tab.insert k merged, changed := true }
    if !es.isEmpty then errs := errs ++ [(k, es)]
    i := i + 1
  pure errs

end PrgGenT


/-! ## Lean source of the table -/

def ctyS : CTy → String
  | .invalid => ".invalid"
  | .int b => s!"(.int {b})"
  | .float b => s!"(.float {b})"
  | .vec a b c => s!"(.vec {a} {b} {c})"

def optS {α : Type} (f : α → String) : Option α → String
  | none => "none"
  | some a => s!"(some {f a})"

def intS (i : Int) : String := if i < 0 then s!"({i})" else s!"{i}"

def okS (k : OK) : String := "." ++ (toString (repr k)).replace "Backend.Proof.Prg.OK." ""

partial def paS : PA → String
  | .bot => ".bot"
  | .any => ".any"
  | .int lo hi => s!"(.int {optS intS lo} {optS intS hi})"
  | .bool b => s!"(.bool {optS toString b})"
  | .ty ts => s!"(.ty [{", ".intercalate (ts.map ctyS)}])"
  | .inst t d => s!"(.inst {paS t} {paS d})"
  | .val ts => s!"(.val [{", ".intercalate (ts.map ctyS)}])"
  | .vals as => s!"(.vals [{", ".intercalate (as.map paS)}])"
  | .valsMin lo => s!"(.valsMin {lo})"
  | .reg => ".reg"
  | .regs n => s!"(.regs {n})"
  | .regsVec n => s!"(.regsVec {optS toString n})"
  | .label => ".label"
  | .labels lo n => s!"(.labels {lo} {optS toString n})"
  | .blockCalls n => s!"(.blockCalls {n})"
  | .data t k fs => s!"(.data {t} {k} [{", ".intercalate (fs.map paS)}])"
  | .alts as => s!"(.alts [{", ".intercalate (as.map paS)}])"
  | .idata => ".idata"
  | .op k n => s!"(.op {okS k} {optS toString n})"

def entS (e : PEnt) : String :=
  s!"  ({e.1}, [{", ".intercalate (e.2.1.map paS)}], {paS e.2.2.1}, {e.2.2.2.1}, {e.2.2.2.2})"

/-- The file header of a generated table. -/
def header (doc : String) (imp : String := "FV.Backend.Proof.IselPrgRootT") : String := s!"import {imp}

/-!
{doc}

GENERATED by `FVTest/Backend/IselPrgGenT.lean` (untrusted; regenerate with
`lake env lean --run FVTest/Backend/IselPrgGenT.lean FV/Backend/Proof/IselPrgTabT.lean
FV/Backend/Proof/IselPrgTabF64.lean`, the float scope's with
`lake env lean --run FVTest/Backend/IselPrgGenT.lean --tf FV/Backend/Proof/IselPrgTabTF.lean`).
Do not edit by hand.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64
"

/-- The table `nm` as chunked literals with its leaf-wise check `{nm}_ok` (hand-checked rules
`handNm`). -/
def tabSrc (nm handNm : String) (tab : PTab) (aextNm : String := "aextT") : String := Id.run do
  let chunk := 40
  let ents := tab.toArray
  let nch := (ents.size + chunk - 1) / chunk
  let mut out := ""
  for c in [0:nch] do
    let es := (ents.extract (c * chunk) ((c + 1) * chunk)).toList
    out := out ++ s!"\n/-- Chunk {c} of the table. -/\ndef {nm}{c} : PTab := [\n" ++ ",\n".intercalate (es.map entS) ++ "]\n"
  out := out ++ s!"\n/-- **The summary table.** -/\ndef {nm} : PTab :=\n  " ++ " ++ ".intercalate ((List.range nch).map fun c => s!"{nm}{c}") ++ "\n"
  out := out ++ s!"\n/-- `chkTab`'s test of one entry. -/\nabbrev {nm}EntryOk (e : PEnt) : Bool :=\n  chkEntry program {nm} {aextNm} actorT aidata {handNm} e\n"
  for c in [0:nch] do
    out := out ++ s!"\ntheorem {nm}{c}_ok : ({nm}{c}).all {nm}EntryOk = true := by\n  simp only [{nm}{c}, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]\n  repeat' apply And.intro\n  all_goals decide +kernel\n"
  out := out ++ s!"\n/-- **Every entry checks.** -/\ntheorem {nm}_ok : chkTab program {nm} {aextNm} actorT aidata {handNm} = true := by\n  unfold chkTab\n  show ({nm}).all {nm}EntryOk = true\n  simp only [{nm}, List.all_append, " ++ ", ".intercalate ((List.range nch).map fun c => s!"{nm}{c}_ok") ++ ", Bool.and_self]\n"
  return out

open PrgGenT in
/-- Run the fixpoint from `roots` with the hand-checked rules `hand`, report, and return the
table. -/
def gen (roots : List Key) (hand : RuleId → Option (Nat × PA))
    (aext : TermId → PA → Option (List (List PA) × Bool) := aextT) : IO (PTab × St) := do
  let p := program
  let mut s : St := { hand, aext }
  for k in roots do
    s := { s with tab := s.tab.insert k {}, order := s.order.push k }
  let mut errs : List (Key × List String) := []
  let mut iter := 0
  repeat
    let (es, s') := step.run s
    s := s'
    errs := es
    iter := iter + 1
    IO.println s!"iteration {iter}: {s.order.size} entries, changed={s.changed}, problems={errs.length}"
    if !s.changed || iter ≥ 40 then break
  let tab := curTab s
  let showK (k : Key) : String := s!"{p.termName k.1} ({k.1}) {repr k.2 |>.pretty 300 |>.take 600}"
  let diag (k : Key) : IO Unit := do
    let some i := s.tab.get? k | pure ()
    let rr := reach p tab aext actorT aidata k.2 (p.rulesOf k.1)
    IO.println s!"DIAG {showK k} osome={i.osome} exh={exhaustive p tab aext actorT aidata rr k.2}"
    for r in rr do
      match aRule p tab aext actorT aidata k.2 r with
      | none => IO.println s!"   rule {r.id} {r.name}: match may throw"
      | some (envs, m, _) =>
        if !envs.isEmpty then
          let rs := envs.map fun env => match aExpr p tab actorT r.rhs env with
            | none => "THROW"
            | some (a, mm, _) => s!"{if PA.le a i.out then "le" else "NOTLE"}/{mm}"
          IO.println s!"   rule {r.id} {r.name}: must={m} envs={envs.length} rhs={rs}"
  for (k, es) in errs.take 80 do
    IO.println s!"PROBLEM {showK k}"
    diag k
    for e in es.take 6 do IO.println s!"   {e}"
    let mut c := k
    for _ in [0:6] do
      match s.callers.get? c with
      | some (c', rid) => IO.println s!"   <- rule {rid} of {showK c'}"; c := c'
      | none => break
  let maxFu := (s.order.toList.map fun k => (s.tab.getD k {}).fu).foldl max 0
  IO.println s!"max fuel {maxFu}"
  pure (tab, s)

/-- The float scope's table (S11f, #35): `prgTabTF` from the roots `stmtFormsTF`/`termRootsT`
with `aextTF`, and the check of the existing `f64Tab` under `aextTF` (`f64TabF_ok`). -/
def mainTF (path : String) : IO Unit := do
  let p := program
  let (tab, s) ← gen ((stmtFormsTF.map fun F => (TId.lower, [F])) ++ termRootsT) handRulesT
    aextTF
  let mut nroot := 0
  for F in stmtFormsTF do
    let i := s.tab.getD (TId.lower, [F]) {}
    if !i.osome || !PA.le i.out (stmtOut F) then
      IO.println s!"ROOT stmt osome={i.osome} out={repr i.out |>.pretty 200 |>.take 200}"
      nroot := nroot + 1
  for (t, as) in termRootsT do
    let i := s.tab.getD (t, as) {}
    if !i.osome then
      IO.println s!"ROOT term {t} osome=false"
      nroot := nroot + 1
  let bad := (tab.filter fun e => !chkEntry p tab aextTF actorT aidata handRulesT e).length
  IO.println s!"prgTabTF: chkEntry failures: {bad} of {tab.length}, root failures {nroot}"
  let (ftab0, _) ← gen f64Roots (fun _ => none)
  let ftab := ftab0.filter fun e => !(e.1 == TId.constant_f64 && PA.leL e.2.1 [f64Hi])
  let fbad := (ftab.filter fun e => !chkEntry p ftab aextTF actorT aidata (fun _ => none) e).length
  IO.println s!"f64Tab under aextTF: chkEntry failures: {fbad} of {ftab.length}"
  let mut out := header (imp := "FV.Backend.Proof.IselPrgRootTF\nimport FV.Backend.Proof.IselPrgTabF64")
    "# Progress of the ISLE lowering over the float scope: the summary table (S11f, #35)

`prgTabTF`: the summary table of the float scope (`IselPrgRootTF`), closed under the calls of the
statement roots `stmtFormsTF` and the terminator roots `termRootsT`, with the hand-checked rules
`handRulesT` and the extractors `aextTF` (`def_inst` may find a float operation). `prgTabTF_ok`:
every entry checks (`chkTab`); `stmtRootsTF_ok`, `termRootsTF_ok`: every root has an entry that
surely returns a value within the interpreter's fuel. `f64TabF_ok`: the `f64const` sub-table
`f64Tab` also checks under `aextTF`."
  out := out ++ tabSrc "prgTabTF" "handRulesT" tab "aextTF"
  out := out ++ "\n/-- The root entry of a statement form of the float scope. -/\ndef stmtRootOkTF (F : PA) : Bool :=\n  match tabFind prgTabTF TId.lower [F] with\n  | some e => e.osome && PA.le e.out (stmtOut F) && decide (e.fu ≤ 1000000)\n  | none => false\n"
  out := out ++ "\n/-- The root entry of a terminator of the float scope. -/\ndef termRootOkTF (q : TermId × List PA) : Bool :=\n  match tabFind prgTabTF q.1 q.2 with\n  | some e => e.osome && decide (e.fu ≤ 1000000)\n  | none => false\n"
  out := out ++ "\n/-- **Every statement root of the float scope checks.** -/\ntheorem stmtRootsTF_ok : stmtFormsTF.all stmtRootOkTF = true := by\n  decide +kernel\n"
  out := out ++ "\n/-- **Every terminator root checks in the float scope's table.** -/\ntheorem termRootsTF_ok : termRootsT.all termRootOkTF = true := by\n  decide +kernel\n"
  let nch := (ftab.length + 39) / 40
  out := out ++ "\n/-- `chkTab`'s test of one `f64Tab` entry under `aextTF`. -/\nabbrev f64TabFEntryOk (e : PEnt) : Bool :=\n  chkEntry program f64Tab aextTF actorT aidata (fun _ => none) e\n"
  for c in [0:nch] do
    out := out ++ s!"\ntheorem f64TabF{c}_ok : (f64Tab{c}).all f64TabFEntryOk = true := by\n  simp only [f64Tab{c}, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]\n  repeat' apply And.intro\n  all_goals decide +kernel\n"
  out := out ++ "\n/-- **`f64Tab` checks under `aextTF`.** -/\ntheorem f64TabF_ok : chkTab program f64Tab aextTF actorT aidata (fun _ => none) = true := by\n  unfold chkTab\n  show (f64Tab).all f64TabFEntryOk = true\n  simp only [f64Tab, List.all_append, " ++ ", ".intercalate ((List.range nch).map fun c => s!"f64TabF{c}_ok") ++ ", Bool.and_self]\n"
  out := out ++ "\nend Backend.Proof.Prg\n"
  IO.FS.writeFile path (Gen.moduleHeader out)
  IO.println s!"wrote {path}: {tab.length} entries"

open PrgGenT in
def main (args : List String) : IO Unit := do
  if let ["--tf", path] := args then return ← mainTF path
  let p := program
  -- the main table
  let (tab, s) ← gen ((stmtFormsT.map fun F => (TId.lower, [F])) ++ termRootsT) handRulesT
  let mut nroot := 0
  for F in stmtFormsT do
    let i := s.tab.getD (TId.lower, [F]) {}
    if !i.osome || !PA.le i.out (stmtOut F) then
      IO.println s!"ROOT stmt osome={i.osome} out={repr i.out |>.pretty 200 |>.take 200}"
      nroot := nroot + 1
  for (t, as) in termRootsT do
    let i := s.tab.getD (t, as) {}
    if !i.osome then
      IO.println s!"ROOT term {t} osome=false"
      nroot := nroot + 1
  let bad := (tab.filter fun e => !chkEntry p tab aextT actorT aidata handRulesT e).length
  IO.println s!"prgTabT: chkEntry failures: {bad} of {tab.length}, root failures {nroot}"
  -- the `f64const` sub-table
  let (ftab0, _) ← gen f64Roots (fun _ => none)
  let ftab := ftab0.filter fun e => !(e.1 == TId.constant_f64 && PA.leL e.2.1 [f64Hi])
  let fbad := (ftab.filter fun e => !chkEntry p ftab aextT actorT aidata (fun _ => none) e).length
  IO.println s!"f64Tab: chkEntry failures: {fbad} of {ftab.length}"
  match args with
  | [path, fpath] =>
    let mut out := header "# Progress of the ISLE lowering over the typed scope: the summary table

`prgTabT`: per entry an internal term, abstract inputs, abstract output, whether it surely returns
a value, and its fuel; closed under the calls of the statement roots `stmtFormsT` and the
terminator roots `termRootsT`, with the hand-checked rules `handRulesT`. `prgTabT_ok`: every
entry checks (`chkTab`); `stmtRootsT_ok`, `termRootsT_ok`: every root has an entry that surely
returns a value (for a statement, one single register per ABI result: `stmtOut`) within the
interpreter's fuel. All are decided once over the exported rule data, leaf by leaf."
    out := out ++ tabSrc "prgTabT" "handRulesT" tab
    out := out ++ "\n/-- The root entry of a statement form: surely a value, one single register per ABI result,
within the interpreter's fuel. -/\ndef stmtRootOkT (F : PA) : Bool :=\n  match tabFind prgTabT TId.lower [F] with\n  | some e => e.osome && PA.le e.out (stmtOut F) && decide (e.fu ≤ 1000000)\n  | none => false\n"
    out := out ++ "\n/-- The root entry of a terminator: surely a value within the interpreter's fuel. -/\ndef termRootOkT (q : TermId × List PA) : Bool :=\n  match tabFind prgTabT q.1 q.2 with\n  | some e => e.osome && decide (e.fu ≤ 1000000)\n  | none => false\n"
    out := out ++ "\n/-- **Every statement root checks.** -/\ntheorem stmtRootsT_ok : stmtFormsT.all stmtRootOkT = true := by\n  decide +kernel\n"
    out := out ++ "\n/-- **Every terminator root checks.** -/\ntheorem termRootsT_ok : termRootsT.all termRootOkT = true := by\n  decide +kernel\n"
    out := out ++ "\nend Backend.Proof.Prg\n"
    IO.FS.writeFile path (Gen.moduleHeader out)
    IO.println s!"wrote {path}: {tab.length} entries"
    let mut fout := header "# Progress of the ISLE lowering over the typed scope: the `f64const` sub-table

`f64Tab`: the summary table of the terms the hand-checked `f64const` rule (`handRulesT`) calls,
from the roots `f64Roots` without the entry of `constant_f64` on `f64Hi` (whose last rule needs the
literal pool), and without hand-checked rules. `f64Tab_ok`: every entry checks (`chkTab`)."
    fout := fout ++ tabSrc "f64Tab" "(fun _ => none)" ftab
    fout := fout ++ "\nend Backend.Proof.Prg\n"
    IO.FS.writeFile fpath (Gen.moduleHeader fout)
    IO.println s!"wrote {fpath}: {ftab.length} entries"
  | _ => pure ()

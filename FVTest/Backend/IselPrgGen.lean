import FV.Backend.Proof.IselPrgRoot

/-!
# Generator of the V7 progress summary table (`FV/Backend/Proof/IselPrgTab.lean`)

Untrusted: computes, by a fixpoint of the abstract interpreter of `IselPrgCheck` (mirrored here
with on-demand table entries), a summary table for every internal term reachable from the
statement roots (`stmtForms`) and the terminator roots (`termRoots`), checks it with the real
`chkEntry` (reporting every failing entry with the reason), and writes `IselPrgTab.lean`: the
table as Lean literals and the leaf-wise `decide +kernel` checks the proofs rely on.

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselPrgRoot`):

    lake env lean --run FVTest/Backend/IselPrgGen.lean FV/Backend/Proof/IselPrgTab.lean

Without an output path it only reports.
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.Prg

deriving instance BEq for Backend.Proof.Prg.PA
deriving instance Hashable for Backend.Proof.Prg.PA

namespace PrgGen

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
      pure <| match actor term.id as with
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
      match aPat program aext aidata a il.lhs env with
      | none => pure none
      | some (envs, m2) =>
        let mut rs := []
        for e in envs do
          match ← gIfLets ils e with
          | none => return none
          | some r => rs := rs ++ [r]
        pure (some (rs.flatMap (·.1), m1 && m2 && rs.all (·.2.1), 1 + max c1 (maxCost (rs.map (·.2.2)))))

def gRule (ins : List PA) (r : Rule) : StateM St (Option (List AEnv × Bool × Nat)) := do
  match aPatArgs program aext aidata ins r.args (List.replicate r.vars.length none) with
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
        let mustR := mustRule program (← get).snap aext actor aidata ins r
        match ← gRule ins r with
        | none => errs := errs ++ [s!"match of rule {r.id} ({r.name}) may throw"]; cs := cs ++ [(1, 1)]
        | some (envs, _, ilc) =>
          if let some (hc, ha) := handRules r.id then
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
      let exh := exhaustive program s.snap aext actor aidata reached ins
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

end PrgGen


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

def header : String := "import FV.Backend.Proof.IselPrgRoot

/-!
# Progress of the ISLE lowering (V7): the summary table

GENERATED by `FVTest/Backend/IselPrgGen.lean` (untrusted; regenerate with
`lake env lean --run FVTest/Backend/IselPrgGen.lean FV/Backend/Proof/IselPrgTab.lean`).
Do not edit by hand.

`prgTab`: per entry an internal term, abstract inputs, abstract output, whether it surely returns
a value, and its fuel; closed under the calls of the statement roots `stmtForms` and the
terminator roots `termRoots`. `prgTab_ok`: every entry checks (`chkTab`); `stmtRoots_ok`,
`termRoots_ok`: every root has an entry that surely returns a value (for a statement, one
single register per ABI result: `stmtOut`) within the interpreter's fuel. All are decided once
over the exported rule data, leaf by leaf.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64
"

open PrgGen in
def main (args : List String) : IO Unit := do
  let p := program
  let roots : List Key := (stmtForms.map fun F => (TId.lower, [F])) ++ termRoots
  let mut s : St := {}
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
    let rr := reach p tab aext actor aidata k.2 (p.rulesOf k.1)
    IO.println s!"DIAG {showK k} osome={i.osome} exh={exhaustive p tab aext actor aidata rr k.2}"
    for r in rr do
      match aRule p tab aext actor aidata k.2 r with
      | none => IO.println s!"   rule {r.id} {r.name}: match may throw"
      | some (envs, m, _) =>
        if !envs.isEmpty then
          let rs := envs.map fun env => match aExpr p tab actor r.rhs env with
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
  -- roots: osome and output
  let mut nroot := 0
  for F in stmtForms do
    let i := s.tab.getD (TId.lower, [F]) {}
    if !i.osome || !PA.le i.out (stmtOut F) then
      IO.println s!"ROOT stmt osome={i.osome} out={repr i.out |>.pretty 200 |>.take 200}"
      if nroot < 200 then diag (TId.lower, [F])
      nroot := nroot + 1
  for (t, as) in termRoots do
    let i := s.tab.getD (t, as) {}
    if !i.osome then
      IO.println s!"ROOT term {t} osome=false"
      if nroot < 220 then diag (t, as)
      nroot := nroot + 1
  let maxFu := (s.order.toList.map fun k => (s.tab.getD k {}).fu).foldl max 0
  IO.println s!"max fuel {maxFu}"
  -- the real check
  let mut bad := 0
  for e in tab do
    if !chkEntry p tab aext actor aidata handRules e then bad := bad + 1
  IO.println s!"chkEntry failures: {bad} of {tab.length}"
  -- write the table
  match args with
  | [path] =>
    let chunk := 40
    let ents := tab.toArray
    let nch := (ents.size + chunk - 1) / chunk
    let mut out := header
    for c in [0:nch] do
      let es := (ents.extract (c * chunk) ((c + 1) * chunk)).toList
      out := out ++ s!"\n/-- Chunk {c} of the table. -/\ndef prgTab{c} : PTab := [\n" ++ ",\n".intercalate (es.map entS) ++ "]\n"
    out := out ++ "\n/-- **The summary table.** -/\ndef prgTab : PTab :=\n  " ++ " ++ ".intercalate ((List.range nch).map fun c => s!"prgTab{c}") ++ "\n"
    out := out ++ "\n/-- `chkTab`'s test of one entry. -/\nabbrev prgEntryOk (e : PEnt) : Bool :=\n  chkEntry program prgTab aext actor aidata handRules e\n"
    for c in [0:nch] do
      out := out ++ s!"\ntheorem prgTab{c}_ok : (prgTab{c}).all prgEntryOk = true := by\n  simp only [prgTab{c}, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]\n  repeat' apply And.intro\n  all_goals decide +kernel\n"
    out := out ++ "\n/-- **Every entry checks.** -/\ntheorem prgTab_ok : chkTab program prgTab aext actor aidata handRules = true := by\n  unfold chkTab\n  show (prgTab).all prgEntryOk = true\n  simp only [prgTab, List.all_append, " ++ ", ".intercalate ((List.range nch).map fun c => s!"prgTab{c}_ok") ++ ", Bool.and_self]\n"
    out := out ++ "\n/-- The root entry of a statement form: surely a value, one single register per ABI result,
within the interpreter's fuel. -/\ndef stmtRootOk (F : PA) : Bool :=\n  match tabFind prgTab TId.lower [F] with\n  | some e => e.osome && PA.le e.out (stmtOut F) && decide (e.fu ≤ 1000000)\n  | none => false\n"
    out := out ++ "\n/-- The root entry of a terminator: surely a value within the interpreter's fuel. -/\ndef termRootOk (q : TermId × List PA) : Bool :=\n  match tabFind prgTab q.1 q.2 with\n  | some e => e.osome && decide (e.fu ≤ 1000000)\n  | none => false\n"
    out := out ++ "\n/-- **Every statement root checks.** -/\ntheorem stmtRoots_ok : stmtForms.all stmtRootOk = true := by\n  decide +kernel\n"
    out := out ++ "\n/-- **Every terminator root checks.** -/\ntheorem termRoots_ok : termRoots.all termRootOk = true := by\n  decide +kernel\n"
    out := out ++ "\nend Backend.Proof.Prg\n"
    IO.FS.writeFile path out
    IO.println s!"wrote {path}: {ents.size} entries in {nch} chunks"
  | _ => pure ()

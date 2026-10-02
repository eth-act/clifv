import FV.Clif
import FV.Opt.Legalize128Pass
import Lean.Data.Json

/-!
# `clif-filetest`: run Cranelift `.clif` runtests through `Clif.run`

```
clif-filetest [-v] [--oracle-dir DIR | --oracle FILE.json] [--print-dir DIR] FILE.clif...
```
With `--print-dir`, the printed program of each file's supported functions is written to
`DIR/<file name>` (for `clif-oracle check`).

Per file:
1. `Clif.parseFile`; functions outside subset S are `unsupported` (with the reason).
2. Round trip: `parse (print p) = p` for the program of the supported functions.
3. Every `; run` line of a supported function whose program callees are all supported is
   run with `Clif.run` (empty `Env`, the file's `; data:` objects, fuel `1_000_000`) and compared with its expectation.
4. With an oracle file (JSON lines from `clif-oracle interp`, schema in
   `docs/contracts/clif.md`), each run is also compared with the Cranelift interpreter.

Prints one line per file and a `TOTAL` line; exit status 1 iff something failed or
disagreed.
-/

open Clif Lean

namespace ClifFiletest

def fuel : Nat := 1000000

def hexBits (v : Val) : String :=
  let digits := v.ty.width / 4
  let h := String.ofList (Nat.toDigits 16 v.toNat)
  "0x" ++ String.ofList (List.replicate (digits - h.length) '0') ++ h

def showVal (v : Val) : String := s!"{v.toInt}:{v.ty.name}"

def showVals (vs : List Val) : String := "[" ++ ", ".intercalate (vs.map showVal) ++ "]"

def showOutcome : Outcome → String
  | .returned vs _ => s!"returned {showVals vs}"
  | .trapped c => s!"trapped {c.name}"
  | .stuck m => s!"stuck ({m})"
  | .outOfFuel => "out of fuel"

def showRun (r : RunCommand) : String :=
  let inv := s!"%{r.func}({", ".intercalate (r.args.map showVal)})"
  match r.expect with
  | .eq vs => s!"{inv} == {showVals vs}"
  | .ne vs => s!"{inv} != {showVals vs}"
  | .nonzero => s!"{inv} != 0"
  | .print => s!"print {inv}"

/-- Does the outcome satisfy the run command's expectation? A `print` command has no
expectation (any outcome, including an aborting call, is a pass). -/
def check (r : RunCommand) (o : Outcome) : Bool :=
  match r.expect with
  | .print => true
  | .eq e =>
    match o with
    | .returned vs _ => vs == e
    | _ => false
  | .ne e =>
    match o with
    | .returned vs _ => vs != e
    | _ => false
  | .nonzero =>
    match o with
    | .returned vs _ =>
      match vs with
      | [v] => v.toNat != 0
      | _ => false
    | _ => false

/-! ## Oracle records -/

inductive OracleActual where
  | returned (vals : List (String × Nat))
  | trapped (code : String)
  | error (msg : String)

structure OracleRecord where
  attached : String
  func : String
  actual : OracleActual

def parseBits (s : String) : Option Nat :=
  match s.toList with
  | '0' :: 'x' :: hs =>
    hs.foldlM (init := 0) fun acc h =>
      if h.isDigit then some (acc * 16 + (h.toNat - '0'.toNat))
      else if 'a' ≤ h ∧ h ≤ 'f' then some (acc * 16 + (h.toNat - 'a'.toNat + 10))
      else if 'A' ≤ h ∧ h ≤ 'F' then some (acc * 16 + (h.toNat - 'A'.toNat + 10))
      else none
  | _ => none

def parseValue (j : Json) : Except String (String × Nat) := do
  let ty ← j.getObjValAs? String "ty"
  let bits ← j.getObjValAs? String "bits"
  match parseBits bits with
  | some n => return (ty, n)
  | none => throw s!"bad bits {bits}"

def parseRecord (j : Json) : Except String OracleRecord := do
  let attached ← j.getObjValAs? String "attached"
  let func ← j.getObjValAs? String "func"
  let act ← j.getObjVal? "actual"
  let actual ←
    match act.getObjVal? "returned" with
    | .ok (.arr vs) => pure (.returned (← vs.toList.mapM parseValue))
    | _ =>
      match act.getObjValAs? String "trapped" with
      | .ok c => pure (.trapped c)
      | _ => pure (.error ((act.getObjValAs? String "error").toOption.getD "?"))
  return { attached, func, actual }

def loadOracle (path : System.FilePath) : IO (Except String (List OracleRecord)) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Json.parse line with
    | .error e => return .error s!"{path}: {e}"
    | .ok j =>
      if let .ok e := j.getObjValAs? String "file_error" then
        return .error s!"oracle could not read the file: {e}"
      match parseRecord j with
      | .ok r => out := out.push r
      | .error e => return .error s!"{path}: {e}"
  return .ok out.toList

/-- Agreement of our outcome with the interpreter's. `none`: the oracle reported an error
(no comparison possible). -/
def agree (o : Outcome) (a : OracleActual) : Option Bool :=
  match o, a with
  | .returned vs _, .returned ws => some (vs.map (fun v => (v.ty.name, v.toNat)) == ws)
  | .trapped c, .trapped d => some (c.name == d)
  | _, .error _ => none
  | _, _ => some false

/-! ## Per-file driver -/

structure Counts where
  pass : Nat := 0
  fail : Nat := 0
  unsupported : Nat := 0
  roundtripFail : Nat := 0
  agree : Nat := 0
  disagree : Nat := 0
  /-- Disagreements in files the upstream suite interprets (`test interpret` header). -/
  disagreeInterp : Nat := 0
  oracleError : Nat := 0
  /-- `--legalize128`: the legalised function passes the original run line. -/
  legalPass : Nat := 0
  /-- `--legalize128`: the legalised function does not pass the original run line. -/
  legalFail : Nat := 0
  /-- `--legalize128`: original and legalised outcomes agree. -/
  legalAgree : Nat := 0
  /-- `--legalize128`: they disagree. -/
  legalDisagree : Nat := 0

def Counts.add (a b : Counts) : Counts :=
  { pass := a.pass + b.pass, fail := a.fail + b.fail,
    unsupported := a.unsupported + b.unsupported,
    roundtripFail := a.roundtripFail + b.roundtripFail,
    agree := a.agree + b.agree, disagree := a.disagree + b.disagree,
    disagreeInterp := a.disagreeInterp + b.disagreeInterp,
    oracleError := a.oracleError + b.oracleError,
    legalPass := a.legalPass + b.legalPass, legalFail := a.legalFail + b.legalFail,
    legalAgree := a.legalAgree + b.legalAgree,
    legalDisagree := a.legalDisagree + b.legalDisagree }

/-- Names of program functions a function calls. -/
def callees (f : Function) : List String := f.externs.map (·.2.name)

/-- Does the filetest treat the extern `name` as available? `rustEnv`: the trusted Rust
contracts (`Clif.Rust.env`) provide the mem* functions, the `__*ti3` 128-bit division
helpers, and every diverging panic entry. -/
def extAvailable (rustEnv : Bool) (name : String) : Bool :=
  (rustEnv && (Clif.Rust.isPanic name || name == "memcpy" || name == "memset" ||
    name == "memmove" || name == "memcmp" || Clif.Rust.isDivHelper name))

/-- Supported functions whose transitive in-file callees are all supported; the others get
a reason. -/
def closure (rustEnv : Bool) (pf : ParsedFile) : List (String × Except String Function) :=
  let direct : List (String × Except String Function) := pf.funcs.map fun f =>
    (f.name, match f.func with
      | .ok fn => .ok fn
      | .error e => .error (toString e))
  let bad0 : List (String × String) :=
    direct.filterMap fun (n, r) => match r with
      | .error e => some (n, e)
      | .ok _ => none
  let names := pf.funcs.map (·.name)
  let step (bad : List (String × String)) : List (String × String) :=
    bad ++ direct.filterMap fun (n, r) =>
      match r with
      | .ok fn =>
        if (bad.lookup n).isSome then none else
        match (callees fn).find? (fun c => (bad.lookup c).isSome) with
        | some c => some (n, s!"calls %{c}, which is unsupported")
        | none =>
          match (callees fn).find? (fun c => !names.contains c && !extAvailable rustEnv c) with
          | some c => some (n, s!"calls extern %{c} (not in this file)")
          | none => none
      | .error _ => none
  let bad := (List.range (names.length + 1)).foldl (fun b _ => step b) bad0
  direct.map fun (n, r) =>
    match bad.lookup n, r with
    | some e, _ => (n, .error e)
    | none, r => (n, r)

/-- Do two outcomes agree (both `stuck` for whatever reason counts as agreement)? -/
def sameOutcome : Outcome → Outcome → Bool
  | .returned vs _, .returned ws _ => vs == ws
  | .trapped c, .trapped d => c == d
  | .stuck _, .stuck _ => true
  | .outOfFuel, .outOfFuel => true
  | _, _ => false

def runFile (verbose : Bool) (path : String) (oracle : Option (List OracleRecord))
    (printDir : Option String) (rustEnv : Bool) (legal : Bool) : IO Counts := do
  let src ← IO.FS.readFile path
  let pf := parseFile src
  let mut c : Counts := {}
  let mut notes : Array String := #[]
  let cl := closure rustEnv pf
  -- Program of all parsed functions (callers of unsupported ones are excluded from runs).
  let supported := pf.funcs.filterMap fun f => f.func.toOption
  let data := match pf.data with | .ok ds => ds | .error _ => []
  if let .error e := pf.data then notes := notes.push s!"  data directives: {e}"
  let prog : Program := { header := pf.header, data, funcs := supported }
  -- The legalised program (`--legalize128`): every legalisable function rewritten to
  -- plain i8..i64 CLIF (`Opt.Legalize128`), the others unchanged.
  let legalProg : Program :=
    { prog with funcs := prog.funcs.map fun f =>
      match Opt.Legalize128.function128 f with | .ok f' => f' | .error _ => f }
  -- Printed program, for checking with `clif-oracle check`.
  if let some d := printDir then
    if !prog.funcs.isEmpty then
      IO.FS.writeFile (System.FilePath.mk d / ((System.FilePath.mk path).fileName.getD path))
        (print prog)
  -- Round trip.
  match parse (print prog) with
  | .ok p' =>
    if p' != prog then
      c := { c with roundtripFail := c.roundtripFail + 1 }
      notes := notes.push "  round trip: parse (print p) ≠ p"
  | .error e =>
    c := { c with roundtripFail := c.roundtripFail + 1 }
    notes := notes.push s!"  round trip: printed text does not parse: {e}"
  -- Oracle records grouped by attached function.
  let orc := oracle.getD []
  for pfn in pf.funcs do
    let recs := orc.filter (·.attached == pfn.name)
    match cl.lookup pfn.name with
    | some (.ok fn) =>
      let mut i := 0
      for r in fn.runs do
        let o := run (if rustEnv then Clif.Rust.env else {}) prog r.func r.args fuel
        let ok := check r o
        if ok then c := { c with pass := c.pass + 1 }
        else
          c := { c with fail := c.fail + 1 }
          notes := notes.push s!"  FAIL {showRun r}: {showOutcome o}"
        if oracle.isSome then
          match recs[i]? with
          | some rec =>
            match agree o rec.actual with
            | some true => c := { c with agree := c.agree + 1 }
            | some false =>
              c := { c with disagree := c.disagree + 1 }
              notes := notes.push s!"  DISAGREE {showRun r}: ours {showOutcome o}"
            | none =>
              c := { c with oracleError := c.oracleError + 1 }
              if verbose then
                let msg := match rec.actual with | .error m => m | _ => ""
                notes := notes.push s!"  oracle error {showRun r}: {msg}"
          | none =>
            c := { c with disagree := c.disagree + 1 }
            notes := notes.push s!"  DISAGREE {showRun r}: no oracle record"
        -- `--legalize128`: run the legalised function on the same line — with the trusted
        -- Rust env, which provides the `__*ti3` helpers — and require it to pass the
        -- original expectation and to agree with the original function's outcome.
        if legal && Opt.Legalize128.mentions128 fn then
          match Opt.Legalize128.function128 fn with
          | .ok f' =>
            if f' != fn then
              match Opt.Legalize128.expandRunArgs fn.sig r.args with
              | .ok args' =>
                let oL := run Clif.Rust.env legalProg r.func args' fuel
                let mapped := Opt.Legalize128.joinRunOutcome fn.sig oL
                if check r mapped then c := { c with legalPass := c.legalPass + 1 }
                else
                  c := { c with legalFail := c.legalFail + 1 }
                  notes := notes.push s!"  LEGAL-FAIL {showRun r}: {showOutcome mapped}"
                let oO := run Clif.Rust.env prog r.func r.args fuel
                if sameOutcome oO mapped then c := { c with legalAgree := c.legalAgree + 1 }
                else
                  c := { c with legalDisagree := c.legalDisagree + 1 }
                  notes := notes.push s!"  LEGAL-DISAGREE {showRun r}: original {showOutcome oO}, legalised {showOutcome mapped}"
              | .error e =>
                c := { c with legalFail := c.legalFail + 1 }
                notes := notes.push s!"  LEGAL-ARG {showRun r}: {e}"
          | .error _ => pure ()  -- the function is not legalisable: outside the claim
        i := i + 1
    | some (.error e) =>
      c := { c with unsupported := c.unsupported + pfn.runLines }
      if pfn.runLines > 0 && verbose then
        notes := notes.push s!"  unsupported %{pfn.name} ({pfn.runLines} runs): {e}"
    | none => pure ()
  if pf.header.contains "test interpret" then c := { c with disagreeInterp := c.disagree }
  let oracleText := if oracle.isSome then
      s!" agree {c.agree} disagree {c.disagree} oracle-error {c.oracleError}" else ""
  let legalText := if legal then
      s!" | legal pass {c.legalPass} fail {c.legalFail} agree {c.legalAgree} disagree {c.legalDisagree}"
      else ""
  IO.println s!"{path}: pass {c.pass} fail {c.fail} unsupported {c.unsupported}{oracleText}{legalText}{if c.roundtripFail > 0 then " ROUNDTRIP-FAIL" else ""}"
  for n in notes do IO.println n
  return c

def usage : String :=
  "usage: clif-filetest [-v] [--oracle-dir DIR | --oracle FILE.json] [--print-dir DIR] [--rust-env] [--legalize128] FILE.clif..."

end ClifFiletest

open ClifFiletest in
def main (args : List String) : IO UInt32 := do
  let mut verbose := false
  let mut oracleDir : Option String := none
  let mut oracleFile : Option String := none
  let mut printDir : Option String := none
  let mut rustEnv := false
  let mut legal := false
  let mut files := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "-v" :: r => verbose := true; rest := r
    | "--oracle-dir" :: d :: r => oracleDir := some d; rest := r
    | "--oracle" :: f :: r => oracleFile := some f; rest := r
    | "--print-dir" :: d :: r => printDir := some d; rest := r
    | "--rust-env" :: r => rustEnv := true; rest := r
    | "--legalize128" :: r => legal := true; rest := r
    | f :: r => files := files.push f; rest := r
    | [] => pure ()
  if files.isEmpty then
    IO.eprintln usage
    return 2
  let mut total : Counts := {}
  let mut filesWithUnsupported := 0
  let mut badOracle := 0
  for f in files do
    let oraclePath : Option System.FilePath :=
      match oracleFile, oracleDir with
      | some o, _ => some o
      | none, some d =>
        some (System.FilePath.mk d / ((System.FilePath.mk f).fileName.getD f ++ ".json"))
      | none, none => none
    let oracle ← match oraclePath with
      | none => pure none
      | some p =>
        if ← p.pathExists then
          match ← loadOracle p with
          | .ok recs => pure (some recs)
          | .error e =>
            IO.println s!"{f}: oracle unavailable: {e}"
            badOracle := badOracle + 1
            pure none
        else
          IO.println s!"{f}: oracle file {p} missing"
          badOracle := badOracle + 1
          pure none
    let c ← runFile verbose f oracle printDir rustEnv legal
    if c.unsupported > 0 then filesWithUnsupported := filesWithUnsupported + 1
    total := total.add c
  let legalTotal := if legal then
      s!" legal pass {total.legalPass} fail {total.legalFail} agree {total.legalAgree} disagree {total.legalDisagree}" else ""
  IO.println s!"TOTAL files {files.size}: pass {total.pass} fail {total.fail} unsupported {total.unsupported} (in {filesWithUnsupported} files) roundtrip-fail {total.roundtripFail} agree {total.agree} disagree {total.disagree} (in `test interpret` files: {total.disagreeInterp}) oracle-error {total.oracleError} oracle-unavailable {badOracle}{legalTotal}"
  return if total.fail + total.disagree + total.roundtripFail + total.legalFail + total.legalDisagree > 0 then 1 else 0

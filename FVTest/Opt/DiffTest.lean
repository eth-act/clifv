import FVTest.Opt.Common
import FV.Clif.Run

/-!
`opt-difftest [-v] [--rules-stats] [--opt-* options] FILE.clif...`: differential test of the
mid-end against `Clif.run` (`docs/contracts/midend.md`).

For each file, the program `p` of the functions `Clif.parseFile` supports (and the file's
`; data:` objects) is optimised function by function (`p'`). Every `; run:` line is run with
`Clif.run` (empty `Env`) on `p` (fuel 10⁶) and on `p'` (fuel 2·10⁶), and the outcomes are
compared with the refinement the mid-end must satisfy:

* `p` returns `vs` ⇒ `p'` returns `vs`;  `p` traps with `c` ⇒ `p'` traps with `c`
  (`agree`, otherwise `FAIL`);
* `p` is stuck or out of fuel ⇒ no obligation (`noclaim`; `-v` shows whether `p'` differs).

Per file: a line if anything failed (every file with `-v`). Then a `TOTAL` line with run
counts, function counts (optimised / ill-formed input / pass errors) and the static
instruction counts before and after. `--rules-stats` adds how often each rule fired.
Exit status 1 iff a run failed or a pass produced an ill-formed function.
-/

open Clif Opt

namespace OptDiffTest

def showVal (v : Val) : String := s!"{v.toInt}:{v.ty.name}"

def showOutcome : Outcome → String
  | .returned vs _ => "returned [" ++ ", ".intercalate (vs.map showVal) ++ "]"
  | .trapped c => s!"trapped {c.name}"
  | .stuck m => s!"stuck ({m})"
  | .outOfFuel => "out of fuel"

inductive Verdict | agree | fail | noclaim

def compare : Outcome → Outcome → Verdict
  | .returned vs _, .returned ws _ => if vs == ws then .agree else .fail
  | .trapped c, .trapped d => if c == d then .agree else .fail
  | .returned .., _ | .trapped _, _ => .fail
  | _, _ => .noclaim

structure Totals where
  files : Nat := 0
  runs : Nat := 0
  agree : Nat := 0
  fail : Nat := 0
  noclaim : Nat := 0
  noclaimDiffer : Nat := 0
  funcs : Nat := 0
  illFormed : Nat := 0
  passErrors : Nat := 0
  sizeBefore : Nat := 0
  sizeAfter : Nat := 0
  rewritten : Nat := 0
  gvn : Nat := 0
  dce : Nat := 0
  licm : Nat := 0
  ruleErrors : Nat := 0
  fired : Std.HashMap String Nat := {}

def sameOutcome : Outcome → Outcome → Bool
  | .returned vs _, .returned ws _ => vs == ws
  | .trapped c, .trapped d => c == d
  | .stuck _, .stuck _ | .outOfFuel, .outOfFuel => true
  | _, _ => false

def runFile (verbose : Bool) (cfg : Config) (path : String) (t : Totals) : IO Totals := do
  let pf := parseFile (← IO.FS.readFile path)
  let funcs := pf.funcs.filterMap (·.func.toOption)
  let data := match pf.data with | .ok ds => ds | .error _ => []
  let p : Program := { header := pf.header, data, funcs }
  let mut t := { t with files := t.files + 1 }
  let mut notes : Array String := #[]
  let mut opt : Array Function := #[]
  for f in funcs do
    let (g, r) := optimizeReport cfg f
    opt := opt.push g
    t := { t with funcs := t.funcs + 1, sizeBefore := t.sizeBefore + r.sizeBefore,
                  sizeAfter := t.sizeAfter + r.sizeAfter, rewritten := t.rewritten + r.rewritten,
                  gvn := t.gvn + r.gvnRemoved, dce := t.dce + r.dceRemoved, licm := t.licm + r.hoisted,
                  ruleErrors := t.ruleErrors + r.ruleErrors,
                  fired := r.fired.fold (fun m k n => m.insert k ((m.get? k).getD 0 + n)) t.fired }
    if let some e := r.illFormed then
      t := { t with illFormed := t.illFormed + 1 }
      if verbose then notes := notes.push s!"  %{f.name}: not optimised: {e}"
    if let some (pass, e) := r.passError then
      t := { t with passErrors := t.passErrors + 1 }
      notes := notes.push s!"  PASS ERROR %{f.name} after {pass}: {e}"
  let p' : Program := { p with funcs := opt.toList }
  let mut fails := 0
  for f in funcs do
    for rc in f.runs do
      let o := run {} p rc.func rc.args 1000000
      let o' := run {} p' rc.func rc.args 2000000
      t := { t with runs := t.runs + 1 }
      let desc := s!"%{rc.func}({", ".intercalate (rc.args.map showVal)})"
      match compare o o' with
      | .agree => t := { t with agree := t.agree + 1 }
      | .fail =>
        t := { t with fail := t.fail + 1 }
        fails := fails + 1
        notes := notes.push s!"  FAIL {desc}: before {showOutcome o}, after {showOutcome o'}"
      | .noclaim =>
        t := { t with noclaim := t.noclaim + 1 }
        if !sameOutcome o o' then
          t := { t with noclaimDiffer := t.noclaimDiffer + 1 }
          if verbose then
            notes := notes.push s!"  noclaim {desc}: before {showOutcome o}, after {showOutcome o'}"
  if verbose || !notes.isEmpty then
    IO.println s!"{path}: functions {funcs.length}, fail {fails}"
    for n in notes do IO.println n
  return t

end OptDiffTest

open OptDiffTest in
def main (args : List String) : IO UInt32 := do
  let ((cfg : Option Config), rest) ← match parseOptArgs args with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"opt-difftest: {e}"; return 2
  let cfg := cfg.getD {}
  let verbose := rest.contains "-v"
  let ruleStats := rest.contains "--rules-stats"
  let files := rest.filter fun a => a != "-v" && a != "--rules-stats"
  if files.isEmpty then
    IO.eprintln "usage: opt-difftest [-v] [--rules-stats] [--opt-* options] FILE.clif..."
    return 2
  let mut t : Totals := {}
  for f in files do
    t ← runFile verbose cfg f t
  IO.println s!"TOTAL files {t.files}: runs {t.runs} agree {t.agree} fail {t.fail} noclaim {t.noclaim} (differ {t.noclaimDiffer}) | functions {t.funcs} ill-formed {t.illFormed} pass-errors {t.passErrors} | insts {t.sizeBefore} -> {t.sizeAfter} | rewritten {t.rewritten} gvn {t.gvn} dce {t.dce} licm {t.licm} rule-errors {t.ruleErrors}"
  if ruleStats then
    let rows := t.fired.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
    for (n, k) in rows do IO.println s!"  rule {n}: {k}"
  return if t.fail == 0 && t.passErrors == 0 then 0 else 1

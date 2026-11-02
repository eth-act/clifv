import FV.Clif

/-!
`lake env lean --run scripts/rust-clif/ParseCheck.lean FILE.clif...`: run `Clif.parseFile` on
each file and print one tab-separated line per function: `FILE  NAME  ok|unsupported|malformed
MESSAGE`. Used by `scripts/rust-clif/parse-check.sh` for the cg_clif survey.
-/

def main (args : List String) : IO Unit := do
  for path in args do
    let src ← IO.FS.readFile path
    let pf := Clif.parseFile src
    if pf.funcs.isEmpty then IO.println s!"{path}\t-\tmalformed\tno function"
    for f in pf.funcs do
      let status := match f.func with
        | .ok _ => "ok\t"
        | .error (.unsupported m) => s!"unsupported\t{m}"
        | .error (.malformed m) => s!"malformed\t{m}"
      IO.println s!"{path}\t{f.name}\t{status}"

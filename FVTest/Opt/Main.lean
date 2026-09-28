import FVTest.Opt.Common
import FV.Clif.Print

/-!
`clif-opt [--opt-* options] [--stats] IN.clif [OUT.clif]`: optimise every function of a
`.clif` file with the Lean mid-end (`Opt.optimize`, `docs/contracts/midend.md`) and print the
result (header, `; data:` directives, functions with their `; run:` lines) to `OUT.clif` or
stdout. Functions `Clif.parseFile` does not support are dropped (listed on stderr). With
`--stats`, one line per function on stderr: instruction counts before/after, rewrites, GVN,
DCE and LICM counts, and why a function was left alone.
-/

open Clif Opt

def reportLine (r : Report) : String :=
  let why := match r.illFormed, r.passError with
    | some e, _ => s!" NOT OPTIMISED (ill-formed input: {e})"
    | none, some (p, e) => s!" PASS ERROR after {p}: {e}"
    | none, none => ""
  s!"%{r.name}: {r.sizeBefore} -> {r.sizeAfter} insts, rewritten {r.rewritten}, skeleton {r.skeleton}, gvn {r.gvnRemoved}, dce {r.dceRemoved}, licm {r.hoisted}{if r.ruleErrors > 0 then s!", rule errors {r.ruleErrors}" else ""}{why}"

def main (args : List String) : IO UInt32 := do
  let ((cfg : Option Config), rest) ← match parseOptArgs args with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"clif-opt: {e}"; return 2
  let cfg := cfg.getD {}
  let stats := rest.contains "--stats"
  let files := rest.filter (· != "--stats")
  let (input, output) ← match files with
    | [i] => pure (i, none)
    | [i, o] => pure (i, some o)
    | _ => do
      IO.eprintln "usage: clif-opt [--opt-rules cranelift|hand] [--opt-no-simplify|--opt-no-gvn|--opt-no-dce|--opt-no-licm|--opt-remat-const|--opt-no-hoist-const] [--opt-rounds N] [--stats] IN.clif [OUT.clif]"
      return 2
  let pf := parseFile (← IO.FS.readFile input)
  let mut funcs : Array Function := #[]
  for p in pf.funcs do
    match p.func with
    | .error e => IO.eprintln s!"clif-opt: {input}: %{p.name}: unsupported: {e}"
    | .ok f =>
      let (g, r) := optimizeReport cfg f
      if stats then IO.eprintln (reportLine r)
      funcs := funcs.push g
  let data := match pf.data with | .ok ds => ds | .error _ => []
  let text := Clif.print { header := pf.header, data, funcs := funcs.toList }
  match output with
  | some o => IO.FS.writeFile o text
  | none => IO.print text
  return 0

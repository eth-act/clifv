import FV.Opt
import FV.Clif.Parse

/-!
Shared command-line handling of the mid-end drivers (`clif-opt`, `opt-difftest`, and the
`--opt` flag of `lean-backend`, `lean-backend-armrun`, `lean-e2e-check`).

Options (anywhere on the command line, consumed by `Opt.parseOptArgs`):
`--opt` (enable), `--opt-rules cranelift|hand` (default cranelift), `--opt-no-simplify`, `--opt-no-gvn`,
`--opt-no-dce`, `--opt-no-licm`, `--opt-remat-const`, `--opt-no-hoist-const`, `--opt-rounds N`, `--opt-proven-only`.
Any `--opt-*` option implies `--opt`.
-/

namespace Opt

open Clif

def ruleSet? (name : String) : Option RuleSetId := RuleSetId.all.find? (·.name == name)

/-- Remove the mid-end options from `args`; `none` config if `--opt` is absent. -/
def parseOptArgs (args : List String) : Except String (Option Config × List String) := do
  let mut cfg : Config := {}
  let mut on := false
  let mut rest : Array String := #[]
  let mut xs := args
  for _ in [0:args.length + 1] do
    match xs with
    | [] => break
    | "--opt" :: r => on := true; xs := r
    | "--opt-rules" :: n :: r =>
      let some rs := ruleSet? n | throw s!"unknown rule set {n} (known: {RuleSetId.all.map (·.name)})"
      cfg := { cfg with rules := rs }; on := true; xs := r
    | "--opt-no-simplify" :: r => cfg := { cfg with simplify := false }; on := true; xs := r
    | "--opt-no-gvn" :: r => cfg := { cfg with gvn := false }; on := true; xs := r
    | "--opt-no-dce" :: r => cfg := { cfg with dce := false }; on := true; xs := r
    | "--opt-no-licm" :: r => cfg := { cfg with licm := false }; on := true; xs := r
    | "--opt-proven-only" :: r => cfg := { cfg with ruleAllow := .proven }; on := true; xs := r
    | "--opt-remat-const" :: r => cfg := { cfg with rematConst := true }; on := true; xs := r
    | "--opt-no-hoist-const" :: r => cfg := { cfg with hoistConst := false }; on := true; xs := r
    | "--opt-rounds" :: n :: r =>
      let some k := n.toNat? | throw s!"--opt-rounds: not a number: {n}"
      cfg := { cfg with rounds := k }; on := true; xs := r
    | a :: r => rest := rest.push a; xs := r
  return (if on then some cfg else none, rest.toList)

/-- Optimise every parsed function of a file. -/
def optimizeParsedFile (cfg : Config) (pf : ParsedFile) : ParsedFile :=
  { pf with funcs := pf.funcs.map fun p => { p with func := p.func.map (optimize · cfg) } }

end Opt

import FVTest.Isle.Opt

/-!
# `simplify` against Cranelift on the CLIF corpus

`oracle/opt_corpus.trace` is `isle-trace-oracle --opt` on every `corpus/clif/*.clif` (156
functions). For every `simplify` call Cranelift makes on an original instruction's value whose
operands' e-classes are still single original nodes (each operand is an entry-block parameter,
a non-pure result, or a pure value whose own call returned nothing but itself; parameters of
other blocks may have been replaced by `remove_constant_phis`), the rules that
contributed to the call must equal, as a multiset, the rules of `Isle.Opt.simplify` on the toy
e-graph of the function. Calls on other values (nodes built by rewrites, or with rewritten
operands) depend on the driver and are skipped; the count of compared calls is printed.
-/

namespace Isle.Test.OptCorpus
open Isle Isle.Opt Isle.Test.Opt

/-- `(file, functions)` sections: `file` lines, then the oracle's `function` sections. -/
def files (s : String) : List (String × String) :=
  let parts := (s.splitOn "file ").filter (· ≠ "")
  parts.filterMap fun p =>
    match p.splitOn "\n" with
    | f :: rest => some (f, "\n".intercalate rest)
    | [] => none

/-- `simplify vN: rules -> [results]` lines as `(N, rules, results)`. -/
def calls (ls : List String) : List (Nat × List String × List Nat) :=
  ls.filterMap fun l =>
    if !l.startsWith "simplify v" then none else
    match (l.drop 9).toString.splitOn ": " with
    | [v, rest] =>
      match (v.drop 1).toString.toNat?, rest.splitOn " -> " with
      | some n, [rules, res] =>
        let res := ((res.replace "[" "").replace "]" "").splitOn ", " |>.filterMap
          fun r => (r.trimAscii.toString.drop 1).toString.toNat?
        some (n, (rules.splitOn " ").filter (· ≠ ""), res)
      | _, _ => none
    | _ => none

/-- Operands of a node. -/
def operands : Clif.Inst → List Nat
  | .unary _ _ x | .bmask _ x | .extend _ _ x | .ireduce _ x => [x]
  | .binary _ _ x y | .icmp _ _ x y | .iconcat _ x y => [x, y]
  | .select _ c x y | .selectSpectreGuard _ c x y | .bitselect _ c x y => [c, x, y]
  | _ => []

def check : IO Unit := do
  let mut compared := 0
  let mut skipped := 0
  for (file, trace) in files (← IO.FS.readFile "FVTest/Isle/oracle/opt_corpus.trace") do
    let prog ← match Clif.parse (← IO.FS.readFile file) with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"{file}: {e}")
    let oracle := sections trace
    for f in prog.funcs do
      let some ls := oracle.lookup s!"%{f.name}"
        | throw (IO.userError s!"{file} %{f.name}: not in oracle output")
      let cs := calls ls
      let (g, _) := graphOf f
      let pureVals := (List.range g.nodes.size).filter fun v => !(Toy.enodes g v).isEmpty
      -- Parameters of non-entry blocks may be replaced before the e-graph pass
      -- (`remove_constant_phis`). A pure original value is clean if Cranelift called
      -- `simplify` on it and got nothing but itself back.
      let laterParams := (f.blocks.drop 1).flatMap fun b => b.params.map (·.1)
      let clean (v : Nat) : Bool :=
        !laterParams.contains v &&
        (!pureVals.contains v || cs.any fun (w, _, res) => w == v && res.all (· == v))
      for v in pureVals do
        let some (_, expected, _) := cs.find? (·.1 == v) | continue
        let ok := (Toy.enodes g v).all fun i => (operands i).all clean
        if !ok then
          skipped := skipped + 1
          continue
        match Toy.run g v with
        | .error e => throw (IO.userError s!"{file} %{f.name} v{v}: {e}")
        | .ok (_, names, _) =>
          let got := names.map ruleLoc
          unless sorted got == sorted expected do
            throw (IO.userError
              s!"{file} %{f.name} v{v}: rules differ\n got: {got}\n expected: {expected}")
          compared := compared + 1
  IO.println s!"corpus: {compared} simplify calls match Cranelift, {skipped} skipped (rewritten operands)"

#eval check

end Isle.Test.OptCorpus

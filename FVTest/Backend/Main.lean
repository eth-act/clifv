import FV.Backend

/-!
`lake exe lean-backend <in.clif> <out.s> [--traps <out.json>] [--rules <out.txt>]`: compile
every function of a `.clif` file with the Lean backend (`FV/Backend.lean`) to one assembly
file for `llvm-mc`; optionally write the function/trap table that
`clif-native --functions-obj` reads (`--traps`) and the names of the ISLE rules that fired
(`--rules`, one per line). Functions the backend does not support are listed on stderr (and in
the table), as is every fired rule outside the emitter-subset closure
(`Isle.Aarch64.Closure.rules`). Exit status 0 unless the arguments are wrong or the input
cannot be read.
-/

open Backend

def usage : String :=
  "usage: lean-backend <in.clif> <out.s> [--traps <out.json>] [--rules <out.txt>]"

def closureIds : Std.HashSet Isle.RuleId :=
  Isle.Aarch64.Closure.rules.foldl (fun s r => s.insert r.rule) {}

def run (input output : String) (traps rules : Option String) : IO UInt32 := do
  let src ← IO.FS.readFile input
  let fa := compileFile (Clif.parseFile src)
  IO.FS.writeFile output fa.text
  if let some t := traps then IO.FS.writeFile t fa.tableJson
  let names := Isle.Aarch64.program.ruleNames fa.rules
  if let some r := rules then IO.FS.writeFile r (String.join (names.map (· ++ "\n")))
  for (id, n) in fa.rules.zip names do
    if !closureIds.contains id then
      IO.eprintln s!"lean-backend: {input}: rule {n} fired outside the emitter-subset closure"
  for (n, why) in fa.unsupported do
    IO.eprintln s!"lean-backend: {input}: %{n}: unsupported: {why}"
  return 0

def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Option (Option String × Option String)
    | [] => some (none, none)
    | "--traps" :: t :: rest => (opts rest).map fun (_, r) => (some t, r)
    | "--rules" :: r :: rest => (opts rest).map fun (t, _) => (t, some r)
    | _ => none
  match args with
  | i :: o :: rest =>
    match opts rest with
    | some (t, r) => run i o t r
    | none => do IO.eprintln usage; return 2
  | _ => do IO.eprintln usage; return 2

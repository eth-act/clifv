import FV.Backend

/-!
`lake exe lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>]
[--dump <dir>] [--regalloc regalloc2|stack]`: compile every function of a `.clif` file with the
Lean backend (`FV/Backend.lean`). Register allocation: `regalloc2` (default; the
`lean-regalloc` oracle, `$LEAN_REGALLOC` or `rust/target/release/lean-regalloc`, every
allocation validated by the Lean checker, `docs/contracts/regalloc.md`) or `stack` (the
stack-slot baseline). If the output path ends in `.o`, write an ELF relocatable object encoded
by the Lean encoder (`FV/Backend/{Encode,Obj}.lean`, no assembler); otherwise write assembly
text (for `llvm-mc`, the encoder's test oracle). Optionally write the function/trap table that
`clif-native --functions-obj` reads (`--traps`), the names of the ISLE rules that fired
(`--rules`, one per line), and per function `name.bin`/`name.relocs.json`/`name.traps.json`
into `dir` (`--dump`, the schema of `clif2obj`'s dumps). Functions the backend does not
support are listed on stderr (and in the table), as is every fired rule outside the
emitter-subset closure (`Isle.Aarch64.Closure.rules`). Exit status 0 unless the arguments are
wrong, the input cannot be read, or encoding fails (an encoder or backend bug; the message
names the function and instruction).
-/

open Backend

def usage : String :=
  "usage: lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>] [--dump <dir>] [--regalloc regalloc2|stack]"

def closureIds : Std.HashSet Isle.RuleId :=
  Isle.Aarch64.Closure.rules.foldl (fun s r => s.insert r.rule) {}

structure Opts where
  traps : Option String := none
  rules : Option String := none
  dump : Option String := none
  stack : Bool := false

def run (input output : String) (o : Opts) : IO UInt32 := do
  let src ← IO.FS.readFile input
  let alloc ← if o.stack then pure Allocator.stack else Allocator.regalloc2 <$> defaultRegallocBin
  let fa ← compileFileIO alloc (Clif.parseFile src)
  if output.endsWith ".o" || o.dump.isSome then
    match fa.layout with
    | .error e =>
      IO.eprintln s!"lean-backend: {input}: encoding failed: {e}"
      return 1
    | .ok fbs =>
      if output.endsWith ".o" then IO.FS.writeBinFile output (elfObject fbs)
      if let some d := o.dump then
        IO.FS.createDirAll d
        for (_, fb) in fbs do
          IO.FS.writeBinFile (System.FilePath.mk d / s!"{fb.name}.bin") (wordsBytes fb.words)
          IO.FS.writeFile (System.FilePath.mk d / s!"{fb.name}.relocs.json") fb.relocsJson
          IO.FS.writeFile (System.FilePath.mk d / s!"{fb.name}.traps.json") fb.trapsJson
  if !output.endsWith ".o" then IO.FS.writeFile output fa.text
  if let some t := o.traps then IO.FS.writeFile t fa.tableJson
  let names := Isle.Aarch64.program.ruleNames fa.rules
  if let some r := o.rules then IO.FS.writeFile r (String.join (names.map (· ++ "\n")))
  for (id, n) in fa.rules.zip names do
    if !closureIds.contains id then
      IO.eprintln s!"lean-backend: {input}: rule {n} fired outside the emitter-subset closure"
  for (n, why) in fa.unsupported do
    IO.eprintln s!"lean-backend: {input}: %{n}: unsupported: {why}"
  return 0

def main (args : List String) : IO UInt32 := do
  let rec opts (o : Opts) : List String → Option Opts
    | [] => some o
    | "--traps" :: t :: rest => opts { o with traps := some t } rest
    | "--rules" :: r :: rest => opts { o with rules := some r } rest
    | "--dump" :: d :: rest => opts { o with dump := some d } rest
    | "--regalloc" :: "regalloc2" :: rest => opts { o with stack := false } rest
    | "--regalloc" :: "stack" :: rest => opts { o with stack := true } rest
    | _ => none
  match args with
  | i :: out :: rest =>
    match opts {} rest with
    | some o => run i out o
    | none => do IO.eprintln usage; return 2
  | _ => do IO.eprintln usage; return 2

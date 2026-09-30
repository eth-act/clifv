import FV.Backend
import FV.Opt.Legal
import FVTest.Opt.Common

/-!
`lake exe lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>]
[--dump <dir>] [--regalloc regalloc2|stack|regalloc2-small] [--personality <sym>]
[--opt [--opt-* options]]`: compile every function of a `.clif` file with the
Lean backend (`FV/Backend.lean`). Register allocation: `regalloc2` (default; the
`lean-regalloc` oracle, `$LEAN_REGALLOC` or `rust/target/release/lean-regalloc`, every
allocation validated by the Lean checker, `docs/contracts/regalloc.md`), `stack` (the
stack-slot baseline), or `regalloc2-small` (regalloc2 with the 10-register stress environment
`smallEnv`, for testing spill code). If the output path ends in `.o`, write an ELF relocatable object encoded
by the Lean encoder (`FV/Backend/{Encode,Obj}.lean`, no assembler); otherwise write assembly
text (for `llvm-mc`, the encoder's test oracle). Optionally write the function/trap table that
`clif-native --functions-obj` reads (`--traps`), the names of the ISLE rules that fired
(`--rules`, one per line), and per function `name.bin`/`name.relocs.json`/`name.traps.json`
into `dir` (`--dump`, the schema of `clif2obj`'s dumps). Functions the backend does not
support are listed on stderr (and in the table), as is every fired rule outside the
emitter-subset closure (`Isle.Aarch64.Closure.rules`). Exit status 0 unless the arguments are
wrong, the input cannot be read, or encoding fails (an encoder or backend bug; the message
names the function and instruction). With `--opt`, every function is first optimised by the
Lean mid-end (`Opt.optimize`, `docs/contracts/midend.md`; options in `FVTest/Opt/Common.lean`).
With `--personality <sym>` (`cargo fv`: `rust_eh_personality`), functions with landing pads
(`try_call`) get cg_clif's LSDA and a `zLPR` CIE with that personality routine
(`FV/Backend/Obj.lean`); without it their landing pads have no LSDA (as Cranelift's own
objects, which leave the LSDA to the embedder).

Every function that mentions `i128` is first legalised by `Opt.Legalize128` (rewritten to
plain `i8..i64` CLIF before the mid-end and the backend). A legalised function the validator
`Opt.Legal.check` accepts is covered by `E2E.backend_correct_legal` and treated like any other
function (`InSubset` and `lowerCheck` decided on the legalised form); a rejected one is
reported unverified ("i128 legalized (outside backend_correct: …)"), as is every legalised
function under `--opt` (no theorem composes the legalisation with the mid-end).
-/

open Backend

def usage : String :=
  "usage: lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>] [--dump <dir>] [--regalloc regalloc2|stack|regalloc2-small] [--personality <sym>] [--opt]"

def closureIds : Std.HashSet Isle.RuleId :=
  Isle.Aarch64.Closure.rules.foldl (fun s r => s.insert r.rule) {}

structure Opts where
  traps : Option String := none
  rules : Option String := none
  dump : Option String := none
  regalloc : String := "regalloc2"
  opt : Option Opt.Config := none
  personality : Option String := none

def run (input output : String) (o : Opts) : IO UInt32 := do
  let src ← IO.FS.readFile input
  let some alloc ← Allocator.ofName? o.regalloc
    | do IO.eprintln s!"lean-backend: unknown allocator {o.regalloc}"; return 2
  let pf := Clif.parseFile src
  let lg := Opt.Legalize128.parsedFile128 pf
  let pf := match o.opt with | some c => Opt.optimizeParsedFile c lg.file | none => lg.file
  let unv128 := match o.opt with
    | some _ => lg.unverified ++ lg.accepted.map
        (·, "i128 legalized and optimised (outside backend_correct_legal: --opt)")
    | none => lg.unverified
  -- the mid-end and `i128` theorems cover functions without `try_call` only
  let unvTry := pf.funcs.filterMap fun p => match p.func with
    | .ok f =>
      if !hasTryCall f then none
      else if o.opt.isSome then
        some (p.name, "try_call (outside backend_correct_opt_proven: try_call-free functions only)")
      else if lg.accepted.contains p.name then
        some (p.name, "try_call in an i128-legalized function (outside backend_correct_legal)")
      else none
    | .error _ => none
  let fa ← compileFileIO alloc pf (unv128 ++ unvTry)
  if output.endsWith ".o" || o.dump.isSome then
    match fa.layout with
    | .error e =>
      IO.eprintln s!"lean-backend: {input}: encoding failed: {e}"
      return 1
    | .ok fbs =>
      if output.endsWith ".o" then IO.FS.writeBinFile output (elfObject fbs fa.unwind fa.lsda o.personality)
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
  for (n, why) in fa.unverified do
    IO.eprintln s!"lean-backend: {input}: %{n}: compiled, unverified (outside backend_correct): {why}"
  for p in pf.funcs do
    if let .ok f := p.func then
      if hasTryCall f && fa.funcs.any (·.name == p.name) && !fa.unverified.any (·.1 == p.name) then
        IO.eprintln s!"lean-backend: {input}: %{p.name}: compiled, verified for normal returns (try_call: unwinding, landing pads and the LSDA trusted)"
  return 0

def main (args : List String) : IO UInt32 := do
  let rec opts (o : Opts) : List String → Option Opts
    | [] => some o
    | "--traps" :: t :: rest => opts { o with traps := some t } rest
    | "--rules" :: r :: rest => opts { o with rules := some r } rest
    | "--dump" :: d :: rest => opts { o with dump := some d } rest
    | "--regalloc" :: a :: rest => opts { o with regalloc := a } rest
    | "--personality" :: p :: rest => opts { o with personality := some p } rest
    | _ => none
  let (optCfg, args) ← match Opt.parseOptArgs args with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"lean-backend: {e}"; return 2
  match args with
  | i :: out :: rest =>
    match opts { opt := optCfg } rest with
    | some o => run i out o
    | none => do IO.eprintln usage; return 2
  | _ => do IO.eprintln usage; return 2

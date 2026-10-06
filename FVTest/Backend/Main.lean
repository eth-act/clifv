import FV.Backend
import FV.Opt.Legalize128Pass
import FVTest.Opt.Common
import FVTest.Backend.StockConfig

/-!
`lake exe lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>]
[--dump <dir>] [--regalloc regalloc2|spill|stack|regalloc2-small] [--personality <sym>]
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

A function inside the theorem's scope whose size is over the validation budget
(`Backend.validationBudget`, blocks × values) is compiled without running the lowering
validator and listed as `compiled, unverified (validation budget)`.
-/

open Backend

def usage : String :=
  "usage: lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>] [--dump <dir>] [--regalloc regalloc2|spill|stack|regalloc2-small] [--personality <sym>] [--opt] [--stock-config <request.json> --config-receipt <receipt.json>]"

/-- The rules the end-to-end theorem covers: the emitter-subset closure, and the `try_call`
rules of `lower_branch` (ids 1034 `bl`, 1035 GOT + `blr`: `Backend.Proof.tryRootRule`, proven by
`tryRulesCorrect`; 1036 `try_call_indirect`: `Backend.Proof.tryIndRootRule`, proven by
`tryIndRulesCorrect`), which are outside the generated closure (its opcodes have no
`try_call`). -/
def closureIds : Std.HashSet Isle.RuleId :=
  Isle.Aarch64.Closure.rules.foldl (fun s r => s.insert r.rule) ({} : Std.HashSet Isle.RuleId)
    |>.insert 1034 |>.insert 1035 |>.insert 1036

structure Opts where
  traps : Option String := none
  rules : Option String := none
  dump : Option String := none
  regalloc : String := "regalloc2"
  opt : Option Opt.Config := none
  personality : Option String := none
  stockConfig : Option String := none
  configReceipt : Option String := none

def run (input output : String) (o : Opts) : IO UInt32 := do
  let src ← IO.FS.readFile input
  if o.configReceipt.isSome != o.stockConfig.isSome then
    IO.eprintln "lean-backend: --stock-config and --config-receipt must be supplied together"
    return 2
  if o.stockConfig.isSome && (o.opt.isSome || o.regalloc != "regalloc2" || o.personality.isSome) then
    IO.eprintln "lean-backend: stock configuration forbids independent opt/regalloc/personality overrides"
    return 2
  let mut stock : Option StockConfig.Config := none
  if let some path := o.stockConfig then
    let request ← match Lean.Json.parse (← IO.FS.readFile path) with
      | .ok j => pure j
      | .error e => do IO.eprintln s!"lean-backend: invalid configuration JSON: {e}"; return 2
    let checked := StockConfig.parse request
    let error := match checked with | .ok _ => none | .error e => some e
    if let some receipt := o.configReceipt then
      IO.FS.writeFile receipt ((StockConfig.receipt request error).pretty ++ "\n")
    match checked with
    | .error e => IO.eprintln s!"lean-backend: unsupported stock configuration: {e}"; return 3
    | .ok c => stock := some c
  let some alloc ← Allocator.ofName? o.regalloc
    | do IO.eprintln s!"lean-backend: unknown allocator {o.regalloc}"; return 2
  let pf := Clif.parseFile src
  let lg := Opt.Legalize128.parsedFile128 pf
  let pf := match o.opt with | some c => Opt.optimizeParsedFile c lg.file | none => lg.file
  let unv128 := match o.opt with
    | some _ => lg.unverified ++ lg.accepted.map
        (·, "i128 legalized and optimised (outside backend_correct_legal: --opt)")
    | none => lg.unverified
  -- the mid-end theorems cover functions without `try_call`/`try_call_indirect` and
  -- `call_indirect` only (`E2E.backend_correct_legal` covers both; `Opt.Legal.check` rejects
  -- `try_call_indirect`)
  let unvTry := pf.funcs.filterMap fun p => match p.func with
    | .ok f =>
      if o.opt.isNone then none
      else if hasTryCall f then
        some (p.name, "try_call (outside backend_correct_opt_proven: try_call-free functions only)")
      else if Opt.hasCallIndirect f then
        some (p.name, "call_indirect (outside backend_correct_opt_proven: functions without indirect calls only)")
      else none
    | .error _ => none
  let fa ← match stock with
    | none => compileFileIO alloc pf (unv128 ++ unvTry)
    | some c => (compileFileWith (StockConfig.allocate c alloc) pf
        (unv128 ++ unvTry ++ pf.funcs.map (fun p => (p.name, "experimental stock-configured driver (outside backend_correct)"))))
  let fa := match stock with
    | some c => if c.unwind then fa else { fa with unwind := [] }
    | none => fa
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
          if let some c := stock then
            let metadata := Lean.Json.mkObj [
              ("name", Lean.toJson fb.name), ("alignment", Lean.toJson (4 : Nat)),
              ("unwind_disabled", Lean.toJson (!c.unwind)),
              ("stack_maps", Lean.toJson ([] : List String)),
              ("exception_metadata_comparison_supported", Lean.toJson false)]
            IO.FS.writeFile (System.FilePath.mk d / s!"{fb.name}.metadata.json") (metadata.pretty ++ "\n")
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
  for (n, why) in fa.unvalidated do
    IO.eprintln s!"lean-backend: {input}: %{n}: compiled, unverified (validation budget): {why}"
  -- A function with a `try_call` is inside `backend_correct_final` for the runs in which every
  -- callee of a `try_call` returns normally (callee contract `CalleeTryOk`: the results only; the
  -- exception payload registers are havocked on the normal return); unwinding is trusted.
  for p in pf.funcs do
    if let .ok f := p.func then
      if hasTryCall f && fa.funcs.any (·.name == p.name) && !fa.unverified.any (·.1 == p.name) &&
          !fa.unvalidated.any (·.1 == p.name) then
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
    | "--stock-config" :: c :: rest => opts { o with stockConfig := some c } rest
    | "--config-receipt" :: c :: rest => opts { o with configReceipt := some c } rest
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

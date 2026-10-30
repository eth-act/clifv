import FV.Backend
import FV.Backend.MemoryCfgNIProduction
import FV.Opt.Legalize128Pass
import FV.Opt.LegalExn
import FVTest.Opt.Common
import FVTest.Backend.StockConfig
import FVTest.Backend.AllocChoice
import FVTest.Backend.CraneliftInput
import FV.Backend.Proof.LowerSimUCheck
import FV.Backend.Proof.LowerSimUCheckTC
import FV.Compile.SubsetTC
import FV.E2E.RegLevelFrameSaved
import FV.E2E.RegLevelUTry

/-!
`lake exe lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>]
[--dump <dir>] [--regalloc lean|regalloc2|spill|stack|regalloc2-small] [--personality <sym>]
[--opt [--opt-* options]]`: compile every function of a `.clif` file with the
Lean backend (`FV/Backend.lean`). Register allocation: `regalloc2` (default, as Cranelift: the
external `lean-regalloc` oracle, `$LEAN_REGALLOC` or `rust/target/release/lean-regalloc`, given
the code in the form Cranelift's lowering hands to regalloc2 (vreg numbering, `args`, calls to
`sret` callees: `FVTest/Backend/CraneliftInput.lean`); every allocation validated by the Lean checker `checkAlloc`
with the spill allocation as fallback, `docs/contracts/regalloc.md`; with `$FV_RA_OUT` set, the
answers are written there; with `$FV_RA_DIAG` set, one line per function is appended there: the
code regalloc2 was given and the allocation lowered), `lean` (the Lean allocator `leanAlloc`,
`FV/Backend/LinearScan.lean`, validated the same way, `FVTest/Backend/AllocChoice.lean`),
`spill` (the fallback for every function), `stack` (the
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
Lean mid-end (`Opt.optimizeExe`, the executable compiler's mid-end, `docs/contracts/midend.md`;
options in `FVTest/Opt/Common.lean`).
With `--personality <sym>` (`cargo fv`: `rust_eh_personality`), functions with landing pads
(`try_call`) get cg_clif's LSDA and a `zLPR` CIE with that personality routine
(`FV/Backend/Obj.lean`); without it their landing pads have no LSDA (as Cranelift's own
objects, which leave the LSDA to the embedder).

Every function that mentions `i128` is first legalised by `Opt.Legalize128` (rewritten to
plain `i8..i64` CLIF before the mid-end and the backend). A legalised function the validator
`Opt.Legal.checkW` accepts is covered by `E2E.backend_correct_legal_wide` and treated like any other
function (`InSubset` and `lowerCheck` decided on the legalised form); a rejected one is
reported unverified ("i128 legalized (outside backend_correct: …)"). Under `--opt` with the
proven rule sets (`--opt-proven-only`) a legalised function is covered by
`E2E.backend_correct_legal_opt_wide` (the legalisation composed with the mid-end), every other by
`E2E.backend_correct_opt_exe` (`call_indirect`, `try_call`, `try_call_indirect` included); with
unproven rules every legalised function is reported unverified. The unwinding of a legalised
function with a `try_call` is covered by `E2E.backend_correct_legal_unwind` when the
handler-edge check `Opt.Legal.exnOk` and the unwinding theorem's checks pass (dead cleanup,
no `--opt`). Under `--opt` with the proven rule sets, the unwinding of a function that is not
legalised is covered by `E2E.backend_correct_opt_exe_cleanup_unwind` (without dead cleanup
`E2E.backend_correct_opt_exe_unwind`) when its compiled form is the mid-end's output on its
source function and the unwinding theorem's checks pass on the optimised function; a legalised
one by `E2E.backend_correct_legal_opt_unwind` (dead cleanup) when its compiled form is the
mid-end's output on the source function's legalisation, which `Opt.Legal.check` and
`Opt.Legal.exnOk` accept, and the checks pass.

A function inside the theorem's scope whose size is over the validation budget
(`Backend.validationBudget`, blocks × values) is compiled without running the lowering
validator and listed as `compiled, unverified (validation budget)`.
-/

open Backend

def usage : String :=
  "usage: lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>] [--dump <dir>] [--regalloc lean|regalloc2|spill|stack|regalloc2-small] [--personality <sym>] [--opt] [--dead-cleanup|--no-dead-cleanup] [--pipeline-t] [--stock-config <request.json> --config-receipt <receipt.json>]"

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
  /-- `--regalloc`; default `regalloc2`. -/
  regalloc : Option String := none
  opt : Option Opt.Config := none
  personality : Option String := none
  stockConfig : Option String := none
  configReceipt : Option String := none
  deadCleanup : Bool := true
  /-- `--pipeline-t` (or `FV_PIPELINE_T=1`): compile with `E2E.LinkCheck.pipeT`'s pipeline (the
  D0 lowering, no dead cleanup, no Stock routes), the compiler `crate_correct_inScope` covers.
  Only for regenerating `crate-proofs/Crates/InScopeInputs` (`scripts/regen-crate-proofs.sh`). -/
  pipelineT : Bool := false

/-- One function's allocation as the backend lowered it: the prepared VCode `vcp`, the
allocation `rf` with `lowerRFunc vcp rf = .ok af` (`lowerAllocReady_eq`, `lowerAlloc_eq`), and
`af`; `none` without an `RFunc` (the stack allocator) or when `prepare` failed. -/
abbrev AllocRecord := Option (VCode × RFunc × AFunc)

/-- Which allocation `lowerAllocReady vcp ra` lowers, and why (`FV_RA_DIAG`). -/
def allocVerdict (vcp : VCode) (ra : Except String RFunc) : String :=
  match ra with
  | .error e => s!"no answer: {e}"
  | .ok rf =>
    match checkAlloc vcp rf with
    | .error e => s!"checkAlloc: {e}"
    | .ok _ =>
      match lowerRFunc vcp rf with
      | .error e => s!"lowerRFunc: {e}"
      | .ok af => if emitReady af then "regalloc2" else "not emitReady"

/-- `Allocator.run`, also returning each function's `AllocRecord` (the objects the unwinding
theorems name). The `regalloc2` case is `allocateRegalloc2` with the allocation it lowers
(`allocResult vcp (readyAnswer vcp ra)`) kept; `lean-regalloc` is given `(shapeOf vcp).code`
(`CraneliftInput.shape`: regalloc2's input as Cranelift builds it, #551), its answer read back
and rebuilt against `vcp`. -/
def allocRecording (a : Allocator) (vcs : Array VCode)
    (shapeOf : VCode → CraneliftInput.Shape := fun vcp => .same vcp "") :
    IO (Array (Except String AFunc) × Array AllocRecord) := do
  match a with
  | .stack => pure (vcs.map allocate, vcs.map fun _ => none)
  | .spill =>
    let ps := vcs.map prepareChecked
    let afs := ps.map (·.bind fun vcp => lowerRFunc vcp (spillAlloc vcp))
    pure (afs, (ps.zip afs).map fun (p, af) => match p, af with
      | .ok vcp, .ok af => some (vcp, spillAlloc vcp, af)
      | _, _ => none)
  | .regalloc2 bin env =>
    let prepared := vcs.map prepareChecked
    let ok := prepared.filterMap (·.toOption)
    let shapes := ok.map shapeOf
    let rs : Array (Except String RFunc) ← do
      try
        match ← CraneliftInput.runLeanRegallocVia bin env shapes ok with
        | .error e => pure (ok.map fun _ => .error e)
        | .ok rs => pure (rs.map (·.bind RAResult.oracle))
      catch e => pure (ok.map fun _ => .error (toString e))
    let mut out : Array (Except String AFunc) := #[]
    let mut recs : Array AllocRecord := #[]
    let mut ans : Array String := #[]
    let diagOn := (← IO.getEnv "FV_RA_DIAG").isSome
    let mut diag : Array String := #[]
    let mut j := 0
    for p in prepared do
      match p with
      | .error e =>
        out := out.push (.error e)
        recs := recs.push none
      | .ok vcp =>
        let ra := rs[j]?.getD (.error "lean-regalloc: missing result")
        let af := lowerAllocReady vcp ra
        out := out.push af
        recs := recs.push (af.toOption.map (vcp, allocResult vcp (readyAnswer vcp ra), ·))
        ans := ans.push <| match ra with
          | .ok rf =>
            if raAnswerRoundTrip vcp rf then raAnswerJson vcp rf
            else raFailJson vcp.name "the answer does not rebuild the allocation"
          | .error e => raFailJson vcp.name e
        if diagOn then
          diag := diag.push s!"{vcp.name}\t{(shapes[j]?.map (·.why)).getD ""}\t{allocVerdict vcp ra}"
        j := j + 1
    -- `cargo fv --keep-temps`: regalloc2's answers, for `cargo fv link-proof` and `lean-link`
    -- (which rebuild the allocations from them, as for the Lean allocator's)
    if let some p ← IO.getEnv "FV_RA_OUT" then
      IO.FS.writeFile p ("{\"functions\":[" ++ ",".intercalate ans.toList ++ "]}\n")
    -- debugging aid (#551): per function, the code regalloc2 was given and the path taken
    if let some p ← IO.getEnv "FV_RA_DIAG" then
      let h ← IO.FS.Handle.mk p .append
      for l in diag do h.putStrLn l
    pure (out, recs)

/-- `allocRunOfName? n` with the `AllocRecord`s: the Lean allocator (`n = "lean"`:
`allocateLeanAnswers`, writing the answers to `$FV_RA_OUT` when set) records its allocation as
the `regalloc2` case does (`allocResult vcp (readyAnswer vcp ra)` with `ra = leanAlloc vcp`);
other names run `allocRecording a`. -/
def allocRecordingNamed (n : String) (a : Allocator) (vcs : Array VCode)
    (shapeOf : VCode → CraneliftInput.Shape := fun vcp => .same vcp "") :
    IO (Array (Except String AFunc) × Array AllocRecord) := do
  if n != "lean" then return ← allocRecording a vcs shapeOf
  let (afs, ans) := allocateLeanAnswers vcs
  if let some p ← IO.getEnv "FV_RA_OUT" then
    IO.FS.writeFile p ("{\"functions\":[" ++ ",".intercalate ans.toList ++ "]}\n")
  let recs := (vcs.zip afs).map fun (vc, af) => match prepareChecked vc, af with
    | .ok vcp, .ok af => some (vcp, allocResult vcp (readyAnswer vcp (leanAlloc vcp)), af)
    | _, _ => none
  pure (afs, recs)

/-- The first check of the unwinding theorem (`E2E.backend_correct_final_cleanup_unwind`, or
`E2E.backend_correct_final_unwind` without dead cleanup) that fails for a compiled function `f`
with a `try_call`, on the objects the theorem names: the lowering `vc` of `f` (`unwCheck`, the
exceptional-edge half of `lowerCheckU`; `lowerCheck` ran during compilation), the prepared
VCode and the allocation (`savedCheck vcp rf`), the allocated function and its final code
(`lastCallsOk af fa`, `padsNonzeroB af fa`). `callSites`/`unwindRows` succeed for every compiled
function (compilation fails otherwise). With `tc` (a function with typed `try_call`s,
`Compile.functionETC`; #585): the same checks with the class-aware validator `unwCheckTC` over
`lowerCheckTC`'s recording (`loweringUTC_of_check`) in place of `unwCheck`; no unwinding theorem
covers typed `try_call`s yet. -/
def unwindCheckFailure? (f : Clif.Function) (rec : AllocRecord) (fa? : Option FnAsm)
    (tc : Bool := false) : Option String :=
  match lowerFunction f with
  | .error _ => some "lowerFunction"
  | .ok vc =>
    if tc && !(Compile.functionETC f && Proof.Driver.unwCheckTC f vc) then some "unwCheckTC"
    else if !tc && !Proof.Driver.unwCheck f vc then some "unwCheck"
    else match rec, fa? with
      | some (vcp, rf, af), some fa =>
        if !savedCheck vcp rf then some "savedCheck"
        else if !Proof.lastCallsOk af fa then some "lastCallsOk"
        else if !Proof.padsNonzeroB af fa then some "padsNonzeroB"
        else none
      | _, _ => some "no lowerRFunc allocation (allocator)"

def run (input output : String) (o : Opts) : IO UInt32 := do
  let src ← IO.FS.readFile input
  let pipelineT := o.pipelineT || (← IO.getEnv "FV_PIPELINE_T") == some "1"
  let o := if pipelineT then { o with deadCleanup := false } else o
  if o.configReceipt.isSome != o.stockConfig.isSome then
    IO.eprintln "lean-backend: --stock-config and --config-receipt must be supplied together"
    return 2
  if o.stockConfig.isSome && (o.opt.isSome || o.regalloc.any (· != "regalloc2") || o.personality.isSome) then
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
      IO.FS.writeFile receipt ((StockConfig.receipt request error none o.deadCleanup).pretty ++ "\n")
    match checked with
    | .error e => IO.eprintln s!"lean-backend: unsupported stock configuration: {e}"; return 3
    | .ok c => stock := some c
  let ra := o.regalloc.getD "regalloc2"
  let some runAlloc ← allocRunOfName? ra
    | do IO.eprintln s!"lean-backend: unknown allocator {ra}"; return 2
  -- the stock configuration requires regalloc2 (checked above)
  let alloc := (← Allocator.ofName? ra).getD .spill
  let source := Clif.parseFile src
  let lg := Opt.Legalize128.parsedFile128 source
  let pf := match o.opt with | some c => Opt.optimizeParsedFile c lg.file | none => lg.file
  -- the mid-end theorems (`E2E.backend_correct_opt_exe`, `E2E.backend_correct_legal_opt`) cover
  -- every function, legalised ones included, for the proven rule sets
  let unv128 := match o.opt with
    | some c => if c.rules == .cranelift && c.ruleAllow == .proven then lg.unverified
      else lg.unverified ++ lg.accepted.map
        (·, "i128 legalized and optimised with unproven rules (outside backend_correct_legal_opt: --opt)")
    | none => lg.unverified
  let unvTry : List (String × String) := []
  -- The settings checks see each function before and after `i128` legalisation.
  let clif (name : String) : List Clif.Function :=
    (source.funcs ++ pf.funcs).filterMap fun p => if p.name == name then p.func.toOption else none
  let rejected ← IO.mkRef (#[] : Array (String × String))
  -- the allocation of each function as lowered (by VCode name), for the unwinding checks
  let records ← IO.mkRef (#[] : Array (String × AllocRecord))
  let allocNone : Array VCode → IO (Array (Except String AFunc)) := fun vcs => do
    -- regalloc2 sees the code as Cranelift's lowering gives it (`CraneliftInput.shape`, #551)
    let byName (n : String) : Option Clif.Function :=
      (pf.funcs.find? (·.name == n)).bind (·.func.toOption)
    let shapeOf := fun (vcp : VCode) => CraneliftInput.shape (byName vcp.name) o.deadCleanup vcp
    let (afs, recs) ← allocRecordingNamed ra alloc vcs shapeOf
    records.set ((vcs.map (·.name)).zip recs)
    pure afs
  let fa ← match stock with
    | none => (if pipelineT then compileFileWith allocNone pf (unv128 ++ unvTry) false
        else compileFileMemoryCfgNIWhen (!o.opt.isSome &&
          !(pf.funcs.any fun p => p.func.toOption.any fun f => f.blocks.any (·.term.isTry)))
          allocNone pf (unv128 ++ unvTry) o.deadCleanup)
    | some c => (compileFileMemoryCfgNIWhen (!pipelineT && !o.opt.isSome &&
        !(pf.funcs.any fun p => p.func.toOption.any fun f => f.blocks.any (·.term.isTry)))
        (StockConfig.allocateWith c clif rejected allocNone) pf
        (unv128 ++ unvTry ++ pf.funcs.map (fun p => (p.name, "experimental stock-configured driver (outside backend_correct)"))) o.deadCleanup)
  if let (some request, some receipt) := (stock.map (·.request), o.configReceipt) then
    IO.FS.writeFile receipt
      ((StockConfig.receipt request none (some (← rejected.get).toList) o.deadCleanup).pretty ++ "\n")
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
  -- exception payload registers are havocked on the normal return). Its unwinding (landing
  -- pads, the LSDA, the frame unwound by the CFI) is inside the unwinding theorem
  -- (`E2E.backend_correct_final_cleanup_unwind`, without dead cleanup
  -- `E2E.backend_correct_final_unwind`) when that theorem's checks pass on its compiled objects
  -- (`unwindCheckFailure?`). An `i128`-legalised function is inside
  -- `E2E.backend_correct_legal_unwind` (dead cleanup only) when, in addition, its legalisation
  -- is recomputed from the source function with the same result, and `Opt.Legal.check` and the
  -- handler-edge check `Opt.Legal.exnOk` accept it (`legalUnwOk`). Under `--opt` with the proven
  -- rule sets, a function that is not legalised is inside
  -- `E2E.backend_correct_opt_exe_cleanup_unwind` (without dead cleanup
  -- `E2E.backend_correct_opt_exe_unwind`) when its compiled form is `Opt.optimizeExe` of its
  -- source function, recomputed (`optUnwOk`), and the checks pass on the optimised function; a
  -- legalised one is inside `E2E.backend_correct_legal_opt_unwind` (dead cleanup only) when its
  -- compiled form is `Opt.optimizeExe` of the source function's legalisation, recomputed, which
  -- `Opt.Legal.check` and `Opt.Legal.exnOk` accept (`legalOptUnwOk`). No unwinding theorem
  -- composes unproven rule sets.
  let recs ← records.get
  let thm := if o.deadCleanup then "backend_correct_final_cleanup_unwind"
    else "backend_correct_final_unwind"
  let optThm := if o.deadCleanup then "backend_correct_opt_exe_cleanup_unwind"
    else "backend_correct_opt_exe_unwind"
  let legalUnwOk (name : String) (g : Clif.Function) : Bool :=
    match (source.funcs.find? (·.name == name)).bind (·.func.toOption) with
    | some f => match Opt.Legalize128.function128Cert f with
      | .ok (g', cert) => g' == g && Opt.Legal.check f g cert && Opt.Legal.exnOk f g cert
      | .error _ => false
    | none => false
  let provenOpt : Bool := match o.opt with
    | some c => c.rules == .cranelift && c.ruleAllow == .proven
    | none => false
  let optUnwOk (name : String) (g : Clif.Function) : Bool :=
    match o.opt, (source.funcs.find? (·.name == name)).bind (·.func.toOption) with
    | some c, some f => provenOpt && Opt.optimizeExe f c == g
    | _, _ => false
  let legalOptUnwOk (name : String) (g : Clif.Function) : Bool :=
    match o.opt, (source.funcs.find? (·.name == name)).bind (·.func.toOption) with
    | some c, some f => match Opt.Legalize128.function128Cert f with
      | .ok (g', cert) => provenOpt && Opt.optimizeExe g' c == g && Opt.Legal.check f g' cert &&
        Opt.Legal.exnOk f g' cert
      | .error _ => false
    | _, _ => false
  for p in pf.funcs do
    if let .ok f := p.func then
      if hasTryCall f && fa.funcs.any (·.name == p.name) && !fa.unverified.any (·.1 == p.name) &&
          !fa.unvalidated.any (·.1 == p.name) then
        let legal := lg.accepted.contains p.name
        let why? : Option String :=
          if o.opt.isSome && !provenOpt then
            some "--opt with unproven rule sets: no unwinding theorem composes them (--opt-proven-only)"
          else if legal && !o.deadCleanup then
            some "i128 legalized: no unwinding theorem composes the legalisation without dead cleanup"
          else if o.opt.isSome && legal && !legalOptUnwOk p.name f then
            some "--opt, i128 legalized: not Opt.optimizeExe of the source function's legalisation accepted by Opt.Legal.check and Opt.Legal.exnOk"
          else if o.opt.isSome && !legal && !optUnwOk p.name f then
            some "--opt: the compiled function is not Opt.optimizeExe of its source function"
          else if o.opt.isNone && legal && !legalUnwOk p.name f then
            some "i128 legalized: Opt.Legal.check (no try_call_indirect, no call_indirect at an i128 signature) or Opt.Legal.exnOk (the handler edges) rejects"
          else (unwindCheckFailure? f ((recs.find? (·.1 == p.name)).bind (·.2))
            (fa.funcs.find? (·.name == p.name))).map (s!"unwinding check failed: {·}")
        let thm := if legal && o.opt.isSome then "backend_correct_legal_opt_unwind"
          else if legal then "backend_correct_legal_unwind"
          else if o.opt.isSome then optThm else thm
        match why? with
        | none =>
          IO.eprintln s!"lean-backend: {input}: %{p.name}: compiled, verified (try_call: unwinding by {thm}; the unwinder/personality model and the decoding of the emitted tables trusted)"
        | some why =>
          let rec? := (recs.find? (·.1 == p.name)).bind (·.2)
          let fa? := fa.funcs.find? (·.name == p.name)
          if why == "unwinding check failed: unwCheck" && Compile.functionETC f &&
              (unwindCheckFailure? f rec? fa? (tc := true)).isNone then
            IO.eprintln s!"lean-backend: {input}: %{p.name}: compiled, verified for normal returns (try_call with float values: unwinding, landing pads and the LSDA trusted; the exceptional-edge conditions hold on the typed lowering (unwCheckTC, loweringUTC_of_check), no unwinding theorem covers typed try_calls yet)"
          else
            IO.eprintln s!"lean-backend: {input}: %{p.name}: compiled, verified for normal returns (try_call: unwinding, landing pads and the LSDA trusted; {why})"
  return 0

def main (args : List String) : IO UInt32 := do
  let rec opts (o : Opts) : List String → Option Opts
    | [] => some o
    | "--traps" :: t :: rest => opts { o with traps := some t } rest
    | "--rules" :: r :: rest => opts { o with rules := some r } rest
    | "--dump" :: d :: rest => opts { o with dump := some d } rest
    | "--regalloc" :: a :: rest => opts { o with regalloc := some a } rest
    | "--personality" :: p :: rest => opts { o with personality := some p } rest
    | "--stock-config" :: c :: rest => opts { o with stockConfig := some c } rest
    | "--config-receipt" :: c :: rest => opts { o with configReceipt := some c } rest
    | "--dead-cleanup" :: rest => opts { o with deadCleanup := true } rest
    | "--no-dead-cleanup" :: rest => opts { o with deadCleanup := false } rest
    | "--pipeline-t" :: rest => opts { o with pipelineT := true } rest
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

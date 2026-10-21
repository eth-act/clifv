import FV.Backend.Lowering.StockLogicalNI
import FV.Link.Compile
import FV.Link.DeadCleanupCompile
import FV.Link.OptCompile
import FV.Link.Placed
import FV.E2E.SrcScopeDefs
import FV.Front.Read
import FV.E2E.LinkScopeInputDefs
import FV.Link.Ld.Spec
import FVTest.Link.LdArgs
import FV.Link.ExeUCompile
import FV.Link.SemanticCompileDefs

/-! # `lake exe lean-link DIR [--dead-cleanup|--no-dead-cleanup] [--opt] [--verified] [--ld FILE]`:
the executable compiler on an executable (L1, L2b)

`--ld FILE` (`cargo fv` passes it when `lean-ld` linked the executable; `FILE`: `lean-ld`'s
arguments): after the compiler succeeds, `ldCheck` links again with `Link.Ld.link`, checks that
the output is the executable read, and decides `Plan.specOkB` of the plan against the link spec:
the premise of `Link.Ld.file0OkB_ld` and the totality theorems `…compileExe{,Opt}_total_ld`
(no check of the linker's output); reported, and added to the `--verified` totality note.

`DIR` is `cargo fv link-proof --cgus … --no-check`'s output for an executable linked by
`cargo fv --lean-link` (docs/research/lean-linker.md): the frontend bundle `bundle.json`
(docs/contracts/frontend.md; read by `Front.readBundle`: per codegen unit the program's
functions in placement order — their CLIF as the frontend wrote it and `lean-regalloc`'s
output — its data objects, local symbols and the merge's names; the executable's symbols and
the functions' Lean code addresses). The `Link.LinkSpec` is built in Lean by `Front.buildSpec`
(the renaming to linked names, the data closure, the CLIF image's symbols; `FV/Front/BundleProof.lean`:
its source program is the units' program under the linked names, a scoping, alpha-equivalent to
the units' program under any scoping; the region's base `R`: the first function's address) and
given the Lean compiler's layout (`Link.LinkSpec.placedPar`/`Link.DeadCleanup.placedPar`,
`FV/Link/Placed.lean`: the CLIF functions' names and the sizes of their compiled code, `=
placed`), the layout the totality theorems are about, by construction; no size is read from
outside (rust-lld's placement of the region object is checked against it, `symsOkB`). The
tool then runs the executable
compiler — `Link.DeadCleanup.compileExe` (default, `--dead-cleanup`; the input conditions
`InScopeP`) or `Link.compileExe` (`--no-dead-cleanup`; the input conditions `InScopeIn`, decided
on the CLIF alone), then the Lean linker (placement, the
compiler's pipeline, the linker's checks, the checks of rust-lld's output — among them that
rust-lld put every function at its placement, `symsOkB`) — and writes the result over the
executable. It prints the theorems covering the written executable (`coverage:`): the
compiler's `compileExe_correct` (entries without a reachable call cycle) and
`compileExe_correct_peak` (any entry), and, for an input in the source domain (`SrcScopeB`),
`compileExe_correct_source` and `compileExe_correct_source_peak` about the original
(pre-`i128`-legalisation) program. No per-crate proof needed.

Outside the compiler's input conditions the tool links with the bare Lean linker (`leanLink`, no
compiler theorem; reported as such). **`--verified`** fails closed: an input outside `SrcScopeB`, outside
the per-function input conditions decided on the CLIF alone (`fnScopeInB`, V7) or outside
`InScopeP` is an error and the executable is not written, so every executable it writes is
covered by the four theorems above and its input is in `InScopeIn` (`InScopeP`'s program-level
conditions with `fnScopeInB`), on which the compiler is proven total
(`Link.DeadCleanup.compileExe_total_reach_input`, `Link.compileExe_total_reach`, given the
layout, reach and `file0` conditions).

**`--opt`**: the optimising executable compiler — `Link.DeadCleanup.compileExeOpt` (default) or
`Link.compileExeOpt` (`--no-dead-cleanup`): `compileExe` on the input whose functions the
mid-end optimised (`Link.LinkSpec.opt`: `Opt.optimizeExe` with the proven rule sets, each
optimised function printed to CLIF and used only when it parses back to itself; the functions
where it does not keep their input and are listed, `optFallbacks:`). The input conditions are
decided on the optimised input, the source domain on the original one; coverage:
`compileExeOpt_correct`, `compileExeOpt_correct_peak`, `compileExeOpt_correct_source`,
`compileExeOpt_correct_source_peak`, totality `compileExeOpt_total_reach_input`. The layout is
then the optimised functions' (`placedPar S.opt`, the theorem's `S.withSizes (sizesOf S.opt)`
after `withSizes_opt`; `cargo fv --lean-link --opt-proven-only`, whose units `lean-backend
--opt-proven-only` compiles with the same mid-end).

**Unwinding** (S10f): with the cleanup compiler the tool then decides `Link.DeadCleanup.unwOkB`
on the written executable — the unwind tables rust-lld wrote for the region, found as
libunwind finds them (`.eh_frame_hdr`'s search), are the compiled functions'
(`Link.EhCheck.ehOkR`), and the compiled functions pass the unwinding checks
(`Link.EhCheck.unwFnsB`) — so `compileExeU` succeeds and the coverage adds
`compileExe_correct_unwind`/`_peak` (the exceptional edges); otherwise the executable is still
written (the theorems above do not depend on unwinding) and the first failing reason is printed.
-/

open Lean E2E E2E.LinkCheck E2E.Elf Link

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

open Backend in
/-- The program-level per-function input conditions `g` fails (`progScopeB`'s conjuncts, the
indirect-call scope `indB` and the call sites `callScopeB` split by cause). -/
def scopeFails (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : List String :=
  let ind := !indFreeB g
  let site (s : Clif.Signature) (args : List Nat) : List String :=
    if indSiteB P S g s args then [] else ["callScopeB:blrRegs"]
  let sites := g.blocks.flatMap fun B =>
    (B.body.flatMap fun st => match st.inst with
      | .call fn args => match g.extern? fn with
        | some e => if dirSiteB P e args then [] else ["callScopeB:dirSite"]
        | none => []
      | .callIndirect sg _ args => match g.sigDecls.lookup sg with
        | some s => site s args
        | none => []
      | _ => []) ++
    match B.term with
    | .tryCall fn args _ => match g.extern? fn with
      | some e => if dirSiteB P e args then [] else ["callScopeB:dirSite"]
      | none => []
    | .tryCallIndirect _ args et => match g.sigDecls.lookup et.sig with
      | some s => site s args
      | none => []
    | _ => []
  ((if declSigB P g then [] else ["declSigB"]) ++
    (if ind && P.funcs.any (fun h => mayB S g h.name && indSigB g h &&
        (match sigParamBytes h.sig with | .ok b => decide (b.length > 8) | .error _ => true))
      then ["indB:calleeStack"] else []) ++
    (if ind && P.funcs.any (fun h => mayB S g h.name && indSigB g h && !indRetsB g h)
      then ["indB:sretRets"] else []) ++
    sites ++ (if outScopeB P g then [] else ["outScopeB"])).eraseDups

/-- The source-domain conditions (`SrcScopeB`'s per-function conjuncts) a parsed function `g` of
the source program `P` fails. -/
def srcFails (P : Clif.Program) (g : Clif.Function) : List String :=
  (if Opt.Legalize128.legalOkB g then [] else ["legalOkB"]) ++
    (if linkFreeB g then [] else ["linkFreeB"]) ++ (if declSigB P g then [] else ["declSigB"])

/-- `--key VALUE` taken out of an argument list. -/
def takeOpt (key : String) : List String → Option String × List String
  | k :: v :: rest =>
    if k == key then (some v, rest) else let (o, r) := takeOpt key (v :: rest); (o, k :: r)
  | l => (none, l)

/-- **`lean-ld`'s plan against the link spec** (`--ld FILE`, `FILE`: `lean-ld`'s arguments, one
per line): links again (`Link.Ld.link`, deterministic), checks that its output is `file0` and
decides `Plan.specOkB`, the premise of `Link.Ld.file0OkB_ld` and the `…_total_ld` theorems;
on failure, the failing conjuncts. -/
def ldCheck (P : LinkSpec) (file0 : ByteArray) (f : String) : IO (Except String Unit) := do
  let args := ((← IO.FS.readFile f).splitOn "\n").filter (!·.isEmpty)
  match ← Link.Ld.parseLdArgs args with
  | .error e => return .error s!"lean-ld's arguments: {e}"
  | .ok c => match Link.Ld.link c.opts c.ins with
    | .error e => return .error s!"lean-ld: {e}"
    | .ok r =>
      if r.img.write.data != file0.data then return .error "lean-ld's output is not the executable read"
      let pl := r.plan
      if pl.specOkB P then return .ok ()
      let pa := pl.pieces.toArray
      let am := addrMap P.input0.addrs
      let bad := P.data.filter fun o =>
        !Link.Ld.objPlanB am pl pa (Link.Ld.pieceHint pa) (offsetOf pl.phdrs P.R) P.size o
      let fails := (if pl.regionInB P.R P.size then [] else ["regionInB"]) ++
        (if Link.Ld.symsPlanB P.input0 pl then [] else ["symsPlanB"]) ++
        (if Link.Ld.tlsBoundB P pl then [] else ["tlsBoundB"]) ++
        (if bad.isEmpty then [] else [s!"dataPlanB ({bad.length} object(s): {(bad.take 3).map (·.name)})"])
      return .error s!"Plan.specOkB fails: {fails}"

def main (args0 : List String) : IO UInt32 := do
  let usage := "usage: lean-link DIR [--dead-cleanup|--no-dead-cleanup] [--opt] [--verified] [--ld FILE]"
  let (ldFile, args) := takeOpt "--ld" args0
  let flags := args.filter (·.startsWith "--")
  if flags.any (fun a => !["--dead-cleanup", "--no-dead-cleanup", "--opt", "--verified"].contains a) ||
      (flags.contains "--dead-cleanup" && flags.contains "--no-dead-cleanup") then
    IO.eprintln usage; return 2
  let deadCleanup := !flags.contains "--no-dead-cleanup"
  let verified := flags.contains "--verified"
  let opt := flags.contains "--opt"
  let [d] := args.filter (!·.startsWith "--") | do IO.eprintln usage; return 2
  let dir : System.FilePath := d
  let (b0, exe) ← try Front.readBundle dir []
    catch e => do IO.eprintln s!"lean-link: {e}"; return 2
  -- `buildSpec` takes a size per function (every region function has a marker); the layout below
  -- replaces them by the compiled code's
  let S ← match Front.buildSpec { b0 with sizes := b0.markers.map fun (n, _) => (n, 0) } with
    | .ok S => pure S
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
  -- the compiler's input: the optimised one under `--opt` (`compileExeOpt S = compileExe S.opt`),
  -- with the Lean compiler's layout (`placedPar = placed`: the totality theorems' layout)
  let SC0 := if opt then S.opt else S
  let SC := if deadCleanup then Link.DeadCleanup.placedPar SC0 else SC0.placedPar
  let names := SC.names
  let R := SC.R
  let file0 ← IO.FS.readBinFile exe
  let summary := s!"{names.length} function(s), {SC.data.length} data object(s), region {hex R}..{hex (R + SC.size)} ({SC.size} bytes)"
  let compile := if deadCleanup then Link.DeadCleanup.compileExe else Link.compileExe
  let link := if deadCleanup then Link.DeadCleanup.leanLink else Link.leanLink
  let thm (s : String) := (if deadCleanup then "Link.DeadCleanup." else "Link.") ++ s
  let exeName := if opt then "compileExeOpt" else "compileExe"
  let theoremName := thm s!"{exeName}_correct"
  let compilerName := thm exeName
  let linkerName := if deadCleanup then "Link.DeadCleanup.leanLink" else "Link.leanLink"
  if opt then
    let fb := Link.optFallbacksWith S.funcs SC0.funcs
    IO.println s!"lean-link: {exe}: --opt: optFallbacks: {fb.length} of {S.funcs.length} function(s) {fb.take 5}"
  -- the source domain (`SrcScopeB` reads the parsed functions only, so `S.input0`'s is the
  -- compiler's input's)
  let I := S.input0
  let srcOk := SrcScopeB I
  if verified && !srcOk then
    let P := I.srcProg
    let bad := P.funcs.filterMap fun g => match srcFails P g with
      | [] => none
      | fs => some (g.name, fs)
    IO.eprintln s!"lean-link: {exe}: --verified: outside the source domain (SrcScopeB): {bad.length} function(s) failing legalOkB/linkFreeB/declSigB {(bad.take 3).map (·.1)}, helperFreeB {helperFreeB P}; not written"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    return 1
  -- the input conditions decided on the CLIF alone (`fnScopeInB`, `addrSlotsInputB`); with
  -- `InScopeP`'s other program conditions, which `compile` checks, `InScopeIn`
  if verified then
    let P := SC.input0.prog
    let syms := fun n => SC.input0.syms.lookup n
    if !addrSlotsInputB P syms then
      IO.eprintln s!"lean-link: {exe}: --verified: outside the input conditions (InScopeIn): addrSlotsInputB fails (an indirect call, a function with an address and stack slots, no program callee with slots); not written"
      return 1
    let bad := P.funcs.filterMap fun g => match fnScopeInFails g with
      | [] => none
      | fs => some (g.name, fs)
    if !bad.isEmpty then
      let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
      IO.eprintln s!"lean-link: {exe}: --verified: outside the input conditions (InScopeIn): {bad.length} function(s) failing fnScopeInB (by cause: {causes}) {(bad.take 3).map (·.1)}; not written"
      for (n, fs) in bad do
        IO.eprintln s!"lean-link:   {n}: {fs}"
      return 1
  -- Keep optimizer and exceptional-edge theorem variants on their retained route
  -- until their production adapters are complete.
  let stockEnabled := !opt && SC0.funcs.any (fun fi => Backend.Stock.Logical.activationEligible fi.func || Backend.Stock.Mixed.activationEligible fi.func || Backend.Stock.Arithmetic.eligible fi.func || Backend.Stock.ScalarAdd.activationEligible fi.func) &&
    !(SC0.funcs.any fun fi => fi.func.blocks.any fun b => b.term.isTry)
  let routes := [Backend.Stock.Logical.lowerValidated,Backend.Stock.Mixed.lowerValidated,
    Backend.Stock.Arithmetic.lowerValidated]
  let compiled := if stockEnabled then SemanticCompilerWith.compileWithRoutes routes SC0 file0 deadCleanup
    else (compile SC file0).map fun file => (⟨file,none⟩ : SemanticCompilerWith.RoutedOutput)
  match compiled with
  | .ok out =>
    let file := out.file
    if out.route.isSome then
      let actualLower := (routes[out.route.getD 0]?).getD Backend.Stock.Arithmetic.lowerValidated
      let SP := SC0.placedProductionWith actualLower deadCleanup
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by Link.SemanticCompilerWith.compileWithRoutes (Link.SemanticCompilerWith.compileWithRoutes_spec, Link.SemanticCompilerWith.attempt_correct)"
      if let some f := ldFile then
        match ← ldCheck SP file0 f with
        | .ok () => IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB); retained legacy acceptance: Link.SemanticCompilerWith.compileWithRoutes_accepts_legacy"
        | .error e => IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {e}"
      let src := if srcOk then
          "; the original (pre-i128-legalisation) program, in SrcScopeB: Link.SemanticCompilerWith.attempt_correct_source, Link.SemanticCompilerWith.attempt_correct_source_peak"
        else "; outside SrcScopeB: about the legalised program only"
      let scope := if verified then "; input in InScopeIn (--verified)" else ""
      IO.println s!"lean-link: {exe}: coverage: Link.SemanticCompilerWith.attempt_correct, Link.SemanticCompilerWith.attempt_correct_depth, Link.SemanticCompilerWith.attempt_correct_peak{src}{scope}"
      return 0
    -- the unwind tables (S10f): with the cleanup compiler, `compileExeU SC file0 = .ok file`
    let unwOk := deadCleanup && Link.DeadCleanup.unwOkB SC file
    IO.FS.writeBinFile exe file
    IO.println s!"lean-link: {exe}: {summary} written by {compilerName} ({theoremName})"
    let src := if srcOk then
        s!"; the original (pre-i128-legalisation) program, in SrcScopeB: {thm s!"{exeName}_correct_source"}, {thm s!"{exeName}_correct_source_peak"}"
      else "; outside SrcScopeB: about the legalised program only"
    let total := if deadCleanup || opt then thm s!"{exeName}_total_reach_input" else "Link.compileExe_total_reach"
    -- `file0` linked by `lean-ld`: its plan against the link spec (`file0OkB_ld`)
    let totalLd := thm s!"{exeName}_total_ld"
    let ldOk ← match ldFile with
      | none => pure false
      | some f => do
        let t0 ← IO.monoMsNow
        match ← ldCheck SC file0 f with
        | .ok () =>
          IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB, {(← IO.monoMsNow) - t0} ms): file0OkB by Link.Ld.file0OkB_ld; totality without checks of the linker's output: {totalLd}"
          pure true
        | .error e =>
          IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {e} (totality only with the checks of file0, {total})"
          pure false
    let totalAll := if ldOk then s!"{total}; on lean-ld's output {totalLd}" else total
    let scope := if verified then s!"; input in InScopeIn (totality: {totalAll}) (--verified)" else ""
    let unw := if unwOk && !opt then
        s!"; exceptional edges: {thm "compileExe_correct_unwind"}, {thm "compileExe_correct_unwind_peak"}"
      else ""
    IO.println s!"lean-link: {exe}: coverage: {thm s!"{exeName}_correct"}, {thm s!"{exeName}_correct_peak"}{src}{scope}{unw}"
    if deadCleanup && !unwOk then
      IO.println s!"lean-link: {exe}: exceptional edges not covered (unwOkB: {Link.DeadCleanup.unwFail SC file})"
    return 0
  | .error e =>
    if e != outOfScopeMsg && e != outOfScopeInMsg then
      IO.eprintln s!"lean-link: {exe}: {e}"
      return 1
    -- outside `compileExe`'s input conditions: the executable is not covered by
    -- `compileExe_correct`; `Link.leanLink` still links it (its checks, the per-crate proof),
    -- except under `--verified`
    let P := SC.input0.prog
    let syms := fun n => SC.input0.syms.lookup n
    let bad := P.funcs.filterMap fun g => match scopeFails P syms g with
      | [] => none
      | fs => some (g.name, fs)
    let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
    let scopeName := if e == outOfScopeInMsg then "InScopeIn" else "InScopeP"
    let fnScope := if e == outOfScopeInMsg then "fnScopeInB" else "fnScopeB"
    let what := if verified then "--verified: not written" else s!"linking with {linkerName} (outside {theoremName} scope)"
    IO.eprintln s!"lean-link: {exe}: outside compileExe's input conditions ({scopeName}): {bad.length} function(s) failing the program-level per-function conditions (by cause: {causes}) {(bad.take 3).map (·.1)}, distinct names {decide (P.funcs.map (·.name)).Nodup}, {if e == outOfScopeInMsg then s!"addrSlotsInputB {addrSlotsInputB P syms}" else s!"addrSlotsInB {addrSlotsInB P syms}"} (else {fnScope}); {what}"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    if verified then return 1
    match link SC file0 with
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
    | .ok file =>
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by {linkerName}"
      IO.println s!"lean-link: {exe}: coverage: none (outside {scopeName}; {linkerName}, no compiler theorem)"
      return 0

import FV.Link.Compile
import FV.Link.DeadCleanupCompile
import FV.E2E.SrcScopeDefs
import FV.Front.Read
import FV.E2E.LinkScopeInputDefs

/-! # `lake exe lean-link DIR SIZES [--dead-cleanup|--no-dead-cleanup] [--verified]`: the
executable compiler on an executable (L1, L2b)

`DIR` is `cargo fv link-proof --cgus … --no-check`'s output for an executable linked by
`cargo fv --lean-link` (docs/research/lean-linker.md): the frontend bundle `bundle.json`
(docs/contracts/frontend.md; read by `Front.readBundle`: per codegen unit the program's
functions in placement order — their CLIF as the frontend wrote it and `lean-regalloc`'s
output — its data objects, local symbols and the merge's names; the executable's symbols and
the functions' Lean code addresses). `SIZES` has one line `NAME WORDS` per function: its size in
the region object (`cargo fv`'s `leanlink.rs`; `Link.leanLink` checks it against the compiled
code, `sizesOkB`). The `Link.LinkSpec` is built in Lean by `Front.buildSpec` (the renaming to
linked names, the data closure, the CLIF image's symbols; `FV/Front/BundleProof.lean`: its
source program is the units' program under the linked names, a scoping, alpha-equivalent to the
units' program under any scoping; the region's base `R`: the first function's address); the
tool then runs the executable
compiler — `Link.DeadCleanup.compileExe` (default, `--dead-cleanup`) or `Link.compileExe`
(`--no-dead-cleanup`): the input conditions `InScopeP`, then the Lean linker (placement, the
compiler's pipeline, the linker's checks, the checks of rust-lld's output — among them that
rust-lld put every function at its placement, `symsOkB`) — and writes the result over the
executable. It prints the theorems covering the written executable (`coverage:`): the
compiler's `compileExe_correct` (entries without a reachable call cycle) and
`compileExe_correct_peak` (any entry), and, for an input in the source domain (`SrcScopeB`),
`compileExe_correct_source` and `compileExe_correct_source_peak` about the original
(pre-`i128`-legalisation) program. No per-crate proof needed.

Outside `InScopeP` the default links with the bare Lean linker (`leanLink`, no compiler
theorem; reported as such). **`--verified`** fails closed: an input outside `SrcScopeB`, outside
the per-function input conditions decided on the CLIF alone (`fnScopeInB`, V7) or outside
`InScopeP` is an error and the executable is not written, so every executable it writes is
covered by the four theorems above and its input is in `InScopeIn` (`InScopeP`'s program-level
conditions with `fnScopeInB`), on which the compiler is proven total
(`compileExe_total_reach_input`, given the layout, reach and `file0` conditions).
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

def main (args : List String) : IO UInt32 := do
  let usage := "usage: lean-link DIR SIZES [--dead-cleanup|--no-dead-cleanup] [--verified]"
  let flags := args.filter (·.startsWith "--")
  if flags.any (fun a => !["--dead-cleanup", "--no-dead-cleanup", "--verified"].contains a) ||
      (flags.contains "--dead-cleanup" && flags.contains "--no-dead-cleanup") then
    IO.eprintln usage; return 2
  let deadCleanup := !flags.contains "--no-dead-cleanup"
  let verified := flags.contains "--verified"
  let [d, sz] := args.filter (!·.startsWith "--") | do IO.eprintln usage; return 2
  let dir : System.FilePath := d
  let mut sizes : Array (String × Nat) := #[]
  for l in (← IO.FS.readFile sz).splitOn "\n" do
    match l.splitOn " " with
    | [n, w] => sizes := sizes.push (n, w.toNat!)
    | _ => pure ()
  let (b, exe) ← try Front.readBundle dir sizes.toList
    catch e => do IO.eprintln s!"lean-link: {e}"; return 2
  let S ← match Front.buildSpec b with
    | .ok S => pure S
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
  let names := S.names
  let R := S.R
  let file0 ← IO.FS.readBinFile exe
  let summary := s!"{names.length} function(s), {S.data.length} data object(s), region {hex R}..{hex (R + S.size)} ({S.size} bytes)"
  let compile := if deadCleanup then Link.DeadCleanup.compileExe else Link.compileExe
  let link := if deadCleanup then Link.DeadCleanup.leanLink else Link.leanLink
  let theoremName := if deadCleanup then "Link.DeadCleanup.compileExe_correct" else "Link.compileExe_correct"
  let compilerName := if deadCleanup then "Link.DeadCleanup.compileExe" else "Link.compileExe"
  let linkerName := if deadCleanup then "Link.DeadCleanup.leanLink" else "Link.leanLink"
  let thm (s : String) := (if deadCleanup then "Link.DeadCleanup." else "Link.") ++ s
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
  -- the input conditions decided on the CLIF alone (`fnScopeInB`); with `InScopeP`'s program
  -- conditions, which `compile` checks, `InScopeIn`
  if verified then
    let P := I.prog
    let bad := P.funcs.filterMap fun g => match fnScopeInFails g with
      | [] => none
      | fs => some (g.name, fs)
    if !bad.isEmpty then
      let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
      IO.eprintln s!"lean-link: {exe}: --verified: outside the input conditions (InScopeIn): {bad.length} function(s) failing fnScopeInB (by cause: {causes}) {(bad.take 3).map (·.1)}; not written"
      for (n, fs) in bad do
        IO.eprintln s!"lean-link:   {n}: {fs}"
      return 1
  match compile S file0 with
  | .ok file =>
    IO.FS.writeBinFile exe file
    IO.println s!"lean-link: {exe}: {summary} written by {compilerName} ({theoremName})"
    let src := if srcOk then
        s!"; the original (pre-i128-legalisation) program, in SrcScopeB: {thm "compileExe_correct_source"}, {thm "compileExe_correct_source_peak"}"
      else "; outside SrcScopeB: about the legalised program only"
    let scope := if verified then s!"; input in InScopeIn (totality: {thm "compileExe_total_reach_input"}) (--verified)" else ""
    IO.println s!"lean-link: {exe}: coverage: {thm "compileExe_correct"}, {thm "compileExe_correct_peak"}{src}{scope}"
    return 0
  | .error e =>
    if e != outOfScopeMsg then
      IO.eprintln s!"lean-link: {exe}: {e}"
      return 1
    -- outside `compileExe`'s input conditions: the executable is not covered by
    -- `compileExe_correct`; `Link.leanLink` still links it (its checks, the per-crate proof),
    -- except under `--verified`
    let P := I.prog
    let syms := fun n => I.syms.lookup n
    let bad := P.funcs.filterMap fun g => match scopeFails P syms g with
      | [] => none
      | fs => some (g.name, fs)
    let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
    let what := if verified then "--verified: not written" else s!"linking with {linkerName} (outside {theoremName} scope)"
    IO.eprintln s!"lean-link: {exe}: outside compileExe's input conditions (InScopeP): {bad.length} function(s) failing the program-level per-function conditions (by cause: {causes}) {(bad.take 3).map (·.1)}, distinct names {decide (P.funcs.map (·.name)).Nodup}, addrSlotsInB {addrSlotsInB P syms} (else fnScopeB); {what}"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    if verified then return 1
    match link S file0 with
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
    | .ok file =>
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by {linkerName}"
      IO.println s!"lean-link: {exe}: coverage: none (outside InScopeP; {linkerName}, no compiler theorem)"
      return 0
